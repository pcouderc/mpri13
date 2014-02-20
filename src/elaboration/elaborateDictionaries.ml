open String

open Name
open XAST
open Types
open Positions
open ElaborationErrors
open ElaborationExceptions
open ElaborationEnvironment

exception Found

let string_of_type ty = ASTio.(XAST.(to_string pprint_ml_type ty))
let string_of_expr e = ASTio.(XAST.(to_string pprint_expression e))

let string_of_instance ins =
  match ins.instance_index, ins.instance_class_name with
  | TName index, TName cn -> Format.sprintf "%s, %s;" index cn

let rec program p = handle_error List.(fun () ->
  flatten (fst (Misc.list_foldmap block ElaborationEnvironment.initial p))
)

and block env = function
  | BTypeDefinitions ts ->
    let env = type_definitions env ts in
    ([BTypeDefinitions ts], env)

  | BDefinition d ->
    let d, env = value_binding env d in
    ([BDefinition d], env)

  | BClassDefinition c ->
    let defs, env = class_definition env c in
    (defs, env)

  | BInstanceDefinitions is ->
    let d, env = instance_definitions env is in
    ([BDefinition d], env)

(* Type definitions *)


and type_definitions env (TypeDefs (_, tdefs)) =
  let env = List.fold_left env_of_type_definition env tdefs in
  List.fold_left type_definition env tdefs

and env_of_type_definition env = function
  | (TypeDef (pos, kind, t, _)) as tdef ->
    bind_type t kind tdef env

  | (ExternalType (p, ts, t, os)) as tdef ->
    bind_type t (kind_of_arity (List.length ts)) tdef env

and type_definition env = function
  | TypeDef (pos, _, t, dt) -> datatype_definition t env dt
  | ExternalType (p, ts, t, os) -> env

and datatype_definition t env = function
  | DAlgebraic ds ->
    List.fold_left algebraic_dataconstructor env ds
  | DRecordType (ts, ltys) ->
    List.fold_left (label_type ts t) env ltys

and label_type ts rtcon env (pos, l, ty) =
  let env' = List.fold_left (fun env x -> bind_type_variable x env) env ts in
  check_wf_type env' KStar ty;
  bind_label pos l ts ty rtcon env

and algebraic_dataconstructor env (_, DName k, ts, kty) =
  check_wf_scheme env ts kty;
  bind_scheme (Name k) ts kty env

and introduce_type_parameters env ts =
  List.fold_left (fun env t -> bind_type_variable t env) env ts

and check_wf_scheme env ts ty =
  check_wf_type (introduce_type_parameters env ts) KStar ty

and check_wf_type env xkind = function
  | TyVar (pos, t) ->
    let tkind = lookup_type_kind pos t env in
    check_equivalent_kind pos xkind tkind

  | TyApp (pos, t, tys) ->
    let kt = lookup_type_kind pos t env in
    check_type_constructor_application pos env kt tys

and check_type_constructor_application pos env k tys =
  match tys, k with
  | [], KStar -> ()
  | ty :: tys, KArrow (k, ks) ->
    check_wf_type env k ty;
    check_type_constructor_application pos env ks tys
  | _ ->
    raise (IllKindedType pos)

and check_equivalent_kind pos k1 k2 =
  match k1, k2 with
    | KStar, KStar -> ()
    | KArrow (k1, k2), KArrow (k1', k2') ->
      check_equivalent_kind pos k1 k1';
      check_equivalent_kind pos k2 k2'
    | _ ->
      raise (IncompatibleKinds (pos, k1, k2))

and env_of_bindings env cdefs = List.(
  (function
    | BindValue (_, vs)
    | BindRecValue (_, vs) ->
      fold_left (fun env (ValueDef (_, ts, _, (x, ty), _)) ->
        bind_scheme x ts ty env
      ) env vs
    | ExternalValue (_, ts, (x, ty), _) ->
      bind_scheme x ts ty env
  ) cdefs
)

and check_equal_types pos ty1 ty2 =
  if not (equivalent ty1 ty2) then
    raise (IncompatibleTypes (pos, ty1, ty2))

and type_application pos env x tys =
  List.iter (check_wf_type env KStar) tys;
  let (ts, (_, ty)) = lookup pos x env in
  try
    substitute (List.combine ts tys) ty
  with _ ->
    raise (InvalidTypeApplication pos)

and is_overloaded pos env ty =
  match ty with
  | TyApp (_, tname, [ty]) ->
    begin
      try Some (lookup_class_type pos tname env, ty)
      with Not_found -> None
    end
  | _ -> None

and class_repr pos env ps = function
  | Some (n, TyVar (_,_)) ->
    let TName cl = n in
    ignore (lookup_class pos (TName cl) env);
    generate_superclass_access pos env ps (TName cl)

  | Some (n, ((TyApp (_, TName _, [])) as t)) ->
    let TName cl = n in
    ignore (lookup_instance pos (TName cl) (TName (repr_of_type t)) env);
    let c = repr_of_type t ^ cl in
    EVar (pos, Name c, [t])

  | Some (n, ((TyApp (_, TName _, ts)) as t)) ->
    let TName cl = n in
    let def = (lookup_instance pos (TName cl) (TName (repr_of_type t)) env) in
    let c = repr_of_type t ^ cl in
    if def.instance_typing_context  <> [] then
      let hd = class_repr pos env ps (Some (n, List.hd ts)) in
      let ts = List.tl ts in
      EApp(pos, EVar (pos, Name c, [t]),
           List.fold_left (fun acc ty ->
               let ty = Some (n, ty) in
               EApp (pos, class_repr pos env ps ty, acc)) hd ts)
    else
      EVar (pos, Name c, [t])

  (* The repr always take the result of is_overloaded in case it is Some _ *)
  | None -> assert false

(* Debug function *)
and string_of_type2 = function
  | TyVar (_, TName n) -> n
  | TyApp (_, TName n, ts) ->
    Format.sprintf "%s(%s)" n
      (List.fold_left (fun acc t -> acc ^ ", " ^ (string_of_type2 t)) "" ts)

and expression env (ps : class_predicates) = function

  | EVar (pos, ((Name s) as x), tys) ->
    (* Rule OApp *)
    let tys' = type_application pos env x tys in
    begin
      (* We look if it's an value or an abstraction *)
      match destruct_tyarrow tys' with
      | None -> (EVar (pos, x, tys), tys')
      | Some (ity, oty) -> begin
          (* If it's a type that asks for an overloaded record as
            first argument *)
        match is_overloaded pos env ity with
        | None -> (EVar (pos, x, tys), tys')
        | Some (cl, ty) ->
          let c = class_repr pos env ps (Some (cl, ty)) in
          (EApp (pos, (EVar (pos, x, tys)), c), oty)
        end
    end

  | ELambda (pos, ((x, aty) as b), e') ->
    check_wf_type env KStar aty;
    let env = bind_simple x aty env in
    let (e, ty) = expression env ps e' in
    (ELambda (pos, b, e), ntyarrow pos [aty] ty)

  | EApp (pos, a, b) ->
    let a, a_ty = expression env ps a in
    let b, b_ty = expression env ps b in
    begin match destruct_tyarrow a_ty with
      | None ->
        raise (ApplicationToNonFunctional pos)
      | Some (ity, oty) ->
        check_equal_types pos b_ty ity;
        (EApp (pos, a, b), oty)
    end

  | EBinding (pos, vb, e) ->
    let vb, env = value_binding env vb in
    let e, ty = expression env ps e in
    (EBinding (pos, vb, e), ty)

  | EForall (pos, tvs, e) ->
    (** Because type abstractions are removed by [value_binding]. *)
    raise (OnlyLetsCanIntroduceTypeAbstraction pos)

  | ETypeConstraint (pos, e, xty) ->
    let e, ty = expression env ps e in
    check_equal_types pos ty xty;
    (e, ty)

  | EExists (_, _, e) ->
    (** Because we are explicitly typed, flexible type variables
        are useless. *)
    expression env ps e

  | EDCon (pos, DName x, tys, es) ->
    let ty = type_application pos env (Name x) tys in
    let (itys, oty) = destruct_ntyarrow ty in
    if List.(length itys <> length es) then
      raise (InvalidDataConstructorApplication pos)
    else
      let es =
        List.map2 (fun e xty ->
          let (e, ty) = expression env ps e in
          check_equal_types pos ty xty;
          e
        ) es itys
      in
      (EDCon (pos, DName x, tys, es), oty)

  | EMatch (pos, s, bs) ->
    let (s, sty) = expression env ps s in
    let bstys = List.map (branch env ps sty) bs in
    let bs = fst (List.split bstys) in
    let tys = snd (List.split bstys) in
    let ty = List.hd tys in
    List.iter (check_equal_types pos ty) (List.tl tys);
    (EMatch (pos, s, bs), ty)

  | ERecordAccess (pos, e, l) ->
    let e, ty = expression env ps e in
    let (ts, lty, rtcon) = lookup_label pos l env in
    let ty =
      match ty with
        | TyApp (_, r, args) ->
          if rtcon <> r then
            raise (LabelDoesNotBelong (pos, l, r, rtcon))
          else
            begin try
              let s = List.combine ts args in
              Types.substitute s lty
            with _ ->
              (** Because we only well-kinded types and only store
                  well-kinded types in the environment. *)
              assert false
            end
        | _ ->
          raise (RecordExpected (pos, ty))
    in
    (ERecordAccess (pos, e, l), ty)

  | ERecordCon (pos, n, i, []) ->
    (** We syntactically forbids empty records. *)
    assert false

  | ERecordCon (pos, n, i, rbs) ->
    let rbstys = List.map (record_binding env ps) rbs in
    let rec check others rty = function
      | [] ->
        List.rev others, rty
      | (RecordBinding (l, e), ty) :: ls ->
        if List.exists (fun (RecordBinding (l', _)) -> l = l') others then
          raise (MultipleLabels (pos, l));

        let (ts, lty, rtcon) = lookup_label pos l env in
        let (s, rty) =
          match rty with
            | None ->
              let rty = TyApp (pos, rtcon, i) in
              let s =
                try
                  List.combine ts i
                with _ -> raise (InvalidRecordInstantiation pos)
              in
              (s, rty)
            | Some (s, rty) ->
              (s, rty)
        in
        check_equal_types pos ty (Types.substitute s lty);
        check (RecordBinding (l, e) :: others) (Some (s, rty)) ls
    in
    let (ls, rty) = check [] None rbstys in
    let rty = match rty with
      | None -> assert false
      | Some (_, rty) -> rty
    in
    (ERecordCon (pos, n, i, ls), rty)

  | ((EPrimitive (pos, p)) as e) ->
    (e, primitive pos p)

and primitive pos = function
  | PIntegerConstant _ ->
    TyApp (pos, TName "int", [])

  | PUnit ->
    TyApp (pos, TName "unit", [])

  | PCharConstant _ ->
    TyApp (pos, TName "char", [])

and branch env ps sty (Branch (pos, p, e)) =
  let denv = pattern env sty p in
  let env = concat pos env denv in
  let (e, ty) = expression env ps e in
  (Branch (pos, p, e), ty)

and concat pos env1 env2 =
  List.fold_left
    (fun env (_, (x, ty)) -> bind_simple x ty env)
    env1 (values env2)

and linear_bind pos env (ts, (x, ty)) =
  assert (ts = []); (** Because patterns only bind monomorphic values. *)
  try
    ignore (lookup pos x env);
    raise (NonLinearPattern pos)
  with UnboundIdentifier _ ->
    bind_simple x ty env

and join pos denv1 denv2 =
  List.fold_left (linear_bind pos) denv2 (values denv1)

and check_same_denv pos denv1 denv2 =
  List.iter (fun (ts, (x, ty)) ->
    assert (ts = []); (** Because patterns only bind monomorphic values. *)
    try
      let (_, (_, ty')) = lookup pos x denv2 in
      check_equal_types pos ty ty'
    with _ ->
      raise (PatternsMustBindSameVariables pos)
  ) (values denv1)

and pattern env xty = function
  | PVar (_, name) ->
    bind_simple name xty ElaborationEnvironment.empty

  | PWildcard _ ->
    ElaborationEnvironment.empty

  | PAlias (pos, name, p) ->
    linear_bind pos (pattern env xty p) ([], (name, xty))

  | PTypeConstraint (pos, p, pty) ->
    check_equal_types pos pty xty;
    pattern env xty p

  | PPrimitive (pos, p) ->
    check_equal_types pos (primitive pos p) xty;
    ElaborationEnvironment.empty

  | PData (pos, (DName x), tys, ps) ->
    let kty = type_application pos env (Name x) tys in
    let itys, oty = destruct_ntyarrow kty in
    if List.(length itys <> length ps) then
      raise (InvalidDataConstructorApplication pos)
    else
      let denvs = List.map2 (pattern env) itys ps in (
        check_equal_types pos oty xty;
        List.fold_left (join pos) ElaborationEnvironment.empty denvs
      )

  | PAnd (pos, ps) ->
    List.fold_left
      (join pos)
      ElaborationEnvironment.empty
      (List.map (pattern env xty) ps)

  | POr (pos, ps) ->
    let denvs = List.map (pattern env xty) ps in
    let denv = List.hd denvs in
    List.(iter (check_same_denv pos denv) (tl denvs));
    denv

and record_binding env ps (RecordBinding (l, e)) =
  let e, ty = expression env ps e in
  (RecordBinding (l, e), ty)

and value_binding env = function
  | BindValue (pos, vs) ->
    let (vs, env) = Misc.list_foldmap value_definition env vs in
    (BindValue (pos, vs), env)

  | BindRecValue (pos, vs) ->
    let env = List.fold_left value_declaration env vs in
    let (vs, _) = Misc.list_foldmap value_definition env vs in
    (BindRecValue (pos, vs), env)

  | ExternalValue (pos, ts, ((x, ty) as b), os) ->
    let env = bind_scheme x ts ty env in
    (ExternalValue (pos, ts, b, os), env)

and eforall pos ts e =
  match ts, e with
    | ts, EForall (pos, [], ((EForall _) as e)) ->
      eforall pos ts e
    | [], EForall (pos, [], e) ->
      e
    | [], EForall (pos, _, _) ->
      raise (InvalidNumberOfTypeAbstraction pos)
    | [], e ->
      e
    | x :: xs, EForall (pos, t :: ts, e) ->
      if x <> t then
        raise (SameNameInTypeAbstractionAndScheme pos);
      eforall pos xs (EForall (pos, ts, e))
    | _, _ ->
      raise (InvalidNumberOfTypeAbstraction pos)


and value_definition env (ValueDef (pos, ts, ps, (x, xty), e)) =
  let env' = introduce_type_parameters env ts in
  check_wf_scheme env ts xty;
  let Name n = x in
  check_value_name pos env n;
  is_canonical pos env ps;

  (* Let restriction, with values that cannot use a typing context *)
  begin
    match is_overloaded pos env xty with
    | Some _ -> () (* Since we transform instances into dictionnaries, it is
                     transformed into a value with a typing context, which is
                     transformed then by expression. This shouldn't raise an
                     exception and is correct. *)
    | None ->
      (match destruct_tyarrow xty with
      | None -> if ps <> [] then raise (InvalidOverloading pos)
      | Some _ -> ())
  end;

  if is_value_form e then begin
    let e = eforall pos ts e in

    (* Rule OAbs *)
    let e = List.fold_right (extend_expr_with_abstraction pos env) ps e in
    let e, ty = expression env' ps e in

    (* We extend xty with the introduced dictionary arguments *)
    let xty = extend_type_with_predicates pos env xty ps in
    let b = (x, ty) in
    check_equal_types pos xty ty;
    (ValueDef (pos, ts, [], b, EForall (pos, ts, e)),
     bind_scheme x ts ty env)
  end else begin
    if ts <> [] || ps <> [] then
      raise (ValueRestriction pos)
    else
      let e = eforall pos [] e in
      let e, ty = expression env' ps e in
      let b = (x, ty) in
      check_equal_types pos xty ty;
      (ValueDef (pos, [], [], b, e), bind_simple x ty env)
  end

and value_declaration env (ValueDef (pos, ts, ps, (x, ty), e)) =
  let ty = extend_type_with_predicates pos env ty ps in
  is_canonical pos env ps;
  bind_scheme x ts ty env


and is_value_form = function
  | EVar _
  | ELambda _
  | EPrimitive _ ->
    true
  | EDCon (_, _, _, es) ->
    List.for_all is_value_form es
  | ERecordCon (_, _, _, rbs) ->
    List.for_all (fun (RecordBinding (_, e)) -> is_value_form e) rbs
  | EExists (_, _, t)
  | ETypeConstraint (_, t, _)
  | EForall (_, _, t) ->
    is_value_form t
  | _ ->
    false

(* Checks that the value actually declarated doesn't replace an already
  existing overloaded function *)
and check_value_name pos env name =
  try
    ignore (lookup_member pos (TName name) env);
    raise (InvalidOverloading pos)
  with Not_found -> ()

(* Class definition *)

and class_definition env c =
  let sclasses =
    lookup_classes_definition c.class_position c.superclasses env in
  check_superclasses env c;
  check_members env sclasses c.class_parameter c.class_members;
  let env = bind_class c.class_name c env in
  let def, env = elaborate_class env c in
  let env = List.fold_left (fun env (pos, LName n, _) ->
      bind_member pos (TName n) c.class_name env) env c.class_members in
  def, env

and check_superclasses env c =
  let pos = c.class_position in
  let rec iter = function
    | [] -> ()
    | cl :: t ->
      unrelated_classes pos env t cl;
      check_class_param pos env cl c.class_parameter;
      iter t
  in
  iter c.superclasses

(* Checks that classes aren't in the same context *)
and unrelated_classes pos env classes c =
  List.iter (fun ((TName n2) as tname) ->
      if is_superclass pos tname c env || c = tname then
        raise (RelatedClasses (pos, c, tname)))
    classes

(* Checks that the parameter of the superclass doesn't differ from its own
  parameter. Already checked at parsing though *)
and check_class_param pos env cl_name param =
  let sc_param = (lookup_class pos cl_name env).class_parameter in
  if not (sc_param = param) then
    raise (SuperclassParameterDifferent (pos, sc_param, param))

and check_members env sclasses param = function
  | [] -> ()
  | (pos, (LName n), ty) :: l ->
    check_wf_scheme env [param] ty;
    try
      ignore (lookup pos (Name n) env);
      raise (InvalidOverloading pos)
    with UnboundIdentifier (_, _) -> ();
    check_members env sclasses param l

(* Verifies that a superclass doesn't already defines a member with this
  specific name
   Should be removed!
*)
and check_superclasses_members env sclasses (pos, n, _) =
  let already_defined sclass =
    List.iter (fun (_, sc_f, _) -> if sc_f = n then
          raise (FunctionDefinedInSClass (pos, sclass.class_name, sc_f)))
      sclass.class_members
  in
  List.iter already_defined sclasses

(* Class elaboration *)

and elaborate_class env c =
  let class_record, env = create_class_record env c in
  let members, env = create_members env c in
  class_record :: members, env

(* Generate the record type for the typeclass c *)
and create_class_record env c =
  let pos = c.class_position in
  let TName n = c.class_name in
  let record = "class" ^ n in

  (* In case the type class<class_name> is already taken *)
  let rec gen_record_name inc =
    try ignore (lookup_type_definition
                  pos (TName (record ^ (string_of_int inc))) env);
      gen_record_name (inc+1)
    with UnboundTypeVariable (_, _) -> record ^ (string_of_int inc) in

  let record_name =
    try ignore (lookup_type_definition pos (TName record) env);
      TName (gen_record_name 0)
    with UnboundTypeVariable _ -> TName record in

  (* Adds the typename of the record into the environment, to be able to know
    later if it corresponds to an overloaded record *)
  let env = bind_class_type pos record_name c.class_name env in

  (* Extends the record fields with the superclasses access' one *)
  let fields = List.fold_left (fun acc (TName sc) ->
      let sc_field = class_typename pos (TName sc) env in
      let ty = TyApp
          (pos, sc_field, [TyVar (pos, c.class_parameter)]) in
    (pos, LName ("sc" ^ n ^ sc), ty) :: acc) c.class_members c.superclasses in

  (* Returns the type definition and checks the elaborated record as a normal
    type *)
  let record = TypeDefs (pos,
                         [TypeDef (pos, kind_of_arity 1, record_name,
                                   DRecordType ([c.class_parameter], fields))]) in
  BTypeDefinitions record, type_definitions env record

(* Generates each overloaded class member's function *)
and create_members env c =
  List.fold_left (fun (acc, env) m ->
      let m, env = create_member env c m in
      m :: acc, env) ([], env) c.class_members

(* Generates the overloaded function, with its record abstraction *)
and create_member env c (pos, lname, ty) =
  let LName n = lname in
  let TName cl = c.class_name in
  let class_pred = ClassPredicate (TName cl, c.class_parameter) in
  let ty = extend_type_with_predicates pos env ty [class_pred] in
  let rec_access =
    ERecordAccess (pos, EVar (pos, Name ("dict" ^ cl), []), lname) in

  (* We introduce the class_param to be able to use the dictionnary *)
  let expr = extend_expr_with_predicate pos env class_pred rec_access in
  let v =
    BindValue (pos,
               [ValueDef (pos, [c.class_parameter], [], (Name n, ty), expr)]) in
  let v, env = value_binding env v in
  BDefinition v, env

(* Extends an expression with class predicates, i.e. adding the types and
  records abstractions *)
and extend_expr_with_predicates pos env ps expr =
  List.fold_right (extend_expr_with_predicate pos env) ps expr

(* Adds the type abstraction and record abstraction for the class predicate *)
and extend_expr_with_predicate pos env cp expr =
  let (ClassPredicate (TName cl, param)) = cp in
  EForall (pos, [param], extend_expr_with_abstraction pos env cp expr)

(* Adds the record abstraction for a class predicate given *)
and extend_expr_with_abstraction pos env cp expr =
  let (ClassPredicate (TName cl, param)) = cp in
  ELambda (pos,
           (Name ("dict" ^ cl), class_type pos cp env),
           expr)

(* Returns the type for the class predicate given *)
and class_type pos (ClassPredicate (cl, param)) env =
  let cl_name = class_typename pos cl env in
  TyApp (pos, cl_name, [TyVar (pos, param)])

(* Extends the type given with the type of abstractions elaborated from class
  predicates *)
and extend_type_with_predicates pos env ty predicates =
  let types = List.fold_right (fun cp acc ->
      class_type pos cp env :: acc) predicates [] in
  ntyarrow pos types ty

(* Retrieves the type of the record of the class given *)
and class_typename = get_type_of_class

(* Instances definitions *)

and instance_definitions env instances =
  (* Extends the env to allow mutually recursives instances *)
  let env = List.fold_left (fun env ins ->
      bind_instance ins env) env instances in
  let pos = (List.hd instances).instance_position in

  let rec step acc env = function
  | [] -> acc, env
  | ins :: t -> let env = instance_definition env ins in
    let v, env = instance_elaboration env ins in
    step (v :: acc) env t
  in
  let values, env = step [] env instances in
  value_binding env (BindRecValue (pos, values))


and instance_definition env instance =
  check_superclasses_instances env instance;
  check_instance_members env instance;
  is_canonical instance.instance_position env instance.instance_typing_context;
  env

(* Checks that there already exists an instance for each instance superclasses *)
and check_superclasses_instances env instance =
  let pos = instance.instance_position in
  let sclasses = lookup_superclasses pos instance.instance_class_name env in
  let index = instance.instance_index in
  List.iter (fun cl ->
      try ignore (lookup_instance pos cl index env)
      with e -> raise e) sclasses

(* Checks there aren't two equal instance predicates that binds the same type *)
and is_canonical pos env cps =
  let rec step = function
    | [] -> ()
    | cp :: tl ->
      if List.mem cp tl then raise (InvalidOverloading pos) else step tl
  in
  step cps

(* Verifies that the instance members is compatible with the class definition *)
and check_instance_members env ins =
  let pos = ins.instance_position in
  let class_ = lookup_class pos ins.instance_class_name env in
  let class_members = class_.class_members in

  let xenv = extended_env env ins class_ in
  List.iter2 (fun (pos, lname, mltype) (RecordBinding (LName n, expr)) ->
      let _, ty = expression xenv ins.instance_typing_context expr in
      let r_type = reconstruct_type ins in
      check_reconstructed_type_arity xenv r_type;
      let mltype = substitute [class_.class_parameter, r_type] mltype in
      if not @@ equivalent mltype ty then
        raise (IncompatibleTypes (pos, ty, mltype))
    ) class_members ins.instance_members

(* Extends the actual env by binding to the class parameter the type of the
  instantiated instance *)
and extended_env env ins class_ =
  let class_members = class_.class_members in
  let env = List.fold_left
      (fun env tname -> bind_type_variable tname env)
      env ins.instance_parameters in
  List.fold_left
    (fun env (pos, (LName name), mltype) ->
       bind_scheme (Name name) [class_.class_parameter] mltype env) env class_members

(* Recreates the type of the instance *)
and reconstruct_type ins =
  let pos = ins.instance_position in
  let type_parameters =
    List.map (fun tname -> TyVar (pos, tname)) ins.instance_parameters in
  TyApp (ins.instance_position, ins.instance_index, type_parameters)

(* Verifies the recreated type arity matches specification *)
and check_reconstructed_type_arity env = function
  | (TyApp (pos, tname, params)) ->
    let kind = lookup_type_kind pos tname env in
    if kind_of_arity (List.length params) <> kind then
      raise (InvalidTypeApplication pos)
  | _ -> assert false


(* Instance elaboration *)

and instance_elaboration env ins =
  let pos = ins.instance_position in
  let ty = reconstruct_type ins in
  let name = Name (instance_name_raw ins ty) in
  let record = ERecordCon (pos, name, [ty],
                           (extend_record_binding pos env ins ty)) in

  (* We cannot just let the elaboration of expressions to do it using the class
    predicates, since we restrict the values to not have class predicates *)
  let expr = extend_expr_with_abs pos ins.instance_parameters record in
  let value = ValueDef (pos, ins.instance_parameters,
                        ins.instance_typing_context,
                        (name, instance_base_type pos ins env), expr) in
  value, env

(* Unused function *)
and create_record_type pos env ins =
  extend_type_with_predicates pos env
    (instance_base_type pos ins env)
    ins.instance_typing_context

(* Adds the fields for the superclasses *)
and extend_record_binding pos env ins ty =
  let instantiation =
    List.map (fun tn -> TyVar (pos, tn)) ins.instance_parameters in
  let TName n = ins.instance_class_name in
  List.fold_left (fun bindings (TName sc) ->
      let sc_ins = repr_of_type ty ^ sc in
      let expr = EVar (pos, Name sc_ins, instantiation) in
      RecordBinding (LName ("sc" ^ n ^ sc), expr) :: bindings)
    ins.instance_members (lookup_superclasses pos ins.instance_class_name env)

(* Creates the records accesses from a class to a specific superclass, if there is *)
and generate_superclass_access pos env ps (TName n) =
  let sc = TName n in
  let path = List.fold_left (fun acc (ClassPredicate (cl, ty)) ->
      if (cl = sc) then Some ([], cl, ty) else
      match acc with
      | Some (_, _, _) -> acc
      | None -> match find_path pos cl sc env with
        | None -> None
        | Some l -> Some (l, cl, ty)) None ps in
  match path with
  | None -> Format.printf "No access to the superclass %s@." n;
              raise (InvalidOverloading pos)
  | Some (l, cl, ty) ->
    let TName orig = cl in
    List.fold_left (fun expr (TName n) ->
      ERecordAccess (pos, expr, LName ("sc" ^ orig ^ n)))
      (EVar (pos, Name ("dict" ^ orig), [TyVar (pos, ty)])) l

(* Extends an expression with types abstraction *)
and extend_expr_with_abs pos ts expr =
  List.fold_right (extend_expr_with_unique_abs pos) ts expr

and extend_expr_with_unique_abs pos t expr =
  EForall (pos, [t], expr)

(* Returns the record type of an instance *)
and instance_base_type pos ins env =
  let cl = ins.instance_class_name in
  let ty = reconstruct_type ins in
  TyApp (pos, class_typename pos cl env, [ty])


and repr_of_type = function
    | TyVar (_, TName n) ->
      if String.contains n '\'' then "" else n
    | TyApp (_, TName n, tl) ->
      List.fold_left (fun acc t -> repr_of_type t ^ acc) n tl

and instance_name ins =
  let ty = reconstruct_type ins in
  TName (instance_name_raw ins ty)

and instance_name_raw ins ty =
  let TName cl = ins.instance_class_name in
  repr_of_type ty ^ cl
