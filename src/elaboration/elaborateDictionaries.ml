open String

open Name
open XAST
open Types
open Positions
open ElaborationErrors
open ElaborationExceptions
open ElaborationEnvironment

let string_of_type ty      = ASTio.(XAST.(to_string pprint_ml_type ty))

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
    (* List.iter (fun ins -> Format.printf "%s;" @@ string_of_instance ins) is; *)
    let env = instance_definitions env is in
    ([], env)

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

and expression env = function
  | EVar (pos, ((Name s) as x), tys) ->
    (EVar (pos, x, tys), type_application pos env x tys)

  | ELambda (pos, ((x, aty) as b), e') ->
    check_wf_type env KStar aty;
    let env = bind_simple x aty env in
    let (e, ty) = expression env e' in
    (ELambda (pos, b, e), ntyarrow pos [aty] ty)

  | EApp (pos, a, b) ->
    let a, a_ty = expression env a in
    let b, b_ty = expression env b in
    begin match destruct_tyarrow a_ty with
      | None ->
        raise (ApplicationToNonFunctional pos)
      | Some (ity, oty) ->
        check_equal_types pos b_ty ity;
        (EApp (pos, a, b), oty)
    end

  | EBinding (pos, vb, e) ->
    let vb, env = value_binding env vb in
    let e, ty = expression env e in
    (EBinding (pos, vb, e), ty)

  | EForall (pos, tvs, e) ->
    (** Because type abstractions are removed by [value_binding]. *)
    raise (OnlyLetsCanIntroduceTypeAbstraction pos)

  | ETypeConstraint (pos, e, xty) ->
    let e, ty = expression env e in
    check_equal_types pos ty xty;
    (e, ty)

  | EExists (_, _, e) ->
    (** Because we are explicitly typed, flexible type variables
        are useless. *)
    expression env e

  | EDCon (pos, DName x, tys, es) ->
    let ty = type_application pos env (Name x) tys in
    let (itys, oty) = destruct_ntyarrow ty in
    if List.(length itys <> length es) then
      raise (InvalidDataConstructorApplication pos)
    else
      let es =
        List.map2 (fun e xty ->
          let (e, ty) = expression env e in
          check_equal_types pos ty xty;
          e
        ) es itys
      in
      (EDCon (pos, DName x, tys, es), oty)

  | EMatch (pos, s, bs) ->
    let (s, sty) = expression env s in
    let bstys = List.map (branch env sty) bs in
    let bs = fst (List.split bstys) in
    let tys = snd (List.split bstys) in
    let ty = List.hd tys in
    List.iter (check_equal_types pos ty) (List.tl tys);
    (EMatch (pos, s, bs), ty)

  | ERecordAccess (pos, e, l) ->
    let e, ty = expression env e in
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
    let rbstys = List.map (record_binding env) rbs in
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

and branch env sty (Branch (pos, p, e)) =
  let denv = pattern env sty p in
  let env = concat pos env denv in
  let (e, ty) = expression env e in
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

and record_binding env (RecordBinding (l, e)) =
  let e, ty = expression env e in
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

  if is_value_form e then begin
    let e = eforall pos ts e in
    let e, ty = expression env' e in
    let b = (x, ty) in
    check_equal_types pos xty ty;
    (ValueDef (pos, ts, [], b, EForall (pos, ts, e)),
     bind_scheme x ts ty env)
  end else begin
    if ts <> [] then
      raise (ValueRestriction pos)
    else
      let e = eforall pos [] e in
      let e, ty = expression env' e in
      let b = (x, ty) in
      check_equal_types pos xty ty;
      (ValueDef (pos, [], [], b, e), bind_simple x ty env)
  end

and value_declaration env (ValueDef (pos, ts, ps, (x, ty), e)) =
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

(* Added for expression typing *)

(* and extend_value_def env (ValueDef (pos, ts, ps, b, e)) = *)
(*   List.fold_right  *)

(* Class definition *)

and debug = ref false

and class_definition env c =
  if !debug then begin
    Format.printf "In class_definition@.";
    List.iter (function TName n -> Format.printf "%s; " n) c.superclasses;
    Format.printf "@." end;
  let sclasses =
    lookup_classes_definition c.class_position c.superclasses env in
  check_superclasses env c;
  check_members env sclasses c.class_parameter c.class_members;
  let env = bind_class c.class_name c env in
  elaborate_class env c

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

and unrelated_classes pos env classes c =
  let TName n1 = c in
  List.iter (fun ((TName n2) as tname) ->
      if !debug then Format.printf "Testing %s with %s@." n1 n2;
      if is_superclass pos tname c env || c = tname then
        raise (RelatedClasses (pos, c, tname))
    )
    classes

and check_class_param pos env cl_name param =
  let sc_param = (lookup_class pos cl_name env).class_parameter in
  if not (sc_param = param) then
    raise (SuperclassParameterDifferent (pos, sc_param, param))

and check_members env sclasses param = function
  | [] -> ()
  | (pos, n, ty) as func :: l ->
    check_wf_scheme env [param] ty;
    check_superclasses_members env sclasses func;
    check_members env sclasses param l

and check_superclasses_members env sclasses (pos, n, _) =
  let already_defined sclass =
    List.iter (fun (_, sc_f, _) -> if sc_f = n then
          raise (FunctionDefinedInSClass (pos, sclass.class_name, sc_f)))
      sclass.class_members
  in
  List.iter already_defined sclasses

(* Class elaboration *)

and elaborate_class env c =
  (* What we need:
     - Create a record type for the class
     - Create a value for each class member
  *)
  let class_record, env = create_class_record env c in
  let members, env = create_members env c in
  class_record :: members, env

and create_class_record env c =
  let pos = c.class_position in
  let record_name = match c.class_name with
    TName n -> TName ("class" ^ n)
  in
  let fields = List.fold_left (fun acc (TName sc) ->
      let sc_field = class_typename sc in
      let ty = TyApp
          (pos, sc_field, [TyVar (pos, c.class_parameter)]) in
    (pos, LName ("sc" ^ sc), ty) :: acc) c.class_members c.superclasses in
  let record = TypeDefs (pos,
                         [TypeDef (pos, kind_of_arity 1, record_name,
                                   DRecordType ([c.class_parameter], fields))]) in
  BTypeDefinitions record, type_definitions env record

and create_members env c =
  List.fold_left (fun (acc, env) m ->
      let m, env = create_member env c m in
      m :: acc, env) ([], env) c.class_members

and create_member env c (pos, lname, ty) =
  let LName n = lname in
  let TName cl = c.class_name in
  let class_pred = ClassPredicate (TName cl, c.class_parameter) in
  let ty = extend_type_with_predicates pos ty [class_pred] in
  let rec_access =
    ERecordAccess (pos, EVar (pos, Name ("dict" ^ cl), []), lname) in

  (* We introduce the class_param to be able to use the dictionnary *)
  let expr = EForall (pos, [c.class_parameter],
                      ELambda (pos,
                               (Name ("dict" ^ cl), class_type pos class_pred),
                               rec_access)) in
  let v =
    BindValue (pos,
               [ValueDef (pos, [c.class_parameter], [], (Name n, ty), expr)]) in
  let v, env = value_binding env v in
  BDefinition v, env

and class_type pos (ClassPredicate (TName cl, param)) =
  let cl_name = class_typename cl in
  TyApp (pos, cl_name, [TyVar (pos, param)])

and extend_type_with_predicates pos ty predicates =
  let types = List.fold_right (fun cp acc ->
      (* let cl_name = class_typename cl in *)
      (* let cl_type = TyApp (pos, cl_name, [TyVar (pos, param)]) in *)
      class_type pos cp :: acc) predicates [] in
  ntyarrow pos types ty

and class_typename cl =
  (* let TName n = c.class_name in *)
  TName ("class" ^ cl)

(* Instances definitions *)

and instance_definitions env instances =
  let env = List.fold_left (fun env ins ->
      bind_instance ins env) env instances in
  let rec step env = function
  | [] -> env
  | ins :: t -> let env = instance_definition env ins in
    step env t
  in
  step env instances

and instance_definition env instance =
  check_superclasses_instances env instance;
  check_instance_members env instance;
  env

and check_superclasses_instances env instance =
  let pos = instance.instance_position in
  let sclasses = lookup_superclasses pos instance.instance_class_name env in
  let index = instance.instance_index in
  List.iter (fun cl ->
      try ignore (lookup_instance pos cl index env)
      with e -> raise e) sclasses


and check_instance_members env ins =
  let pos = ins.instance_position in
  let class_ = lookup_class pos ins.instance_class_name env in
  let class_members = class_.class_members in
  let xenv = extended_env env ins class_ in
  List.iter2 (fun (pos, lname, mltype) (RecordBinding (LName n, expr)) ->
      let _, ty = expression xenv expr in
      let r_type = reconstruct_type ins in
      check_reconstructed_type_arity xenv r_type;
      let mltype = substitute [class_.class_parameter, r_type] mltype in
      if not @@ equivalent mltype ty then
        raise (IncompatibleTypes (pos, ty, mltype))
    ) class_members ins.instance_members

and extended_env env ins class_ =
  let class_members = class_.class_members in
  let env = List.fold_left
      (fun env tname -> bind_type_variable tname env)
      env ins.instance_parameters in
  List.fold_left
    (fun env (pos, (LName name), mltype) ->
       bind_scheme (Name name) [class_.class_parameter] mltype env) env class_members


and reconstruct_type ins =
  let pos = ins.instance_position in
  let type_parameters =
    List.map (fun tname -> TyVar (pos, tname)) ins.instance_parameters in
  TyApp (ins.instance_position, ins.instance_index, type_parameters)

and check_reconstructed_type_arity env = function
  | (TyApp (pos, tname, params)) ->
    let kind = lookup_type_kind pos tname env in
    if kind_of_arity (List.length params) <> kind then
      raise (InvalidTypeApplication pos)
  | _ -> assert false


(* and check *)
