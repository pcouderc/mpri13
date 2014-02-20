open Positions
open Name
open XAST
open Types
open ElaborationExceptions


type class_tree = Class of tname * class_tree list

type t = {
  values       : (tnames * binding) list;
  types        : (tname * (Types.kind * type_definition)) list;
  classes      : (tname * (class_definition * class_tree)) list;
  labels       : (lname * (tnames * Types.t * tname)) list;
  instances    : ((tname * tname) * instance_definition) list;
  members      : (tname * tname) list;
  class_types  : (tname * tname) list
}

let empty = { values = [];
              types = [];
              classes = [];
              labels = [];
              instances = [];
              members = [];
              class_types = []
            }

let values env = env.values

let lookup pos x env =
  try
    List.find (fun (_, (x', _)) -> x = x') env.values
  with Not_found -> raise (UnboundIdentifier (pos, x))

let bind_scheme x ts ty env =
  { env with values = (ts, (x, ty)) :: env.values }

let bind_simple x ty env =
  bind_scheme x [] ty env

let bind_type t kind tdef env =
  { env with types = (t, (kind, tdef)) :: env.types }

let lookup_type pos t env =
  try
    List.assoc t env.types
  with Not_found ->
    raise (UnboundTypeVariable (pos, t))

let lookup_type_kind pos t env =
  fst (lookup_type pos t env)

let lookup_type_definition pos t env =
  snd (lookup_type pos t env)

let lookup_class pos k env =
  try
    fst @@ List.assoc k env.classes
  with Not_found -> raise (UnboundClass (pos, k))

let lookup_class_tree pos k env =
  try
    snd @@ List.assoc k env.classes
  with Not_found -> raise (UnboundClass (pos, k))

let generate_class_tree pos k env =
  let sclasses =
    List.map (fun c -> lookup_class_tree pos c env) k.superclasses in
  Class (k.class_name, sclasses)

let bind_class k c env =
  let pos = c.class_position in
  let ct = generate_class_tree pos c env in
  try
    ignore (lookup_class pos k env);
    raise (AlreadyDefinedClass (pos, k))
  with UnboundClass _ ->
    { env with classes = (k, (c, ct)) :: env.classes }

let lookup_superclasses pos k env =
  (lookup_class pos k env).superclasses

let lookup_classes_definition pos lnames env =
  List.map (fun k -> lookup_class pos k env) lnames

let find_path pos k1 k2 env =
  let rec find acc t =
    match acc with
    | None -> None
    | Some acc ->
      match t with
      | Class (k, []) -> if k = k2 then Some (k :: acc) else None
      | Class (k, l) -> if k = k2 then Some (k :: acc) else
          List.fold_left find (Some acc) l
  in
  let ct = lookup_class_tree pos k1 env in
  find (Some []) ct


(** ! Modified ! *)
let is_superclass pos k1 k2 env =
  match find_path pos k1 k2 env with
  | None -> false
  | Some _ -> true

let bind_type_variable t env =
  bind_type t KStar (TypeDef (undefined_position, KStar, t, DAlgebraic [])) env

let lookup_label pos l env =
  try
    List.assoc l env.labels
  with Not_found ->
    raise (UnboundLabel (pos, l))

let bind_label pos l ts ty rtcon env =
  try
    ignore (lookup_label pos l env);
    raise (LabelAlreadyTaken (pos, l))
  with UnboundLabel _ ->
    { env with labels = (l, (ts, ty, rtcon)) :: env.labels }

let lookup_instance pos classname index env =
  try
    List.assoc (classname, index) env.instances
  with Not_found ->
    raise (UnboundInstance (pos, classname, index))

let lookup_class_instances pos classname env =
  List.fold_left
    (fun acc ((cl, _), inst) -> if cl = classname then inst :: acc else acc)
    [] env.instances

let bind_instance ins env =
  let classname = ins.instance_class_name in
  let index = ins.instance_index in
  try
    let pos = ins.instance_position in
    ignore (lookup_instance pos classname index env);
    raise (AlreadyDefinedInstance (pos, classname, index))
  with
  | UnboundInstance _ -> { env with instances = ((classname, index), ins) ::
  env.instances }

let lookup_member pos tname env =
    List.assoc tname env.members

let bind_member pos ((TName n) as tname) ty env =
  try
    ignore (lookup_member pos tname env);
    raise (OverloadedSymbolCannotBeBound (pos, Name n))
  with Not_found ->
    { env with members = (tname, ty) :: env.members }

let lookup_class_type pos tname env =
  List.assoc tname env.class_types

let get_type_of_class pos tname env =
  fst @@ List.find (fun (_, cl) -> cl = tname) env.class_types

let bind_class_type pos ty cl env =
  try
    ignore (lookup_class_type pos ty env);
    raise (AlreadyDefinedClass (pos, ty))
  with Not_found ->
    { env with class_types = (ty, cl) :: env.class_types }

let initial =
  let primitive_type t k = TypeDef (undefined_position, k, t, DAlgebraic []) in
  List.fold_left (fun env (t, k) ->
    bind_type t k (primitive_type t k) env
  ) empty [
    (TName "->", KArrow (KStar, KArrow (KStar, KStar)));
    (TName "int", KStar);
    (TName "char", KStar);
    (TName "unit", KStar)
  ]
