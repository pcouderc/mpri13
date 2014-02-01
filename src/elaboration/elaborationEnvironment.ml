open Positions
open Name
open XAST
open Types
open ElaborationExceptions

type t = {
  values       : (tnames * binding) list;
  types        : (tname * (Types.kind * type_definition)) list;
  classes      : (tname * class_definition) list;
  labels       : (lname * (tnames * Types.t * tname)) list;
  instances    : ((tname * tname) * instance_definition) list;
}

let empty = { values = [];
              types = [];
              classes = [];
              labels = [];
              instances = []
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
    List.assoc k env.classes
  with Not_found -> raise (UnboundClass (pos, k))

let bind_class k c env =
  try
    let pos = c.class_position in
    ignore (lookup_class pos k env);
    raise (AlreadyDefinedClass (pos, k))
  with UnboundClass _ ->
    { env with classes = (k, c) :: env.classes }

let lookup_superclasses pos k env =
  (lookup_class pos k env).superclasses

let lookup_classes_definition pos lnames env =
  List.map (fun k -> lookup_class pos k env) lnames

(** ! Modified ! *)
let is_superclass pos k1 k2 env =
  let sclasses = lookup_superclasses pos k1 env in
  if !Misc.debug then
    begin
      Format.printf "function is_superclass@.";
      List.iter (function TName name -> Format.printf "%s; " name) sclasses;
      Format.printf "@."
    end;
  List.mem k2 sclasses

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
  (* if !Misc.debug then Format.printf ("In lookup@."); *)
  (* let _s (TName name) = name in *)
  (* List.iter (fun ((_,_),ins) -> *)
  (*     Format.printf "%s, %s@." (_s ins.instance_class_name) (_s ins.instance_index)) *)
  (*   env.instances; *)
  try
    List.assoc (classname, index) env.instances
  with Not_found ->
    raise (UnboundInstance (pos, classname, index))

let lookup_class_instances pos classname env =
  List.fold_left
    (fun acc ((cl, _), inst) -> if cl = classname then inst :: acc else acc)
    [] env.instances

let bind_instance ins env =
  (* Format.printf ("In binding@."); *)
  let classname = ins.instance_class_name in
  let index = ins.instance_index in
  try
    let pos = ins.instance_position in
    ignore (lookup_instance pos classname index env);
    raise (AlreadyDefinedInstance (pos, classname, index))
  with
  | UnboundInstance _ -> { env with instances = ((classname, index), ins) :: env.instances }

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
