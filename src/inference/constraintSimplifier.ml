open InferenceTypes
open MultiEquation
open Name



(** [Unsat] is raised if a canonical constraint C ≡ false. *)
exception Unsat

(** [OverlappingInstances] is raised if two rules of kind (E) overlap. *)
exception OverlappingInstances of tname * variable

(** [MultipleClassDefinitions k] is raised if two rules of kind (I)
    share the same goal. *)
exception MultipleClassDefinitions of tname

(** [UnboundClass k] is raised if the type class [k] occurs in a
    constraint while it is undefined. *)
exception UnboundClass of tname

(** Student! This is your job! You must implement the following functions: *)

type equivalence = variable list * ((tname * variable) * (tname * variable)) list
type implication = tname * tname list

let equivs = ref []
let implics = ref []

(** [equivalent [b1;..;bN] k t [(k_1,t_1);...;(k_N,t_N)]] registers
    a rule of the form (E). *)
let equivalent vl cl v ps =
  List.iter (fun (_, ((cl', v'), _)) ->
      if cl = cl' && v = v' then
        raise (OverlappingInstances (cl', v'))) !equivs;
  equivs := (vl, ((cl, v), ps)) :: !equivs

(** [canonicalize pos pool c] where [c = [(k_1,t_1);...;(k_N,t_N)]]
    decomposes [c] into an equivalent constraint [c' =
    [(k'_1,v_1);...;(k'_M,v_M)]], introducing the variables
    [v_1;...;v_M] in [pool]. It raises [Unsat] if the given constraint
    is equivalent to [false]. *)
let canonicalize pos pool k =
  (* Todo ? =>
     - Get each equivalences of k
     - Assemble them and remove the doubles
     - Get the variable in pool
     - Introduce them and verify that  the number of classes = number of vars
     - Return the new constraint
  *)

  let constraints =
    List.fold_left (fun acc (k, _) ->
        let _, (_, ps) = (List.find (fun (_,((cl,_),_)) -> cl = k) !equivs) in
        ps :: acc) [] k in

  let rec remove_doubles acc = function
    | [] -> acc
    | (k, t) :: tl ->
      if List.mem k acc then remove_doubles acc tl
      else remove_doubles (k :: acc) tl in

  let constraints = remove_doubles [] @@ List.flatten constraints in
  try List.combine constraints @@ inhabitants pool
  with Invalid_argument _ -> raise Unsat

(** [add_implication k [k_1;...;k_N]] registers a rule of the form
    (E'). *)
let add_implication cl sc =
  List.iter (fun k ->
      if not @@ List.mem_assoc k !implics then
        raise (UnboundClass k)) sc;
  implics := (cl, sc) :: !implics

(** [entails C1 C2] returns true is the canonical constraint [C1] implies
    the canonical constraint [C2]. *)
let entails _ _ = true

(** [contains k1 k2] *)
let contains _ _ = true
