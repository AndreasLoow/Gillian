(* The debugger's view of the JavaScript memory: the generic GIL lifter, with
   the heap shown as JavaScript objects. Objects are read off the memory's
   core predicates rather than its internal state, so that the view does not
   depend on how the memory is assembled. *)

open Gil_syntax
open Debugger.Utils
module PC = Js2jsil_lib.JS2GIL_ParserAndCompiler
module SMemory = Js_memory.JSILMemory.Symbolic
module JSCI = Javert_utils.JSCertInterface
module JSILNames = Javert_utils.JSILNames

type obj = {
  mutable props : (Expr.t * Expr.t) list;
  mutable props_domain : Expr.t option;
  mutable slots : (Expr.t * Expr.t) list;
  mutable slots_domain : Expr.t option;
}

let to_str pp = Fmt.to_to_string (Fmt.hbox pp)

(* The objects of the memory, by location, in order of appearance *)
let objects_of memory : (Expr.t * obj) list =
  let objs = ref [] in
  let get loc =
    match List.assoc_opt loc !objs with
    | Some o -> o
    | None ->
        let o =
          { props = []; props_domain = None; slots = []; slots_domain = None }
        in
        objs := (loc, o) :: !objs;
        o
  in
  List.iter
    (function
      | Asrt.CorePred (p, [ l; k ], [ v ]) when p = JSILNames.aCell ->
          let o = get l in
          o.props <- (k, v) :: o.props
      | Asrt.CorePred (p, [ l; d ], []) when p = JSILNames.aProps ->
          (get l).props_domain <- Some d
      | Asrt.CorePred (p, [ l; k ], [ v ]) when p = JSCI.a_slot ->
          let o = get l in
          o.slots <- (k, v) :: o.slots
      | Asrt.CorePred (p, [ l; d ], []) when p = JSCI.a_slots_domain ->
          (get l).slots_domain <- Some d
      | _ -> ())
    (SMemory.assertions memory);
  List.rev !objs

let sorted l = List.sort (fun (k, _) (k', _) -> Expr.compare k k') l

(* The fields of an attribute record, named *)
let attribute_fields (v : Expr.t) : (string * string) list option =
  let named names es =
    if List.length es = List.length names then
      Some (List.combine names (List.map (to_str Expr.pp) es))
    else None
  in
  let es =
    match v with
    | Expr.EList es -> Some es
    | Expr.Lit (LList ls) -> Some (List.map Expr.lit ls)
    | _ -> None
  in
  match es with
  | Some (Expr.Lit (String "d") :: es) ->
      named [ "value"; "writable"; "enumerable"; "configurable" ] es
  | Some (Expr.Lit (String "a") :: es) ->
      named [ "get"; "set"; "enumerable"; "configurable" ] es
  | _ -> None

let add_heap_variables memory (variables : Variable.ts) new_var_ref :
    Variable.scope list =
  let node name children =
    let id = new_var_ref () in
    Hashtbl.replace variables id children;
    Variable.create_node name id ()
  in
  let domain name = function
    | Some d -> [ Variable.create_leaf name (to_str Expr.pp d) () ]
    | None -> []
  in
  let prop (k, v) =
    let name = to_str Expr.pp k in
    match v with
    | Expr.Lit Nono -> Variable.create_leaf name "absent" ()
    | _ -> (
        match attribute_fields v with
        | Some fields ->
            node name
              (List.map (fun (f, x) -> Variable.create_leaf f x ()) fields)
        | None -> Variable.create_leaf name (to_str Expr.pp v) ())
  in
  let slot (k, v) =
    Variable.create_leaf (to_str Expr.pp k) (to_str Expr.pp v) ()
  in
  let obj (loc, o) =
    node (to_str Expr.pp loc)
      ([
         node "properties" (List.map prop (sorted o.props));
         node "slots" (List.map slot (sorted o.slots));
       ]
      @ domain "property domain" o.props_domain
      @ domain "slot domain" o.slots_domain)
  in
  let id = new_var_ref () in
  Hashtbl.replace variables id (List.map obj (objects_of memory));
  [ { id; name = "Objects" } ]

module Make
    (Verification : Gillian.Abstraction.Verifier.S with type annot = PC.Annot.t) =
struct
  include Gillian.Debugger.Lifter.Gil_lifter.Make (SMemory) (PC) (Verification)

  let get_variables = get_variables' ~add_heap_variables
end
