(* Concrete counterparts of the state combinators. Each follows the concrete
   side of the corresponding CSE combinator: a concrete state can be partial
   (a frame), so a missing resource is a miss, distinct from an error; and
   actions are named, and return their outputs, as on the symbolic side, so
   that one program runs on both. *)

open Gil_syntax

module LMap = Map.Make (struct
  type t = Literal.t

  let compare = Stdlib.compare
end)

type err = Miss | Err of Literal.t list [@@deriving yojson, show]
type 'a res = ('a, err) result

module type S = sig
  type t

  val pp : t Fmt.t
  val instantiate : Literal.t list -> t * Literal.t list
  val execute_action : string -> t -> Literal.t list -> (t * Literal.t list) res
end

let err msg vs = Error (Err (Literal.String msg :: vs))
let unknown_action a = Fmt.failwith "Unknown concrete action %s" a

module Exclusive : S with type t = Literal.t option = struct
  type t = Literal.t option

  let pp = Fmt.(option ~none:(any "None") Literal.pp)

  let instantiate = function
    | [] -> (Some Literal.Undefined, [])
    | [ v ] -> (Some v, [])
    | _ -> failwith "Invalid Exclusive instantiation"

  let execute_action a s args =
    match (a, s, args) with
    | ("load" | "store"), None, _ -> Error Miss
    | "load", Some v, [] -> Ok (s, [ v ])
    | "load", _, _ -> err "load err: args length" []
    | "store", Some _, [ v ] -> Ok (Some v, [])
    | "store", _, _ -> err "store err: args length" []
    | a, _, _ -> unknown_action a
end

(* An absent property is a state of the cell, so that owning it is what
   expresses that the property does not exist. *)
module DynCell : sig
  type cell = Absent | Val of Literal.t

  include S with type t = cell option
end = struct
  type cell = Absent | Val of Literal.t
  type t = cell option

  let absent = Literal.Nono

  let pp =
    Fmt.(
      option ~none:(any "None") (fun ft -> function
        | Absent -> Literal.pp ft absent
        | Val v -> Literal.pp ft v))

  let instantiate = function
    | [] -> (Some Absent, [])
    | [ v ] when v = absent -> (Some Absent, [])
    | [ v ] -> (Some (Val v), [])
    | _ -> failwith "Invalid DynCell instantiation"

  let execute_action a s args =
    match (a, s, args) with
    | ("lookup" | "mutate" | "delete"), None, _ -> Error Miss
    | "lookup", Some Absent, [] -> Ok (s, [ absent ])
    | "lookup", Some (Val v), [] -> Ok (s, [ v ])
    | "lookup", _, _ -> err "lookup err: args length" []
    | "mutate", Some _, [ v ] when v = absent -> err "mutate err: type" []
    | "mutate", Some _, [ v ] -> Ok (Some (Val v), [])
    | "mutate", _, _ -> err "mutate err: args length" []
    | "delete", Some _, [] -> Ok (Some Absent, [])
    | "delete", _, _ -> err "delete err: args length" []
    | a, _, _ -> unknown_action a
end

module Product (IDs : MyUtils.IDs) (S1 : S) (S2 : S) :
  S with type t = S1.t * S2.t = struct
  type t = S1.t * S2.t

  module IDer = MyUtils.Identifier (IDs)

  let pp ft (s1, s2) = Fmt.pf ft "(@[%a@]) × (@[%a@])" S1.pp s1 S2.pp s2

  let instantiate args =
    let s1, v1 = S1.instantiate args in
    let s2, v2 = S2.instantiate args in
    ((s1, s2), v1 @ v2)

  let execute_action a (s1, s2) args =
    match IDer.get_ided a with
    | ID1 a ->
        Result.map
          (fun (s1, vs) -> ((s1, s2), vs))
          (S1.execute_action a s1 args)
    | ID2 a ->
        Result.map
          (fun (s2, vs) -> ((s1, s2), vs))
          (S2.execute_action a s2 args)
    | NotIDed a -> unknown_action a
end

module type TotalMapKey = sig
  type entry

  (* The keys of the map; actions at other keys are type errors *)
  val is_key : Literal.t -> bool

  (* The entry at a key that was never written *)
  val default : Literal.t -> entry
end

(* A map that has an entry at every key. Only the entries that were written are
   stored. *)
module TotalMap (S : S) (K : TotalMapKey with type entry = S.t) : sig
  include S

  val bindings : t -> (Literal.t * S.t) list
end = struct
  type t = S.t LMap.t

  let pp = MyUtils.pp_bindings ~pp_k:Literal.pp ~pp_v:S.pp LMap.iter

  let instantiate = function
    | [] -> (LMap.empty, [])
    | _ -> failwith "Invalid TotalMap instantiation"

  let get k m = Option.value ~default:(K.default k) (LMap.find_opt k m)
  let bindings = LMap.bindings

  let execute_action a m args =
    match args with
    | [] -> err "map err: missing key" []
    | k :: _ when not (K.is_key k) -> err "map err: type" [ k ]
    | k :: args -> (
        match S.execute_action a (get k m) args with
        | Ok (e, vs) -> Ok (LMap.add k e m, k :: vs)
        | Error e -> Error e)
end

module type KeysSpec = sig
  type t

  val keys : t -> Literal.t list
end

(* Adds an action listing the keys of a state, as determined by the
   specification. *)
module Keys (S : S) (Spec : KeysSpec with type t = S.t) : S with type t = S.t =
struct
  include S

  let execute_action a s args =
    match (a, args) with
    | "keys", [] -> Ok (s, [ Literal.LList (Spec.keys s) ])
    | "keys", _ -> err "keys err: args length" []
    | _ -> S.execute_action a s args
end

(* The heap: entries are created by allocation, at a fresh location unless one
   is given, and can be freed. An action at an unallocated location misses. *)
module Heap (S : S) : S with type t = S.t LMap.t = struct
  type t = S.t LMap.t

  let pp =
    Fmt.(
      iter_bindings ~sep:(any "@\n") LMap.iter (fun ft (l, s) ->
          pf ft "@[%a |-> %a@]" Literal.pp l S.pp s))

  let instantiate = function
    | [] -> (LMap.empty, [])
    | _ -> failwith "Invalid Heap instantiation"

  let execute_action a h args =
    match (a, args) with
    | "alloc", idx :: args -> (
        let loc =
          match idx with
          | Literal.Empty -> Some (Literal.Loc (Utils.Generators.fresh_loc ()))
          | Loc _ -> Some idx
          | _ -> None
        in
        match loc with
        | Some loc ->
            let s, vs = S.instantiate args in
            Ok (LMap.add loc s h, loc :: vs)
        | None -> err "alloc err: type" [ idx ])
    | "alloc", [] -> err "alloc err: args length" []
    | "free", [ (Literal.Loc _ as l) ] ->
        if LMap.mem l h then Ok (LMap.remove l h, [ l ]) else Error Miss
    | "free", _ -> err "free err: args" args
    | _, [] -> err "heap err: missing address" []
    | _, (Literal.Loc _ as l) :: args -> (
        match LMap.find_opt l h with
        | None -> Error Miss
        | Some s -> (
            match S.execute_action a s args with
            | Ok (s, vs) -> Ok (LMap.add l s h, l :: vs)
            | Error e -> Error e))
    | _, l :: _ -> err "heap err: type" [ l ]
end

module Mapper (N : Mapper.NameMap) (S : S) : S with type t = S.t = struct
  include S

  let execute_action a =
    S.execute_action (Mapper.subst N.action_substitutions a)
end

(* Only the actions named by the filter are available. *)
module Filter
    (F : sig
      val actions : string list
    end)
    (S : S) : S with type t = S.t = struct
  include S

  let execute_action a =
    if List.mem a F.actions then S.execute_action a else unknown_action a
end

(* The whole concrete memory *)
module Make (InitData : Engine.General.Init_data.S) (S : S) :
  Engine.Concrete.Memory_S with type init_data = InitData.t and type t = S.t =
struct
  type init_data = InitData.t
  type vt = Engine.Concrete.Values.t
  type st = Engine.Concrete.Subst.t
  type err_t = err [@@deriving yojson, show]
  type t = S.t
  type action_ret = (t * vt list, err_t) result

  let init _ = fst (S.instantiate [])
  let copy s = s
  let execute_action = S.execute_action
  let pp = S.pp
  let pp_err = pp_err
end
