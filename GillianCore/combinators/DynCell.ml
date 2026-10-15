(** A cell whose absence is a state of the cell, not an error; the counterpart
    of CSE's [DynCell] (js_theories/DynCell.v).

    An owned cell is either absent, represented by the value [none], or holds a
    value. Reading an absent cell yields [none], writing one creates it, and
    deleting one is a successful no-op. Writing [none] is an error: absence is
    only reached by deleting. *)

open Utils
open Monadic
open Engine.Symbolic
open Gil_syntax
module DR = Delayed_result
module Recovery_tactic = Engine.General.Recovery_tactic

type t = Expr.t option [@@deriving show, yojson]
type err_t = MissingState | MutateAbsent [@@deriving show, yojson]
type action = Lookup | Mutate | Delete
type pred = Dyn [@@deriving yojson]

let absent = Expr.Lit Nono
let pp = Fmt.(option ~none:(any "None") Expr.pp)

let action_from_str = function
  | "lookup" -> Some Lookup
  | "mutate" -> Some Mutate
  | "delete" -> Some Delete
  | _ -> None

let action_to_str = function
  | Lookup -> "lookup"
  | Mutate -> "mutate"
  | Delete -> "delete"

let list_actions () =
  [ (Lookup, [], [ "value" ]); (Mutate, [ "value" ], []); (Delete, [], []) ]

let pred_from_str = function
  | "dyn" -> Some Dyn
  | _ -> None

let pred_to_str = function
  | Dyn -> "dyn"

let list_preds () = [ (Dyn, [], [ "value" ]) ]
let empty () : t = None

let[@inline] execute_action action s args =
  let open Expr.Infix in
  match (action, s, args) with
  | _, None, _ -> DR.error MissingState
  | Lookup, Some v, [] -> DR.ok (Some v, [ v ])
  | Mutate, Some _, [ v' ] -> (
      match v' with
      | Expr.EList _ | Lit (LList _) -> DR.ok (Some v', [])
      | _ ->
          if%sat v' == absent then DR.error MutateAbsent else DR.ok (Some v', [])
      )
  | Delete, Some _, [] -> DR.ok (Some absent, [])
  | a, _, args ->
      Fmt.failwith "Invalid action %s with state %a and args %a"
        (action_to_str a) pp s (Fmt.Dump.list Expr.pp) args

let[@inline] consume core_pred s args =
  match (core_pred, s, args) with
  | Dyn, Some v, [] -> DR.ok (None, [ v ])
  | Dyn, None, _ -> DR.error MissingState
  | Dyn, _, _ -> failwith "Invalid DynCell consume"

let[@inline] produce core_pred s args =
  match (core_pred, s, args) with
  | Dyn, None, [ v ] -> Delayed.return (Some v)
  | Dyn, Some _, _ -> Delayed.vanish ()
  | Dyn, _, _ -> failwith "Invalid DynCell produce"

let substitution subst s =
  Option.map (Subst.subst_in_expr ~partial:true subst) s |> Delayed.return

let compose s1 s2 =
  match (s1, s2) with
  | None, s | s, None -> Delayed.return s
  | _ -> Delayed.vanish ()

let is_exclusively_owned s _ =
  match s with
  | None -> Delayed.return false
  | Some _ -> Delayed.return true

let is_empty = Option.is_none

let is_concrete = function
  | None -> true
  | Some v -> Expr.is_concrete v

let instantiate = function
  | [] -> (Some absent, [])
  | [ v ] -> (Some v, [])
  | _ -> failwith "Invalid DynCell instantiation"

let lvars = function
  | None -> Containers.SS.empty
  | Some v -> Expr.lvars v

let alocs = function
  | None -> Containers.SS.empty
  | Some v -> Expr.alocs v

let assertions = function
  | None -> []
  | Some v -> [ (Dyn, [], [ v ]) ]

let assertions_others _ = []
let get_recovery_tactic _ _ = Recovery_tactic.none

let can_fix = function
  | MissingState -> true
  | MutateAbsent -> false

let get_fixes = function
  | MissingState ->
      [ [ Fix.CorePred (Dyn, [], [ Expr.LVar (Generators.fresh_svar ()) ]) ] ]
  | MutateAbsent -> []
