(** A slot of a JavaScript object; the counterpart of CSE's [SlotCell]
    (js_theories/SlotCell.v).

    An owned slot either holds a value or is in its default state, which reads
    back as the slot's default (JSCertInterface). The cell does not know which
    slot it is, so the slot's name is the first argument of every action and of
    the predicate: the map of slots passes it on along with its index.

    The predicate describes a slot holding a value; a slot in its default state
    is described by the domain of the map of slots instead. *)

open Gillian.Monadic
open Gil_syntax
module DR = Delayed_result
module Recovery_tactic = Gillian.General.Recovery_tactic
module Containers = Gillian.Utils.Containers
module Subst = Gillian.Symbolic.Subst
module JSCI = Javert_utils.JSCertInterface

type cell = Default | Val of Expr.t [@@deriving yojson]
type t = cell option [@@deriving yojson]

type err_t = MissingState | UnknownSlot of Expr.t | DefaultSlot
[@@deriving show, yojson]

type action = Lookup | Mutate
type pred = Slot [@@deriving yojson]

let pp ft = function
  | None -> Fmt.string ft "None"
  | Some Default -> Fmt.string ft "default"
  | Some (Val v) -> Expr.pp ft v

let default_of = function
  | Expr.Lit (String n) -> Option.map Expr.lit (JSCI.slot_default n)
  | _ -> None

let action_from_str = function
  | "lookup" -> Some Lookup
  | "mutate" -> Some Mutate
  | _ -> None

let action_to_str = function
  | Lookup -> "lookup"
  | Mutate -> "mutate"

let list_actions () =
  [ (Lookup, [ "slot" ], [ "value" ]); (Mutate, [ "slot"; "value" ], []) ]

let pred_from_str = function
  | "slot" -> Some Slot
  | _ -> None

let pred_to_str = function
  | Slot -> "slot"

let list_preds () = [ (Slot, [ "slot" ], [ "value" ]) ]
let empty () : t = None

(* The value an owned slot reads back as *)
let read k = function
  | Val v -> DR.ok v
  | Default -> (
      match default_of k with
      | Some v -> DR.ok v
      | None -> DR.error (UnknownSlot k))

let[@inline] execute_action action s args =
  let open DR.Syntax in
  match (action, s, args) with
  | _, None, _ -> DR.error MissingState
  | Lookup, Some c, [ k ] ->
      let++ v = read k c in
      (s, [ v ])
  | Mutate, Some _, [ _; v ] -> DR.ok (Some (Val v), [])
  | a, _, args ->
      Fmt.failwith "Invalid action %s with state %a and args %a"
        (action_to_str a) pp s (Fmt.Dump.list Expr.pp) args

let[@inline] consume core_pred s args =
  match (core_pred, s, args) with
  | Slot, Some (Val v), [ _ ] -> DR.ok (None, [ v ])
  | Slot, Some Default, [ _ ] -> DR.error DefaultSlot
  | Slot, None, _ -> DR.error MissingState
  | Slot, _, _ -> failwith "Invalid SlotCell consume"

let[@inline] produce core_pred s args =
  match (core_pred, s, args) with
  | Slot, None, [ _; v ] -> Delayed.return (Some (Val v))
  | Slot, Some _, _ -> Delayed.vanish ()
  | Slot, _, _ -> failwith "Invalid SlotCell produce"

let substitution subst = function
  | Some (Val v) ->
      Delayed.return (Some (Val (Subst.subst_in_expr ~partial:true subst v)))
  | s -> Delayed.return s

let compose s1 s2 =
  match (s1, s2) with
  | None, s | s, None -> Delayed.return s
  | _ -> Delayed.vanish ()

let is_exclusively_owned s _ = Delayed.return (Option.is_some s)
let is_empty = Option.is_none

let is_concrete = function
  | Some (Val v) -> Expr.is_concrete v
  | _ -> true

let instantiate = function
  | [] -> (Some Default, [])
  | _ -> failwith "Invalid SlotCell instantiation"

let lvars = function
  | Some (Val v) -> Expr.lvars v
  | _ -> Containers.SS.empty

let alocs = function
  | Some (Val v) -> Expr.alocs v
  | _ -> Containers.SS.empty

(* Without its name the cell cannot state its assertion: the map of slots does
   (see [JSILMemory.Slots]). *)
let assertions _ = []
let assertions_others _ = []
let get_recovery_tactic _ _ = Recovery_tactic.none

let can_fix = function
  | MissingState -> true
  | UnknownSlot _ | DefaultSlot -> false

let get_fixes = function
  | MissingState ->
      [
        [
          Gillian.Combinators.Fix.CorePred
            (Slot, [], [ Expr.LVar (Gillian.Utils.Generators.fresh_svar ()) ]);
        ];
      ]
  | UnknownSlot _ | DefaultSlot -> []
