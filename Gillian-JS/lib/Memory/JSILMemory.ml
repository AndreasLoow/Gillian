open Gillian.Monadic
open Gillian.Combinators.Shorthands
open Gil_syntax
module ExpMap = Gillian.Combinators.MyUtils.ExpMap
module JSCI = Javert_utils.JSCertInterface

(* Default instantiation is Nono *)
module StringIndex = struct
  include StringIndex

  let default_instantiation = [ Expr.Lit Nono ]
end

(* An object: its properties and its slots. Neither side takes arguments when
   allocated. *)
module PatchedProduct
    (IDs : IDs)
    (S1 : Gillian.Combinators.MyMonadicSMemory.S)
    (S2 : Gillian.Combinators.MyMonadicSMemory.S) :
  Gillian.Combinators.MyMonadicSMemory.S with type t = S1.t * S2.t = struct
  include Product (IDs) (S1) (S2)

  let instantiate _ =
    let s1, v1 = S1.instantiate [] in
    let s2, v2 = S2.instantiate [] in
    ((s1, s2), v1 @ v2)

  let pp ft (s1, s2) = Fmt.pf ft "%a, slots %a" S1.pp s1 S2.pp s2
end

(* Add an action to delete objects *)

module DeleteActionAddition (S : MyMonadicSMemory) :
  ActionAddition with type t = S.t = struct
  type t = S.t
  type action = Delete
  type err_t = unit [@@deriving show, yojson]

  let list_actions () = [ (Delete, [], []) ]

  let action_from_str = function
    | "delete" -> Some Delete
    | _ -> None

  let action_to_str Delete = "delete"
  let[@inline] execute_action Delete _ _ = Delayed.return (Ok (S.empty (), []))
  let can_fix () = false
  let get_fixes () = []
  let get_recovery_tactic _ () = Gillian.General.Recovery_tactic.none
end

(* the "Props" predicate considers its out an in, so it must be removed
   from consumption and then checked for equality. *)
module MoveInToOut (S : Gillian.Combinators.MyMonadicSMemory.S) :
  Gillian.Combinators.MyMonadicSMemory.S with type t = S.t = struct
  include S

  let[@inline] consume pred s ins =
    match (pred_to_str pred, ins) with
    | "domainset", [ out ] -> (
        let open Delayed_result.Syntax in
        let** s', outs = S.consume pred s [] in
        match outs with
        | [ out' ] ->
            if%sat Expr.Infix.(out == out') then Delayed_result.ok (s', [])
            else Delayed.vanish ()
        | _ -> Delayed_result.ok (s', outs))
    | _ -> consume pred s ins

  (* Likewise, the domain is an in of the assertions and the signature. *)
  let move_domainset (p, ins, outs) =
    if pred_to_str p = "domainset" then (p, ins @ outs, []) else (p, ins, outs)

  let assertions s = List.map move_domainset (S.assertions s)
  let list_preds () = List.map move_domainset (S.list_preds ())
end

(* Outer substitutions for JS *)
module JSSubst : NameMap = struct
  let action_substitutions =
    [
      ("GetCell", "left_lookup");
      ("SetCell", "left_mutate");
      ("DeleteCell", "left_delete");
      ("GetAllProps", "left_inner_get_domainset");
      ("Alloc", "alloc");
      ("DeleteObject", "delete");
      ("GetSlot", "right_lookup");
      ("SetSlot", "right_mutate");
    ]

  let pred_substitutions =
    [
      ("Cell", "left_dyn");
      ("Props", "left_inner_domainset");
      ("Slot", "right_slot");
      ("SlotsDomain", "right_domainset");
    ]
end

(* Substitutions for internal PMap (avoids name clash) *)
module JSSubstInner : NameMap = struct
  let action_substitutions = [ ("inner_get_domainset", "get_domainset") ]
  let pred_substitutions = [ ("inner_domainset", "domainset") ]
end

(* Outer pred/action filter *)
module JSFilter : FilterVals = struct
  let mode : filter_mode = ShowOnly

  let action_filters =
    [
      "GetCell";
      "SetCell";
      "DeleteCell";
      "Alloc";
      "DeleteObject";
      "GetAllProps";
      "GetSlot";
      "SetSlot";
    ]

  let preds_filters = [ "Cell"; "Props"; "Slot"; "SlotsDomain" ]
end

(* Patch domainset to filter out all Nonos *)
module PatchDomainsetObject (S : sig
  include MyMonadicSMemory

  val get_nonos : t -> Expr.t list
  val is_not_nono : t -> Expr.t -> bool
end) =
  Injector
    (struct
      include DummyInject (S)

      let post_execute_action a (s, args, rets) =
        match (a, rets) with
        | "get_domainset", [ dom ] ->
            let open Delayed.Syntax in
            let* dom =
              match dom with
              | Expr.Lit (LList lits) ->
                  List.map Expr.lit lits
                  |> List.filter (S.is_not_nono s)
                  |> Expr.list |> Delayed.return
              | Expr.EList lits ->
                  lits
                  |> List.filter (S.is_not_nono s)
                  |> Expr.list |> Delayed.return
              | dom ->
                  let nonos = Expr.ESet (S.get_nonos s) in
                  Delayed.reduce (BinOp (dom, SetDiff, nonos))
            in
            Delayed.return (s, args, [ dom ])
        | _ -> Delayed.return (s, args, rets)

      let post_consume p (s, outs) =
        match (p, outs) with
        | "domainset", [ Expr.ESet dom ] ->
            let dom = List.filter (S.is_not_nono s) dom in
            Delayed.return (s, [ Expr.ESet dom ])
        | _ -> Delayed.return (s, outs)
    end)
    (S)

(* Slot names are fixed: see JSCertInterface *)
module SlotIndex : PMapIndex = struct
  let mode : index_mode = Dynamic

  let is_valid_index = function
    | Expr.Lit (String n) as e when JSCI.is_slot_name n ->
        Delayed.return (Some e)
    | Expr.Lit _ -> Delayed.return None
    | e -> Delayed.return (Some e)

  let make_fresh () = failwith "Invalid in dynamic mode"
  let default_instantiation = []
end

(* An object's slots. A slot outside the domain set is in its default state;
   allocation leaves every slot in it. A slot's cell takes the slot's name as
   its first argument, so actions and predicates on a slot repeat its index. *)
module Slots = struct
  include MoveInToOut (PMap (SlotIndex) (SlotCell))

  let instantiate = function
    | [] -> ((fst (empty ()), Some (Expr.ESet [])), [])
    | _ -> failwith "Invalid Slots instantiation"

  let slot_pred = Option.get (pred_from_str "slot")
  let domainset_pred = Option.get (pred_from_str "domainset")

  (* The cells cannot state their own assertions, which need their names *)
  let assertions ((h, d) : t) =
    ExpMap.fold
      (fun k c acc ->
        let v =
          match c with
          | Some (SlotCell.Val v) -> Some v
          | Some SlotCell.Default -> SlotCell.default_of k
          | None -> None
        in
        match v with
        | Some v -> (slot_pred, [ k; k ], [ v ]) :: acc
        | None -> acc)
      h []
    @ Option.fold ~none:[] ~some:(fun d -> [ (domainset_pred, [ d ], []) ]) d

  let get_fixes e =
    get_fixes e
    |> Gillian.Combinators.Fix.map_corepred (fun (p, ins, outs) ->
           match ins with
           | k :: ins when p = slot_pred -> (p, k :: k :: ins, outs)
           | _ -> (p, ins, outs))

  let pp ft ((h, d) : t) =
    let open Fmt in
    let pp_bindings =
      iter_bindings ~sep:comma ExpMap.iter
        (hbox (pair ~sep:(any ": ") Expr.pp SlotCell.pp))
    in
    pf ft "[ @[%a@] | @[%a@] ]" pp_bindings h (option Expr.pp) d
end

(* The content of memory at a given location: properties * slots *)
module BaseMemoryContent (S : MyMonadicSMemory) = struct
  module S =
    PatchedProduct (IDs) (Mapper (JSSubstInner) (MoveInToOut (S))) (Slots)

  include ActionAdder (DeleteActionAddition (S)) (S)
end

(* Override pretty printing, implement `is_not_nono` *)
module ObjectBase = struct
  include PMap (StringIndex) (DynCell)

  let pp ft ((h, d) : t) =
    let d =
      match d with
      | Some (Expr.ESet l) -> Some (Expr.ESet (List.sort Expr.compare l))
      | e -> e
    in
    let open Fmt in
    let pp_bindings =
      iter_bindings ~sep:comma ExpMap.iter
        (hbox (parens (pair ~sep:(any " :") Expr.pp DynCell.pp)))
    in
    pf ft "[ @[%a@] | @[%a@] ]" pp_bindings h (option Expr.pp) d

  let get_nonos (h, _) =
    ExpMap.fold
      (fun _ v acc ->
        match v with
        | Some (Expr.Lit Nono) -> Expr.Lit Nono :: acc
        | _ -> acc)
      h []

  let is_not_nono (h, _) idx =
    match ExpMap.find_opt idx h with
    | Some (Some (Expr.Lit Nono)) -> false
    | _ -> true
end

(* Override pretty printing, implement `is_not_nono` *)
module SplitObjectBase = struct
  include SplitPMap (StringIndex) (DynCell)

  let pp ft (((ch, sh), d) : t) =
    let h = ExpMap.union (fun _ a _ -> Some a) ch sh in
    let d =
      match d with
      | Some (Expr.ESet l) -> Some (Expr.ESet (List.sort Expr.compare l))
      | e -> e
    in
    let open Fmt in
    let pp_bindings =
      iter_bindings ~sep:comma ExpMap.iter
        (hbox (parens (pair ~sep:(any " :") Expr.pp DynCell.pp)))
    in
    pf ft "[ @[%a@] | @[%a@] ]" pp_bindings h (option Expr.pp) d

  let get_nonos (((ch, sh), _) : t) =
    let nonos_from_map m =
      ExpMap.fold
        (fun _ v acc ->
          match v with
          | Some (Expr.Lit Nono) -> Expr.Lit Nono :: acc
          | _ -> acc)
        m []
    in
    nonos_from_map ch @ nonos_from_map sh

  let is_not_nono ((ch, sh), _) idx =
    match ExpMap.find_opt idx ch with
    | Some (Some (Expr.Lit Nono)) -> false
    | _ -> (
        match ExpMap.find_opt idx sh with
        | Some (Some (Expr.Lit Nono)) -> false
        | _ -> true)
end

(* Patch map pretty-printing for nicer diffs *)
module PatchedBasePMap (S : MyMonadicSMemory) = struct
  include OpenPMap (LocationIndex) (S)

  let pp ft (h : t) =
    let open Fmt in
    let sorted_locs_with_vals =
      ExpMap.bindings h |> List.sort (fun (k1, _) (k2, _) -> Expr.compare k1 k2)
    in
    let pp_one ft (loc, fv_pairs) =
      pf ft "@[%a |-> %a@]" Expr.pp loc S.pp fv_pairs
    in
    (list ~sep:(any "@\n") pp_one) ft sorted_locs_with_vals
end

(* Patch map pretty-printing for nicer diffs *)
module PatchedALocPMap (S : MyMonadicSMemory) = struct
  include OpenALocPMap (S)

  let pp ft (h : t) =
    let open Fmt in
    let sorted_locs_with_vals =
      Gillian.Combinators.MyUtils.SMap.bindings h
      |> List.sort (fun (k1, _) (k2, _) -> String.compare k1 k2)
    in
    let pp_one ft (loc, fv_pairs) = pf ft "@[%s |-> %a@]" loc S.pp fv_pairs in
    (list ~sep:(any "@\n") pp_one) ft sorted_locs_with_vals
end

(* When allocating, two params are given:
    - the address to allocate into (can be 'empty' to generate new address) - defaults to empty
    - the legacy metadata address, which is ignored: objects have no metadata
   Similarly to WISL, return the index on each action. *)
module PatchAlloc (Map : OpenPMapType) = struct
  include Map

  (* Patch the alloc action *)
  let[@inline] execute_action a s args =
    let open Delayed.Syntax in
    match (action_to_str a, args) with
    | "alloc", [ idx; v ] ->
        let* idx =
          match idx with
          | Expr.Lit Empty -> Delayed.return (Some (ALoc.alloc ()))
          | _ -> Gillian.Combinators.MyUtils.get_loc idx
        in
        let idx =
          match idx with
          | Some idx -> idx
          | None ->
              failwith "Invalid index given for alloc (no error handles this)"
        in
        let idx = Expr.loc_from_loc_name idx in
        let ss, v = Map.Entry.instantiate [ v ] in
        let s' = set ~idx ~idx':idx ss s in
        Delayed_result.ok (s', idx :: v)
    | "alloc", _ -> failwith "Invalid arguments for alloc"
    | _ -> execute_action a s args
end

(* Helper to escape (or create) functor hell *)
module Object = BaseMemoryContent (PatchDomainsetObject (ObjectBase))
module SplitObject = BaseMemoryContent (PatchDomainsetObject (SplitObjectBase))

module Wrap (Map : OpenPMapType) =
  Filter (JSFilter) (Mapper (JSSubst) (PatchAlloc (Map)))

(* Actual exports *)

module MonadicSMemory_Base = Wrap (PatchedBasePMap (Object))
module MonadicSMemory_ALoc = Wrap (PatchedALocPMap (Object))
module MonadicSMemory_Split = Wrap (PatchedBasePMap (SplitObject))
module MonadicSMemory_ALocSplit = Wrap (PatchedALocPMap (SplitObject))

(* The Gillian-JS symbolic memory *)
module Symbolic =
  Gillian.Combinators.MyMonadicSMemory.Make
    (MonadicSMemory_Base)
    (Gillian.Combinators.MyMonadicSMemory.DummyID)
