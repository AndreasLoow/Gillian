open Gillian.Monadic
open Gillian.Combinators.Shorthands
open Gil_syntax
module ExpMap = Gillian.Combinators.MyUtils.ExpMap
module JSCI = Javert_utils.JSCertInterface

(* Default instantiation is Nono *)
module StringIndex = struct
  include StringIndex

  let default_instantiation _ = [ Expr.Lit Nono ]
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
      ("GetSlot", "right_load");
      ("SetSlot", "right_typed_store");
    ]

  let pred_substitutions =
    [
      ("Cell", "left_dyn");
      ("Props", "left_inner_domainset");
      ("Slot", "right_ex");
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

(* Slot names are fixed (see JSCertInterface), so an index is resolved to a
   name, branching over the names if need be. A slot's default is its own. *)
module SlotIndex : PMapIndex = struct
  let mode : index_mode = Dynamic

  let is_valid_index = function
    | Expr.Lit (String n) as e when JSCI.is_slot_name n ->
        Delayed.return (Some e)
    | Expr.Lit _ -> Delayed.return None
    | e ->
        let open Expr.Infix in
        let names = List.map (fun n -> Expr.string n) JSCI.slot_names in
        Delayed.branches
          (Delayed.return
             ~learned:[ not (Expr.BinOp (e, SetMem, Expr.ESet names)) ]
             None
          :: List.map
               (fun n -> Delayed.return ~learned:[ e == n ] (Some n))
               names)

  let make_fresh () = failwith "Invalid in dynamic mode"

  let default_instantiation = function
    | Expr.Lit (String n) ->
        Option.fold ~none:[]
          ~some:(fun v -> [ Expr.Lit v ])
          (JSCI.slot_default n)
    | _ -> []
end

(* An object's slots. A slot outside the domain set holds its default;
   allocation leaves every slot outside it. *)
module Slots = struct
  include MoveInToOut (PMap (SlotIndex) (Exclusive))

  let instantiate = function
    | [] -> ((fst (empty ()), Some (Expr.ESet [])), [])
    | _ -> failwith "Invalid Slots instantiation"

  let load = Option.get (action_from_str "load")

  (* Reading a slot outside the domain set leaves it there, so that the domain
     set goes on describing it. *)
  let execute_action a ((h, d) as s : t) args =
    let open Delayed.Syntax in
    match (d, args) with
    | Some d, idx :: _ when a = load -> (
        let* idx_opt = SlotIndex.is_valid_index idx in
        match idx_opt with
        | Some (Expr.Lit (String n) as idx') when not (ExpMap.mem idx' h) ->
            if%sat Expr.BinOp (idx', SetMem, d) then execute_action a s args
            else
              let v = Option.get (JSCI.slot_default n) in
              Delayed_result.ok
                ~learned:[ Expr.Infix.(idx == idx') ]
                (s, [ idx'; Expr.Lit v ])
        | _ -> execute_action a s args)
    | _ -> execute_action a s args
end

(* Writing a slot checks the type of the value, since JSCert's fields are
   typed. *)
module TypedStore (S : sig
  include MyMonadicSMemory

  val store : action
end) : ActionAddition with type t = S.t = struct
  type t = S.t
  type action = TypedStore

  type err_t = StoreErr of S.err_t | SlotType of Expr.t * Expr.t
  [@@deriving show, yojson]

  let list_actions () = [ (TypedStore, [ "index"; "value" ], []) ]
  let action_from_str s = if s = JSCI.typed_store then Some TypedStore else None
  let action_to_str TypedStore = JSCI.typed_store

  let[@inline] execute_action TypedStore s args =
    let open Delayed.Syntax in
    let store args =
      Delayed.map (S.execute_action S.store s args) (function
        | Ok x -> Ok x
        | Error e -> Error (StoreErr e))
    in
    match args with
    | [ idx; v ] -> (
        let* idx_opt = SlotIndex.is_valid_index idx in
        match idx_opt with
        | Some (Expr.Lit (String n) as idx') -> (
            match JSCI.slot_types n with
            | None -> store [ idx'; v ]
            | Some tys ->
                let tys =
                  Expr.ESet (List.map (fun t -> Expr.Lit (Type t)) tys)
                in
                if%sat Expr.BinOp (Expr.UnOp (TypeOf, v), SetMem, tys) then
                  store [ idx'; v ]
                else Delayed_result.error (SlotType (idx', v)))
        | _ -> store args)
    | _ -> store args

  let can_fix _ = false
  let get_fixes _ = []
  let get_recovery_tactic _ _ = Gillian.General.Recovery_tactic.none
end

module SlotsStore = struct
  include Slots

  let store = Option.get (action_from_str "store")
end

module TypedSlots = ActionAdder (TypedStore (SlotsStore)) (Slots)

(* The content of memory at a given location: properties * slots *)
module BaseMemoryContent (S : MyMonadicSMemory) = struct
  module S =
    PatchedProduct (IDs) (Mapper (JSSubstInner) (MoveInToOut (S))) (TypedSlots)

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

(* Allocation takes the address to allocate into, or 'empty' for a new
   address. Similarly to WISL, return the index on each action. *)
module PatchAlloc (Map : OpenPMapType) = struct
  include Map

  (* Patch the alloc action *)
  let[@inline] execute_action a s args =
    let open Delayed.Syntax in
    match (action_to_str a, args) with
    | "alloc", [ idx ] ->
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
        let ss, v = Map.Entry.instantiate [] in
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

(* The concrete memory, from the concrete counterparts of the combinators
   above, so that concrete and symbolic execution share the memory model. *)
module Concrete = struct
  module C = Gillian.Combinators.CCombinators

  module Props =
    C.TotalMap
      (C.DynCell)
      (struct
        type entry = C.DynCell.t

        let is_key = function
          | Literal.String _ -> true
          | _ -> false

        let default _ = Some C.DynCell.Absent
      end)

  module PropsWithKeys =
    C.Keys
      (Props)
      (struct
        type t = Props.t

        let keys m =
          List.filter_map
            (function
              | k, Some (C.DynCell.Val _) -> Some k
              | _ -> None)
            (Props.bindings m)
      end)

  module Slots =
    C.TotalMap
      (C.Exclusive)
      (struct
        type entry = C.Exclusive.t

        let is_key = function
          | Literal.String n -> JSCI.is_slot_name n
          | _ -> false

        let default = function
          | Literal.String n -> JSCI.slot_default n
          | _ -> None
      end)

  module TypedSlots = struct
    include Slots

    let execute_action a s args =
      match (a, args) with
      | "typed_store", [ (Literal.String n as k); v ] -> (
          match JSCI.slot_types n with
          | Some tys when not (List.mem (Literal.type_of v) tys) ->
              C.err "slot mutate err: type" [ k; v ]
          | _ -> Slots.execute_action "store" s args)
      | "typed_store", _ -> Slots.execute_action "store" s args
      | _ -> Slots.execute_action a s args
  end

  module Object = C.Product (IDs) (PropsWithKeys) (TypedSlots)

  module Names : NameMap = struct
    let action_substitutions =
      [
        ("GetCell", "left_lookup");
        ("SetCell", "left_mutate");
        ("DeleteCell", "left_delete");
        ("GetAllProps", "left_keys");
        ("Alloc", "alloc");
        ("DeleteObject", "free");
        ("GetSlot", "right_load");
        ("SetSlot", "right_typed_store");
      ]

    let pred_substitutions = []
  end

  include
    C.Make
      (Gillian.General.Init_data.Dummy)
      (C.Filter
         (struct
           let actions = JSFilter.action_filters
         end)
         (C.Mapper (Names) (C.Heap (Object))))
end
