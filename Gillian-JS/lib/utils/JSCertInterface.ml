(** The JSCert object interface of the Gillian-JS memory.

    Each object is a map of properties and a fixed set of slots, one per field
    of JSCert's [object] record (coq/JsSyntax.v) other than its properties, plus
    a few Gillian-only ones. See Gillian-JS/docs/jscert-correspondence.md for
    the correspondence with JSCert and with CSE (js_theories/). *)

open Gil_syntax

(** {1 Slots} *)

type slot = {
  name : string;  (** The Gillian slot name. *)
  jscert : string option;  (** The JSCert field, if any. *)
  default : Literal.t;
      (** The value [Alloc] gives the slot, as [object_new] does in JSCert. An
          option field's [None] is [empty]. *)
}

let slot ?jscert name default = { name; jscert; default }

(* The fields of [object_new proto class] other than [proto] and [class],
   which [Alloc] does not take yet: until it does, they start as [null] and
   ["Object"] and the runtime sets them. *)
let slots : slot list =
  let none = Literal.Empty in
  let default = Literal.String "default" in
  [
    slot "@proto" ~jscert:"object_proto_" Null;
    slot "@class" ~jscert:"object_class_" (String "Object");
    slot "@extensible" ~jscert:"object_extensible_" (Bool true);
    slot "@primitiveValue" ~jscert:"object_prim_value_" none;
    slot "@get" ~jscert:"object_get_" default;
    slot "@getOwnProperty" ~jscert:"object_get_own_prop_" default;
    slot "@getProperty" ~jscert:"object_get_prop_" default;
    slot "@put" ~jscert:"object_put_" default;
    slot "@canPut" ~jscert:"object_can_put_" default;
    slot "@hasProperty" ~jscert:"object_has_prop_" default;
    slot "@delete" ~jscert:"object_delete_" default;
    slot "@defaultValue" ~jscert:"object_default_value_" default;
    slot "@defineOwnProperty" ~jscert:"object_define_own_prop_" default;
    slot "@construct" ~jscert:"object_construct_" none;
    slot "@call" ~jscert:"object_call_" none;
    slot "@hasInstance" ~jscert:"object_has_instance_" none;
    slot "@scope" ~jscert:"object_scope_" none;
    slot "@formalParameters" ~jscert:"object_formal_parameters_" none;
    slot "@code" ~jscert:"object_code_" none;
    slot "@targetFunction" ~jscert:"object_target_function_" none;
    slot "@boundThis" ~jscert:"object_bound_this_" none;
    slot "@boundArguments" ~jscert:"object_bound_args_" none;
    slot "@parameterMap" ~jscert:"object_parameter_map_" none;
    (* Gillian-only: ArrayBuffer, DataView and Uint8Array *)
    slot "@ArrayBufferData" none;
    slot "@ArrayBufferByteLength" none;
    slot "@ViewedArrayBuffer" none;
    slot "@ByteOffset" none;
    slot "@ByteLength" none;
    slot "@ArrayLength" none;
    (* Gillian-only: marks environment records, which are objects *)
    slot "@er" (Bool false);
  ]

let slot_names = List.map (fun s -> s.name) slots
let is_slot_name n = List.mem n slot_names

let slot_default n =
  List.find_map (fun s -> if s.name = n then Some s.default else None) slots

(** {1 Actions and core predicates} *)

let get_slot = "GetSlot"
let set_slot = "SetSlot"
let a_slot = "Slot"

(** [SlotsDomain(l, D)]: every slot of [l] outside [D] holds its default *)
let a_slots_domain = "SlotsDomain"
