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
  types : Type.t list option;
      (** The types of the values the slot may hold, those of its JSCert field,
          if it has one. Writing a value of another type is an error. *)
}

let slot ?jscert ?types name default = { name; jscert; default; types }

(* The fields of [object_new proto class] other than [proto] and [class],
   which [Alloc] does not take yet: until it does, they start as [null] and
   ["Object"] and the runtime sets them. *)
let slots : slot list =
  let none = Literal.Empty in
  let default = Literal.String "default" in
  let prim =
    Type.[ UndefinedType; NullType; BooleanType; NumberType; StringType ]
  in
  let value = Type.ObjectType :: prim in
  let tag = Type.[ StringType ] in
  let opt tys = Some (Type.EmptyType :: tys) in
  [
    slot "@proto" ~jscert:"object_proto_"
      ~types:Type.[ NullType; ObjectType ]
      Null;
    slot "@class" ~jscert:"object_class_" ~types:tag (String "Object");
    slot "@extensible" ~jscert:"object_extensible_"
      ~types:Type.[ BooleanType ]
      (Bool true);
    slot "@primitiveValue" ~jscert:"object_prim_value_" ?types:(opt prim) none;
    slot "@get" ~jscert:"object_get_" ~types:tag default;
    slot "@getOwnProperty" ~jscert:"object_get_own_prop_" ~types:tag default;
    slot "@getProperty" ~jscert:"object_get_prop_" ~types:tag default;
    slot "@put" ~jscert:"object_put_" ~types:tag default;
    slot "@canPut" ~jscert:"object_can_put_" ~types:tag default;
    slot "@hasProperty" ~jscert:"object_has_prop_" ~types:tag default;
    slot "@delete" ~jscert:"object_delete_" ~types:tag default;
    slot "@defaultValue" ~jscert:"object_default_value_" ~types:tag default;
    slot "@defineOwnProperty" ~jscert:"object_define_own_prop_" ~types:tag
      default;
    slot "@construct" ~jscert:"object_construct_" ?types:(opt tag) none;
    slot "@call" ~jscert:"object_call_" ?types:(opt tag) none;
    slot "@hasInstance" ~jscert:"object_has_instance_" ?types:(opt tag) none;
    slot "@scope" ~jscert:"object_scope_" ?types:(opt Type.[ ListType ]) none;
    slot "@formalParameters" ~jscert:"object_formal_parameters_"
      ?types:(opt Type.[ ListType ])
      none;
    slot "@code" ~jscert:"object_code_" ?types:(opt tag) none;
    slot "@targetFunction" ~jscert:"object_target_function_"
      ?types:(opt Type.[ ObjectType ])
      none;
    slot "@boundThis" ~jscert:"object_bound_this_" ?types:(opt value) none;
    slot "@boundArguments" ~jscert:"object_bound_args_"
      ?types:(opt Type.[ ListType ])
      none;
    slot "@parameterMap" ~jscert:"object_parameter_map_"
      ?types:(opt Type.[ ObjectType ])
      none;
    (* Gillian-only: ArrayBuffer, DataView and Uint8Array *)
    slot "@ArrayBufferData" none;
    slot "@ArrayBufferByteLength" none;
    slot "@ViewedArrayBuffer" none;
    slot "@ByteOffset" none;
    slot "@ByteLength" none;
    slot "@ArrayLength" none;
    (* Gillian-only: marks environment records, which are objects *)
    slot "@er" ~types:Type.[ BooleanType ] (Bool false);
  ]

let slot_names = List.map (fun s -> s.name) slots
let is_slot_name n = List.mem n slot_names

let slot_default n =
  List.find_map (fun s -> if s.name = n then Some s.default else None) slots

(** The types slot [n] may hold, if restricted *)
let slot_types n =
  Option.join
    (List.find_map (fun s -> if s.name = n then Some s.types else None) slots)

(** [SetSlot] checks the type of the value it writes. *)
let typed_store = "typed_store"

(** The [call] and [construct] tag of a user function, whose body is in [@code]:
    JSCert's [call_default] and [construct_default]. *)
let tag_default = "default"

(** {1 Built-in functions} *)

(** A built-in function's [@call] and [@construct] hold the procedures that
    implement it, which play the role of JSCert's [call_prealloc p] and
    [construct_prealloc p]. *)
type builtin = {
  prealloc : string;  (** The JSCert [prealloc], as a Rocq term. *)
  call : string option;  (** The procedure in [@call], if any. *)
  construct : string option;  (** The procedure in [@construct], if any. *)
}

let builtin prealloc call construct = { prealloc; call; construct }

(* Every [prealloc] of JSCert, in its order. *)
let builtins : builtin list =
  [
    builtin "prealloc_global" None None;
    builtin "prealloc_global_eval" (Some "ExecuteEval") None;
    builtin "prealloc_global_parse_int" (Some "Object_parseInt") None;
    builtin "prealloc_global_parse_float" (Some "Object_parseFloat") None;
    builtin "prealloc_global_is_finite" (Some "Object_isFinite") None;
    builtin "prealloc_global_is_nan" (Some "Object_isNan") None;
    builtin "prealloc_global_decode_uri" (Some "Object_decodeURI") None;
    builtin "prealloc_global_decode_uri_component"
      (Some "Object_decodeURIComponent") None;
    builtin "prealloc_global_encode_uri" (Some "Object_encodeURI") None;
    builtin "prealloc_global_encode_uri_component"
      (Some "Object_encodeURIComponent") None;
    builtin "prealloc_object" (Some "Object_call") (Some "Object_construct");
    builtin "prealloc_object_get_proto_of" (Some "Object_getPrototypeOf") None;
    builtin "prealloc_object_get_own_prop_descriptor"
      (Some "Object_getOwnPropertyDescriptor") None;
    builtin "prealloc_object_get_own_prop_name"
      (Some "Object_getOwnPropertyNames") None;
    builtin "prealloc_object_create" (Some "Object_create") None;
    builtin "prealloc_object_define_prop" (Some "Object_defineProperty") None;
    builtin "prealloc_object_define_props" (Some "Object_defineProperties") None;
    builtin "prealloc_object_seal" (Some "Object_seal") None;
    builtin "prealloc_object_freeze" (Some "Object_freeze") None;
    builtin "prealloc_object_prevent_extensions"
      (Some "Object_preventExtensions") None;
    builtin "prealloc_object_is_sealed" (Some "Object_isSealed") None;
    builtin "prealloc_object_is_frozen" (Some "Object_isFrozen") None;
    builtin "prealloc_object_is_extensible" (Some "Object_isExtensible") None;
    builtin "prealloc_object_keys" (Some "Object_keys") None;
    builtin "prealloc_object_keys_call" None None;
    builtin "prealloc_object_proto" None None;
    builtin "prealloc_object_proto_to_string" (Some "OP_toString") None;
    builtin "prealloc_object_proto_value_of" (Some "OP_valueOf") None;
    builtin "prealloc_object_proto_has_own_prop" (Some "OP_hasOwnProperty") None;
    builtin "prealloc_object_proto_is_prototype_of" (Some "OP_isPrototypeOf")
      None;
    builtin "prealloc_object_proto_prop_is_enumerable"
      (Some "OP_propertyIsEnumerable") None;
    builtin "prealloc_function" (Some "Function_call")
      (Some "Function_construct");
    builtin "prealloc_function_proto" (Some "FP_default") None;
    builtin "prealloc_function_proto_to_string" (Some "FP_toString") None;
    builtin "prealloc_function_proto_apply" (Some "FP_apply") None;
    builtin "prealloc_function_proto_call" (Some "FP_call") None;
    builtin "prealloc_function_proto_bind" (Some "FP_bind") None;
    builtin "prealloc_bool" (Some "Boolean_call") (Some "Boolean_construct");
    builtin "prealloc_bool_proto" None None;
    builtin "prealloc_bool_proto_to_string" (Some "BP_toString") None;
    builtin "prealloc_bool_proto_value_of" (Some "BP_valueOf") None;
    builtin "prealloc_number" (Some "Number_call") (Some "Number_construct");
    builtin "prealloc_number_proto" None None;
    builtin "prealloc_number_proto_to_string" (Some "NP_toString") None;
    builtin "prealloc_number_proto_value_of" (Some "NP_valueOf") None;
    builtin "prealloc_number_proto_to_fixed" (Some "NP_toFixed") None;
    builtin "prealloc_number_proto_to_exponential" (Some "NP_toExponential")
      None;
    builtin "prealloc_number_proto_to_precision" (Some "NP_toPrecision") None;
    builtin "prealloc_array" (Some "Array_call") (Some "Array_construct");
    builtin "prealloc_array_is_array" (Some "Array_isArray") None;
    builtin "prealloc_array_proto" None None;
    builtin "prealloc_array_proto_to_string" (Some "AP_toString") None;
    builtin "prealloc_array_proto_join" (Some "AP_join") None;
    builtin "prealloc_array_proto_pop" (Some "AP_pop") None;
    builtin "prealloc_array_proto_push" (Some "AP_push") None;
    builtin "prealloc_string" (Some "String_call") (Some "String_construct");
    builtin "prealloc_string_proto" None None;
    builtin "prealloc_string_proto_to_string" (Some "SP_toString") None;
    builtin "prealloc_string_proto_value_of" (Some "SP_valueOf") None;
    builtin "prealloc_string_proto_char_at" (Some "SP_charAt") None;
    builtin "prealloc_string_proto_char_code_at" (Some "SP_charCodeAt") None;
    builtin "prealloc_math" None None;
    builtin "prealloc_mathop mathop_abs" (Some "M_abs") None;
    builtin "prealloc_date" (Some "Date_call") (Some "Date_construct");
    builtin "prealloc_regexp" (Some "RegExp_call") (Some "RegExp_construct");
    builtin "prealloc_error" (Some "Error_call") (Some "Error_construct");
    builtin "prealloc_error_proto" None None;
    builtin "prealloc_native_error native_error_eval" (Some "EvalError_call")
      (Some "EvalError_construct");
    builtin "prealloc_native_error native_error_range" (Some "RangeError_call")
      (Some "RangeError_construct");
    builtin "prealloc_native_error native_error_ref"
      (Some "ReferenceError_call") (Some "ReferenceError_construct");
    builtin "prealloc_native_error native_error_syntax"
      (Some "SyntaxError_call") (Some "SyntaxError_construct");
    builtin "prealloc_native_error native_error_type" (Some "TypeError_call")
      (Some "TypeError_construct");
    builtin "prealloc_native_error native_error_uri" (Some "URIError_call")
      (Some "URIError_construct");
    builtin "prealloc_native_error_proto native_error_eval" None None;
    builtin "prealloc_native_error_proto native_error_range" None None;
    builtin "prealloc_native_error_proto native_error_ref" None None;
    builtin "prealloc_native_error_proto native_error_syntax" None None;
    builtin "prealloc_native_error_proto native_error_type" None None;
    builtin "prealloc_native_error_proto native_error_uri" None None;
    builtin "prealloc_error_proto_to_string" (Some "EP_toString") None;
    builtin "prealloc_throw_type_error" (Some "ThrowTypeError") None;
    builtin "prealloc_json" None None;
  ]

(** The value of [@call] for [call_prealloc p], and of [@construct] for
    [construct_prealloc p]. A [prealloc] that Gillian does not implement is
    named by itself, which is no procedure's name. *)
let call_id b = Option.value ~default:b.prealloc b.call

let construct_id b = Option.value ~default:b.prealloc b.construct

(** {1 Actions and core predicates} *)

let get_slot = "GetSlot"
let set_slot = "SetSlot"
let a_slot = "Slot"

(** [SlotsDomain(l, D)]: every slot of [l] outside [D] holds its default *)
let a_slots_domain = "SlotsDomain"
