# Gillian-JS ↔ CSE ↔ JSCert correspondence

This is a living table. It is updated whenever a memory state, action or
predicate changes on either side.

- **Gillian-JS:** the OCaml memory model in `Gillian-JS/lib/Memory/`, built
  from `Gillian.Combinators`.
- **CSE:** the Rocq memory model on `GillianPlatform/CSE`, branch `cse-tree`,
  theory `js_theories/`.
- **JSCert:** `AndreasLoow/jscert`, mainly `coq/JsSyntax.v` and `coq/JsCommon.v`.

The two memory models are built from combinators that correspond one to one,
and they expose the same actions and core predicates. The simulation relates
the CSE model to JSCert's object heap (`js_theories/JsCert_Heap_Sim.v`): it
holds in both directions, allocation excluded from the CSE-to-JSCert one, and
it is lifted through CSE's whole-memory transfer theorems.

## 1. Combinator stack

| Level | Gillian-JS (OCaml) | CSE (Rocq) | JSCert |
|---|---|---|---|
| Heap | `OpenPMap(LocationIndex)` | `map_mm Nat` (`JS_Object.js_heap`) | `Heap.heap object_loc object` |
| Object | `Product` of properties and slots | `prod_mm` (`js_object`), initialising both sides | `object` |
| Properties | `PMap(StringIndex)` with domain set, over `DynCell` | `js_map_mm` over `DynCell` (`js_props`) | `object_properties_` |
| Slots | `PMap(SlotIndex)` with domain set, over `Exclusive` | `slot_map_mm` (`js_slots`) | the other 23 fields of `object` |

- A property outside the domain is absent; a slot outside the domain is in its
  default state.
- Allocation gives an object with every property absent and every slot in its
  default state, which is JSCert's `object_new null "Object"`.

On the CSE side every combinator in the stack is proven sound, concrete and
symbolic side alike. The property map owns each property whole: its cells
never compose (`JS_Map.Exclusive_Cells`, which `DynCell` satisfies), as on the
Gillian side, where a `PMap` entry is a single `DynCell`.

**`DynCell`** (`GillianCore/combinators/DynCell.ml`, `js_theories/DynCell.v`).
- Actions `lookup`, `mutate`, `delete`; predicate `dyn`, CSE resource `rm_cell`.
- An absent cell holds `none` on the Gillian side and is `DC_absent` on the CSE
  side, which reads back as `VUndef`.

**Slots** (`Slots` in `Gillian-JS/lib/Memory/JSILMemory.ml`, `js_theories/SlotMap.v`).
- Actions `load [k]`, `store [k; v]`; predicate `ex [k]; [v]`, CSE resource
  `rm_slot`.
- A slot outside the domain set holds its own default (`SlotIndex`'s
  `default_instantiation`, `dom_default` in CSE). The domain is exclusive on
  both sides, and its CSE resource `rm_slots_dom` owns every slot outside the
  set as well.
- Reading a slot outside the domain set leaves the state unchanged; writing
  it, or consuming its `ex`, brings it into the map and its name into the
  domain set.
- A key that is not a literal is resolved by branching over the slot names.
- A write of a value outside the slot's type errs on both sides. The Gillian
  side (`SetSlot` is `TypedStore`, `JSCertInterface.slot_types`) checks the
  GIL type of the value, e.g. a string for a method tag; the CSE side checks
  the field's codec, which is finer, e.g. one of the tags JSCert has. The
  Gillian-only slots take any value.

**Concrete memory** (`Concrete` in `Gillian-JS/lib/Memory/JSILMemory.ml`,
`GillianCore/combinators/CCombinators.ml`).
- Built from concrete counterparts of the same combinators, which follow the
  concrete (`cmm_*`) side of the CSE ones: `Heap` (`map_mm`, allocating with
  `CE_new`), `Product` (`prod_mm`), `TotalMap` over `DynCell` with `Keys`
  (`js_map_mm`, `keys_mm`), and `TotalMap` over `Exclusive` (`slot_map_mm`).
- The whole concrete memory owns every property and slot of an object, absent
  or default until written, so it needs no domain set (CSE's concrete slot map
  keeps its domain token only for frames). A missing resource is a miss
  and a malformed action an error, both of which fail concrete execution.

## 2. Actions

| Action (ins → outs) | Path | JSCert |
|---|---|---|
| `Alloc(l?) → l` | heap alloc → object init | `object_alloc S (object_new null "Object")` |
| `GetCell(l, p) → attrs \| none` | heap → properties → `DynCell lookup` | `Heap.read_option (object_properties_ O) p` |
| `SetCell(l, p, attrs)` | … → `DynCell mutate` | `object_set_property` |
| `DeleteCell(l, p)` | … → `DynCell delete` | `object_rem_property` |
| `GetAllProps(l) → [p…]` | properties domain; CSE: `keys_mm`'s `act_keys` (`js_theories/Keys.v`), which symbolically answers fresh variables that are a permutation of the keys holding values, when the domain names exactly the map's properties | the names of the properties of `object_properties_`, once each, in any order |
| `GetSlot(l, f) → v` | heap → slots → `Exclusive load` at `f` | the field `f` of the object at `l` |
| `SetSlot(l, f, v)` | … → `Exclusive store` at `f` | `object_write` with field `f` updated |

- In JSIL, `x := slot(l, f)` and `slot(l, f) := v` compile to `GetSlot` and
  `SetSlot`.
- `DeleteObject` is only used for clean-up, and is outside the simulation.

## 3. Core predicates

| Predicate | Meaning | CSE resource |
|---|---|---|
| `Cell(l, p; attrs)` | the property `p` of `l`; `none` means owned and absent | `DynCell.rm_cell` |
| `Props(l, D)` | every property of `l` outside `D` is owned and absent | properties domain |
| `Slot(l, f; v)` | the slot `f` of `l` holds `v` | `SlotMap.rm_slot` |
| `SlotsDomain(l, D)` | the domain, and every slot of `l` outside `D`, owned and default | `SlotMap.rm_slots_dom` |

In JSIL logic these are `((l, p) -> attrs)`, `empty_fields(l : D)`,
`Slot(l, f, v)` and `slots_domain(l : D)`.

## 4. Attributes

| JSCert | Gillian-JS | CSE |
|---|---|---|
| `attributes_data_of {value; writable; enumerable; configurable}` | `{{ "d", v, w, e, c }}` | `VList [VString "d"; v; VBool w; VBool e; VBool c]` |
| `attributes_accessor_of {get; set; enumerable; configurable}` | `{{ "a", g, s, e, c }}` | `VList [VString "a"; g; s; VBool e; VBool c]` |
| no property | `none` | `VUndef` |

## 5. Slots

See `Gillian-JS/lib/utils/JSCertInterface.ml` for the table. On the CSE side,
`js_theories/JS_Fields.v` gives each field a codec between its JSCert type and
values; the slot table, defaults and types included, is derived from it. `@proto` and
`@class` default to `null` and `"Object"`, as in `object_new null "Object"`;
an option field defaults to `empty`.

| JSCert field | Gillian slot | Default |
|---|---|---|
| `object_proto_` | `@proto` | `null` |
| `object_class_` | `@class` | `"Object"` |
| `object_extensible_` | `@extensible` | `true` |
| `object_prim_value_` | `@primitiveValue` | `empty` |
| `object_get_` … `object_define_own_prop_` (9 tags) | `@get`, `@getOwnProperty`, `@getProperty`, `@put`, `@canPut`, `@hasProperty`, `@delete`, `@defaultValue`, `@defineOwnProperty` | `"default"` |
| `object_construct_`, `object_call_`, `object_has_instance_` | `@construct`, `@call`, `@hasInstance` | `empty` |
| `object_scope_`, `object_formal_parameters_`, `object_code_` | `@scope`, `@formalParameters`, `@code` | `empty` |
| `object_target_function_`, `object_bound_this_`, `object_bound_args_`, `object_parameter_map_` | `@targetFunction`, `@boundThis`, `@boundArguments`, `@parameterMap` | `empty` |

Gillian-only slots, outside the simulated fragment (they must be default
there):
- `@ArrayBufferData`, `@ArrayBufferByteLength`, `@ViewedArrayBuffer`,
  `@ByteOffset`, `@ByteLength`, `@ArrayLength` (ArrayBuffer, DataView,
  Uint8Array);
- `@er`, which marks environment records (decision 2: they are still
  objects).

**Functions and method tags (A7).**
- A user function has `@call` and `@construct` set to `"default"`
  (`call_default`, `construct_default`), its body's procedure id in `@code`,
  its parameters in `@formalParameters`, and `@get` and `@hasInstance` set to
  `"function"`, as JSCert's 13.2 does. Calls resolve `"default"` to `@code`.
- Arrays have `@defineOwnProperty` set to `"array"`.
- Arguments objects keep the default methods: the code is strict, and
  JSCert's `args_obj` variants are for non-strict arguments objects.

- A built-in function has the procedures implementing it in `@call` and
  `@construct`. These play the role of JSCert's `call_prealloc p` and
  `construct_prealloc p`: `builtins` in `JSCertInterface.ml` gives the
  procedures for each of JSCert's 82 `prealloc`s, and a `prealloc` that Gillian
  does not implement is named by itself. On the CSE side the names are the
  parameter `JS_Slots.Prealloc_Table` (injective, and distinct from
  `"default"` and `"after_bind"`), which this table instantiates;
  `Gillian-JS/test` checks those properties and that the initial heap
  installs these procedures. Each native error has its own construct procedure
  (`EvalError_construct`, …), as JSCert distinguishes them. Built-ins that
  JSCert lacks (ES6+ ones, `Date`, `Math` beyond `abs`, …) are outside the
  simulated fragment.

**Still to align with JSCert:**
- `@scope` holds a list of environment-record objects (decision 2).

## 6. Values

`js_theories/JS_Values.v`.

| JSCert | Gillian-JS | CSE |
|---|---|---|
| `prim_undef` | `undefined` | `VUndef` |
| `prim_null` | `null` | `VNull` |
| `prim_bool b` | `b` | `VBool b` |
| `prim_string s` | `s` | `VString s` |
| `prim_number n` | `n` | `VNum n`: the ADT value `JSNum (bits_of_b64 n)` |
| an object location | a location | `VNat (object_loc_to_nat l)`: the 82 built-in locations first, then ordinary ones |
| option `None` | `empty` | `VEmpty`: the ADT value `JSEmpty` |

The ADT constructors are a parameter (`JS_ADTs`), since CSE's ADT environment
`Aenv` is a global parameter (D4).

## 7. Open decisions

- **D3: `code` and `scope`.** `code` relates a function id to a JSCert
  `funcbody` through a fixed code table (`JS_Slots.Code_Table`). `scope` is a
  list of environment locations on the CSE side, as in JSCert; the Gillian
  runtime does not use JSCert's environment records yet.

## 8. The JSCert heap as a memory model

`js_theories/Wrapper_JsCert.v` gives each action of the CSE heap its JSCert
meaning:

| Action | JSCert |
|---|---|
| `alloc` | `object_alloc S (object_new null "Object")` |
| property `lookup` | `Heap.read_option` of the object's properties, `undefined` if absent |
| property `mutate` | `object_write` with `Heap.write` of the properties |
| property `delete` | `object_write` with `Heap.rem` of the properties |
| property `keys` | the names bound in the properties, once each, in any order |
| slot `lookup` | the field, encoded |
| slot `mutate` | the field, decoded and written; a value of the wrong type errs |

Any other input errs. The relation maps every location to the encoding of the
object there: every property owned, every slot owned, and the domain.
