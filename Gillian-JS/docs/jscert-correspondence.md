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
the CSE model to JSCert's object heap. Each action is a JSCert core heap
operation, so the action relation is equality on the encoded arguments and
results.

Status markers:
- **now:** what Gillian-JS does today;
- **target:** what the plan moves it to.

## 1. Combinator stack

| Level | Gillian-JS (OCaml) | CSE (Rocq) | JSCert |
|---|---|---|---|
| Heap | `OpenPMap(LocationIndex)` | `map_mm Loc` | `Heap.heap object_loc object` |
| Object | product with alloc-init (target) | `prod_mm` + `cmm_init` | `object` |
| Properties | `PMap(StringIndex)` with domain set, over `DynCell` (now) | `js_map_mm DynCell` | `object_properties_` : `Heap.heap prop_name attributes` |
| Slots | static-domain `PMap(SlotName)` over `Exclusive` (target) | `dom_map_mm SlotName ex_mm` | the other 23 fields of `object` |

**Now:**
- an object is `Product(PMap(StringIndex, DynCell), Agreement)`;
- the attributes and internal fields live in a separate metadata object, which
  the `Agreement` side points to;
- `MoveInToOut` makes the domain an in of `Props`, as in the JSIL logic.

## 2. Actions

| Action (ins → outs) | JSCert | CSE path | Miss / error |
|---|---|---|---|
| `Alloc(proto, class) → l` | `object_alloc S (object_new proto class)` | `map_mm` new → `Object.cmm_init [proto; class]` | never misses |
| `GetProp(l, p) → attrs \| none` | `Heap.read_option (object_properties_ O) p` | heap → props → `DynCell` `lookup` | miss: `l` or `p` not owned |
| `SetProp(l, p, attrs)` | `object_set_property` | … → `DynCell` `mutate` | miss: as `GetProp`; error: `attrs` ill-formed |
| `DelProp(l, p)` | `object_rem_property` | … → `DynCell` `delete` | miss: as `GetProp` |
| `GetKeys(l) → [p…]` | the domain of `object_properties_` (as a list, up to permutation) | `JS_Map` keys action (new) | miss: the domain or a cell not owned |
| `GetSlot(l, f) → v` | the field `f` of the object at `l` | heap → slots → `ex_mm` `lookup` | miss: slot not owned; error: unknown `f` |
| `SetSlot(l, f, v)` | `object_write` with field `f` updated | … → `ex_mm` `mutate` | as `GetSlot`; error: `v` ill-typed for `f` |

- JSCert has no object deletion. Gillian's `DeleteObject` is kept only for the
  compiler's cleanup, and is outside the simulation.
- Misses are Gillian's `can_fix` errors, and CSE's `miss` outcomes. Errors are
  the remaining ones, CSE's `err`.

## 3. Core predicates

| Predicate | Meaning | CSE resource |
|---|---|---|
| `Prop(l, p; attrs)` (now `Cell`) | the property `p` of `l`; `none` means owned and absent | `DynCell` `rm_cell` |
| `Props(l, D)` | every property of `l` outside `D` is owned and absent | `JS_Map` domain (`pointsto_undef_vs_dom`) |
| `Slot(l, f; v)` | the slot `f` of `l` | `ex_mm` cell |

- `Props` takes the domain as an in on both sides.
- `DataProp`, `AccessorProp`, `JSObject`, `JSObjGeneral` and so on become
  logic-level predicates over these, keeping their names.

**`DynCell`.** Gillian's `DynCell` (`GillianCore/combinators/DynCell.ml`) has
the actions `lookup`, `mutate` and `delete` and the single predicate `dyn`,
like CSE's `act_lookup`, `act_mutate`, `act_delete` and `rm_cell`.
- An absent cell holds `none` on the Gillian side, and is `DC_absent` on the
  CSE side, which reads back as `VUndef`.
- Writing `none` is an error on the Gillian side; CSE's `mutate` errors on any
  value outside the cell's type.
- CSE also has the resources `rm_val` and `rm_absent`, one per state. `rm_cell`
  is their union for cells that never hold `VUndef`.

## 4. Attributes

A property's attributes are one value, so one cell holds the whole JSCert
`attributes` record.

| JSCert | Gillian-JS | CSE |
|---|---|---|
| `attributes_data_of {value; writable; enumerable; configurable}` | `{{ "d", v, w, e, c }}` | `VList [VString "d"; v; VBool w; VBool e; VBool c]` |
| `attributes_accessor_of {get; set; enumerable; configurable}` | `{{ "a", g, s, e, c }}` | `VList [VString "a"; g; s; VBool e; VBool c]` |
| no property | `none` | `VUndef` (the `DynCell` absent state) |

## 5. Slots

The slot names are the JSCert field names. `Alloc(proto, class)` gives every
slot the default from `object_new proto class`. An option field's `None` is
encoded as `empty` (see §6).

| JSCert field | Gillian slot (now → target) | Values | `object_new` default |
|---|---|---|---|
| `object_proto_` | `@proto` | `null` or a location | `proto` |
| `object_class_` | `@class` | string | `class` |
| `object_extensible_` | `@extensible` | bool | `true` |
| `object_prim_value_` | `@primitiveValue` | `empty` or a value | `empty` |
| `object_get_` | `@get` (new) | `"default"`, `"function"`, `"args_obj"` | `"default"` |
| `object_get_own_prop_` | `@getOwnProperty` (new) | `"default"`, `"args_obj"`, `"string"` | `"default"` |
| `object_get_prop_` | `@getProperty` (new) | `"default"` | `"default"` |
| `object_put_` | `@put` (new) | `"default"` | `"default"` |
| `object_can_put_` | `@canPut` (new) | `"default"` | `"default"` |
| `object_has_prop_` | `@hasProperty` (new) | `"default"` | `"default"` |
| `object_delete_` | `@delete` (new) | `"default"`, `"args_obj"` | `"default"` |
| `object_default_value_` | `@defaultValue` (new) | `"default"` | `"default"` |
| `object_define_own_prop_` | `@defineOwnProperty` (new) | `"default"`, `"array"`, `"args_obj"` | `"default"` |
| `object_construct_` | `@construct` | `empty`, `"default"`, `"after_bind"` or a prealloc name | `empty` |
| `object_call_` | `@call` | `empty`, `"default"`, `"after_bind"` or a prealloc name | `empty` |
| `object_has_instance_` | `@hasInstance` | `empty`, `"function"`, `"after_bind"` | `empty` |
| `object_scope_` | `@scope` | see D3 | `empty` |
| `object_formal_parameters_` | `@formalParameters` | `empty` or a list of strings | `empty` |
| `object_code_` | `@code` (new) | `empty` or a function id; see D3 | `empty` |
| `object_target_function_` | `@targetFunction` | `empty` or a location | `empty` |
| `object_bound_this_` | `@boundThis` | `empty` or a value | `empty` |
| `object_bound_args_` | `@boundArguments` | `empty` or a list of values | `empty` |
| `object_parameter_map_` | `@parameterMap` (new) | `empty` or a location | `empty` |

**`@call` and `@construct` today hold a JSIL procedure id.** In the target they
hold JSCert's tag, and a user function's procedure id moves to `@code`. The
runtime then dispatches on the tag.

**Gillian-only slots.** Gillian-JS's `ArrayBuffer`, `DataView` and `Uint8Array`
keep internal fields that JSCert does not have:
- `@ArrayBufferData` and `@ArrayBufferByteLength`;
- `@ViewedArrayBuffer`, `@ByteOffset`, `@ByteLength` and `@ArrayLength`.

They are slots on both sides too. The simulation relates only states in which
they are all `empty`, so the AWS case study, which uses them, is verified but
lies outside the simulated fragment.

## 6. Values

| JSCert | Gillian-JS | CSE |
|---|---|---|
| `prim_undef` | `undefined` | `VUndef` |
| `prim_null` | `null` | `VNull` |
| `prim_bool b` | `b` | `VBool b` |
| `prim_string s` | `s` | `VString s` |
| `prim_number n` | `n` (float) | **D4** |
| `object_loc_normal n` | a fresh location | `VNat n` |
| `object_loc_prealloc p` | a named location (`$lg`, `$lobj_proto`, …) | **D4** |
| option `None` | `empty` | **D4** |

## 7. Open decisions

- **D3: `code` and `scope`.**
  - `code`: a function id is related to a JSCert `funcbody` through a fixed code
    table, a parameter of the JSCert wrapper.
  - `scope`: while environment records remain `@er` objects, `scope` is outside
    the related fragment.
- **D4: CSE values for numbers, preallocated locations and `None`.** Either:
  - add constructors to CSE's core value type; or
  - encode them with existing constructors. For example:
    - `pVADT "JSNum" "num" [pVInt bits]` for a number;
    - `pVADT "JSLoc" name []` for a preallocated location;
    - `pVADT "JS" "empty" []` for `None`.
