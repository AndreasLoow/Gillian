open JSILNames
open Gillian.Gil_syntax.Asrt

let points_to ~loc ~field ~value = CorePred (aCell, [ loc; field ], [ value ])
let metadata ~loc ~metadata = CorePred (aMetadata, [ loc ], [ metadata ])
let empty_fields ~loc ~domain = CorePred (aProps, [ loc; domain ], [])

let slots_domain ~loc ~domain =
  CorePred (JSCertInterface.a_slots_domain, [ loc; domain ], [])

(* The slot's name is both its index and its cell's first argument *)
let slot ~loc ~slot ~value =
  CorePred (JSCertInterface.a_slot, [ loc; slot; slot ], [ value ])
