(* The table relating JSCert's preallocated functions to the runtime's
   procedures must be injective on each side, distinct from the other tags,
   and name the procedures the initial heap installs. *)

module JSCI = Javert_utils.JSCertInterface

(* The initial heap installs each built-in's procedures *)
let init = Option.get (Javert_utils.Runtime_files.read "Init.jsil")

let installed name =
  let re = Str.regexp_string ("\"" ^ name ^ "\"") in
  try
    ignore (Str.search_forward re init 0);
    true
  with Not_found -> false

let injective name ids () =
  let sorted = List.sort_uniq String.compare ids in
  Alcotest.(check int)
    (name ^ " ids are distinct")
    (List.length ids) (List.length sorted);
  List.iter
    (fun id ->
      if id = JSCI.tag_default || id = "after_bind" then
        Alcotest.failf "%s id %s is a tag" name id)
    ids

let procedures_installed () =
  List.iter
    (fun (b : JSCI.builtin) ->
      List.iter
        (fun p ->
          if not (installed p) then
            Alcotest.failf "%s: %s is not installed" b.prealloc p)
        (Option.to_list b.call @ Option.to_list b.construct))
    JSCI.builtins

(* A slot's default must be a value it may hold. *)
let defaults_typed () =
  List.iter
    (fun (sl : JSCI.slot) ->
      match sl.types with
      | Some tys when not (List.mem (Gil_syntax.Literal.type_of sl.default) tys)
        -> Alcotest.failf "%s: default of the wrong type" sl.name
      | _ -> ())
    JSCI.slots

let () =
  Alcotest.run "jscert_interface"
    [
      ("slots", [ Alcotest.test_case "defaults typed" `Quick defaults_typed ]);
      ( "builtins",
        [
          Alcotest.test_case "82 preallocs" `Quick (fun () ->
              Alcotest.(check int) "count" 82 (List.length JSCI.builtins));
          Alcotest.test_case "call injective" `Quick
            (injective "call" (List.map JSCI.call_id JSCI.builtins));
          Alcotest.test_case "construct injective" `Quick
            (injective "construct" (List.map JSCI.construct_id JSCI.builtins));
          Alcotest.test_case "procedures installed" `Quick procedures_installed;
        ] );
    ]
