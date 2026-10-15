module CState = Test262_outcome.State
module JSCI = Javert_utils.JSCertInterface

let get_slot cstate loc slot =
  let act_ret =
    CState.execute_action JSCI.get_slot cstate
      [
        CState.eval_expr cstate (Lit loc);
        CState.eval_expr cstate (Lit (String slot));
      ]
  in
  try
    match act_ret with
    | [ Ok (_, [ _; _; v ]) ] -> Some v
    | _ -> None
  with _ -> None

let get_cell cstate loc prop =
  let act_ret =
    CState.execute_action JSILNames.getCell cstate
      [ CState.eval_expr cstate (Lit loc); CState.eval_expr cstate (Lit prop) ]
  in
  try
    match act_ret with
    | [ Ok (_, [ _; _; cell ]) ] -> Some cell
    | _ -> None
  with _ -> None

let is_test262_error ret_val ret_state =
  let open Gil_syntax.Literal in
  let constructor_name = String "constructor" in
  let get_constructor_loc = function
    | LList [ String "d"; Loc fobj; _; _; _ ] -> Some (Loc fobj)
    | _ -> None
  in
  let ( let* ) = Option.bind in
  (* A user function's body is in @code, its @construct being the default *)
  let body f =
    match get_slot ret_state f "@construct" with
    | Some (String t) when t = JSCI.tag_default -> get_slot ret_state f "@code"
    | c -> c
  in
  let final_proto =
    let* proto = get_slot ret_state ret_val "@proto" in
    let* constructor = get_cell ret_state proto constructor_name in
    let* cloc = get_constructor_loc constructor in
    body cloc
  in
  match final_proto with
  | Some (String constructor)
    when String.length constructor >= 12
         && String.sub constructor 0 12 = "Test262Error" -> true
  | _ -> false

let error_has_proto str ret_val ret_state =
  let open Gil_syntax.Literal in
  match get_slot ret_state ret_val "@proto" with
  | Some (Loc s) when String.equal s str -> true
  | _ -> false

let is_syntax_error = error_has_proto "$lserr_proto"
let is_ref_error = error_has_proto "$lrferr"

let parsing_failure_is_jsparser
    ({ additional_data; _ } : Utils.Gillian_result.Error.compilation_error) =
  match additional_data with
  | Some (`Assoc a) -> (
      match List.assoc_opt "is_parser_error" a with
      | Some (`Bool true) -> true
      | _ -> false)
  | _ -> false
