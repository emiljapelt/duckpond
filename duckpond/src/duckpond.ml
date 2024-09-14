open Duckpondlib.Errors
open Duckpondlib.Exceptions
open Duckpondlib.Io
open Duckpondlib.Absyn
open Duckpondlib.Flags
open Duckpondlib.Optimize
open Duckpondlib.Typing
open Duckpondlib.Defaults
open Duckpondlib.Values
open Duckpondlib.Interpreter
open Duckpondlib.Inference



let () = Printexc.record_backtrace true
let nothing a = a

let run () = 
  try 
    let input = resolve_arguments () in
    let error_printer = create_error_printer input in

    let defaults = StringMap.of_list builtin_binds in
    let term = 
      read_input input error_printer |>
      type_alias_substitute StringMap.empty |>
      (if flags.optimize then optimize_term else nothing) in
    let (inf_ty,_,_) = infer_term term {empty_inference_info with type_mapping = (StringMap.map snd defaults)} in
    let () = Printf.printf "infered: %s\n" (print_type inf_ty); exit 0 in
    let ty = type_term (StringMap.map snd defaults) term in
    let v = eval_term defaults term in

    Printf.printf "%s : %s\n" (print_value v) (print_type ty)

  with 
  | Failure msg -> Printf.printf "%s\n" msg
  | Problem p -> ()

let () = run ()