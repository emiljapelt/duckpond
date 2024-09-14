
open Absyn
module StringMap = Map.Make(String)

type value =
  | V_Unit
  | V_Bool of bool
  | V_Int of int
  | V_String of string
  | V_Tuple of value * value
  | V_Closure of string * typ * (value * typ) StringMap.t * term
  | V_Object of (typ * value) StringMap.t
  | V_Term of term
  | V_Builtin_unary of (value -> value)
  | V_Builtin_binary of (value -> value -> value)

let rec print_value v = match v with
  | V_Unit -> "()"
  | V_Bool b -> string_of_bool b
  | V_Int i -> string_of_int i
  | V_String s -> "\""^s^"\""
  | V_Tuple(v0,v1) -> "("^print_value v0^","^print_value v1^")"
  | V_Object c -> "{"^(StringMap.to_list c |> List.map (fun (n, (_,t)) -> n ^" = "^print_value t)|> String.concat ", ")^"}"
  | V_Term _ -> "<Term>"
  | V_Closure _ -> "<Closure>"
  | V_Builtin_unary _
  | V_Builtin_binary _ -> "<Builtin>"