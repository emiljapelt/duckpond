open Absyn
open Values


let builtin_int_add a b = match a,b with
| V_Int a, V_Int b -> V_Int (a+b)
| _ -> failwith "Builtin addition failed"

let builtin_int_mul a b = match a,b with
| V_Int a, V_Int b -> V_Int (a*b)
| _ -> failwith "Builtin multiply failed"

let builtin_int_sub a b = match a,b with
| V_Int a, V_Int b -> V_Int (a-b)
| _ -> failwith "Builtin subtract failed"

let builtin_int_eq a b = match a,b with
| V_Int a, V_Int b -> V_Bool (a=b)
| _ -> failwith "Builtin equal failed"

let builtin_int_gt a b = match a,b with
| V_Int a, V_Int b -> V_Bool (a>b)
| _ -> failwith "Builtin greater-than failed"


let builtin_binds = [
  ("+", (V_Builtin_binary builtin_int_add, T_Func(T_Int, T_Func(T_Int, T_Int))));
  ("*", (V_Builtin_binary builtin_int_mul, T_Func(T_Int, T_Func(T_Int, T_Int))));
  ("-", (V_Builtin_binary builtin_int_sub, T_Func(T_Int, T_Func(T_Int, T_Int))));
  ("=", (V_Builtin_binary builtin_int_eq, T_Func(T_Int, T_Func(T_Int, T_Bool))));
  (">", (V_Builtin_binary builtin_int_gt, T_Func(T_Int, T_Func(T_Int, T_Bool))));
]