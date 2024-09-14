module StringMap = Map.Make(String)

type typ = 
  | T_Unit
  | T_Bool
  | T_Int
  | T_String
  | T_Fix of string * typ
  | T_Func of typ * typ
  | T_Object of (typ StringMap.t)
  | T_Alias of string
  | T_Tuple of typ * typ
  | T_Alts of typ list
  | T_NameBind of string * typ
  | T_Name of string
  | T_Addition of typ * typ
  | T_Poly of string

type term =
  | Unit
  | Bool of bool
  | Int of int
  | String of string
  | Tuple of term * term
  | Name of string
  | Func of string * typ option * term
  | App of term * term
  | Object of (typ option * term) StringMap.t
  | With of term * (typ option * term) StringMap.t
  | Access of term * string 
  | Bind of bool * string * typ option * term * term
  | TypeAlias of string * typ * term
  | WhenIs of term * ((string option * pattern) * term) list

and pattern =
  | P_Type of typ
  | P_Int of int
  | P_String of string
  | P_Bool of bool
  | P_Tuple of pattern * pattern
  | P_Any

let rec print_type t : string = match t with
  | T_Unit -> "unit"
  | T_Bool -> "bool"
  | T_Int -> "int"
  | T_String -> "string"
  | T_Fix(n,t) -> "fix "^n^"."^print_type t
  | T_Func(t0,t1) -> "("^(print_type t0)^" -> "^(print_type t1)^")"
  | T_Object c -> "{"^(StringMap.to_list c |> List.map (fun (n, t) -> n ^": "^print_type t)|> String.concat ", ")^"}"
  | T_Alias n -> n
  | T_Tuple(t0,t1) -> "("^print_type t0^","^print_type t1^")"
  | T_Alts tys -> "("^(List.map print_type tys |> String.concat " | ")^")"
  | T_Name n -> n
  | T_NameBind(n,ty) -> "("^n^": "^print_type ty^")"
  | T_Addition(ty0,ty1) -> "("^print_type ty0^" + "^print_type ty1^")"
  | T_Poly n -> n

