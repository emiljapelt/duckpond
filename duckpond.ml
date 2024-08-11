
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

type term =
  | Unit
  | Bool of bool
  | Int of int
  | String of string
  | Tuple of term * term
  | Name of string
  | Func of string * typ * term
  | App of term * term
  | Object of (typ * term) StringMap.t
  | With of term * (typ * term) StringMap.t
  | Access of term * string 
  | Bind of string * typ * term * term
  | TypeAlias of string * typ * term
  | WhenIs of term * ((string option * pattern) * term) list

and pattern =
  | P_Type of typ
  | P_Int of int
  | P_String of string
  | P_Bool of bool
  | P_Tuple of pattern * pattern
  | P_Any

type value =
  | V_Unit
  | V_Bool of bool
  | V_Int of int
  | V_String of string
  | V_Tuple of value * value
  | V_Func of (value -> value)
  | V_Object of (typ * value) StringMap.t

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

let rec print_value v = match v with
  | V_Unit -> "()"
  | V_Bool b -> string_of_bool b
  | V_Int i -> string_of_int i
  | V_String s -> "\""^s^"\""
  | V_Tuple(v0,v1) -> "("^print_value v0^","^print_value v0^")"
  | V_Func _ -> "<Func>"
  | V_Object c -> "{"^(StringMap.to_list c |> List.map (fun (n, (_,t)) -> n ^" = "^print_value t)|> String.concat ", ")^"}"

let rec type_match type_target typ = match simplify_type type_target, simplify_type typ with
  | T_NameBind(_,ty), t -> type_match ty t
  | T_Unit, T_Unit
  | T_Int, T_Int
  | T_Bool, T_Bool
  | T_String, T_String -> true
  | T_Func(tt0,tt1), T_Func(t0,t1) -> type_match tt0 t0 && type_match tt1 t1
  | T_Object c0, T_Object c1 -> StringMap.for_all (fun n t -> match StringMap.find_opt n c1 with | None -> false | Some t' -> type_match t t') c0
  | T_Alts ts0, T_Alts ts1 -> List.for_all (fun ty -> List.mem ty ts1) ts0 (*List.combine ts0 ts1 |> List.for_all (fun (t0,t1) -> type_match t0 t1)*)
  | T_Alts ts, t -> List.exists (fun at -> type_match at t) ts
  | _ -> false

and type_equal t0 t1 = match simplify_type t1, simplify_type t0 with
  | T_NameBind(_,ty), t -> type_equal ty t
  | T_Unit, T_Unit
  | T_Int, T_Int
  | T_String, T_String -> true
  | T_Func(t00,t01), T_Func(t10,t11)
  | T_Tuple(t00,t01), T_Tuple(t10,t11) -> type_equal t00 t10 && type_equal t01 t11
  | T_Object c0, T_Object c1 -> StringMap.for_all (fun n t -> match StringMap.find_opt n c1 with | None -> false | Some t' -> type_equal t t') c0
  | T_Alts ts0, T_Alts ts1 -> List.combine ts0 ts1 |> List.for_all (fun (t0,t1) -> type_equal t0 t1)
  | _ -> false

and compute_object_addition cont0 cont1 = 
      (StringMap.merge (fun _ old add -> match old, add with
        | Some t, None
        | None, Some t -> Some t
        | Some t_o, Some t_n -> if type_equal t_o t_n then Some t_o else failwith "Type collision"
        | _,_ -> None
        ) cont0 cont1)

and simplify_type typ = match typ with
| T_Unit
| T_Bool
| T_Int
| T_Name _ 
| T_String -> typ
| T_Fix(fp,t) -> T_Fix(fp,simplify_type t)
| T_Func(a_t,r_t) -> T_Func(simplify_type a_t, simplify_type r_t)
| T_Object cont -> T_Object(StringMap.map simplify_type cont)
| T_Alias _ -> failwith "nope0"
| T_Tuple(t_0, t_1) -> T_Tuple(simplify_type t_0, simplify_type t_1)
| T_Alts ts -> T_Alts(List.map simplify_type ts)
| T_NameBind(n,ty) -> T_NameBind(n, simplify_type ty)
| T_Addition(ty0,ty1) -> (match simplify_type ty0, simplify_type ty1 with
  | T_Object cont0, T_Object cont1 -> T_Object(compute_object_addition cont0 cont1)
  | T_Name _, T_Name _ 
  | T_Object _, T_Name _
  | T_Name _, T_Object _ -> typ
  | _ -> failwith "Cannot add these types"
)

let type_combine t0 t1 = match t0, t1 with
  | T_Alts a0, T_Alts a1 -> List.fold_left (fun acc t -> if List.exists (type_equal t) acc then acc else t::acc) a0 a1
  | T_Alts a, t 
  | t, T_Alts a -> if List.exists (type_equal t) a then a else t::a
  | t0, t1 -> [t0;t1]

let rec specialize_type types t = match t with
  | T_Alias n -> (match StringMap.find_opt n types with
    | None -> failwith ("No such named type: "^n)
    | Some t -> specialize_type types t
  )
  | T_Alts alts -> T_Alts(List.map (specialize_type types) alts)
  | T_Func(t0,t1) -> T_Func(specialize_type types t0, specialize_type types t1)
  | T_Tuple(t0,t1) -> T_Tuple(specialize_type types t0, specialize_type types t1)
  | T_Addition(t0,t1) -> T_Addition(specialize_type types t0, specialize_type types t1)
  | _ -> t

let rec pattern_alias_subst pat types = match pat with
  | P_Type t -> P_Type(specialize_type types t)
  | P_Tuple(p0,p1) -> P_Tuple(pattern_alias_subst p0 types, pattern_alias_subst p1 types)
  | _ -> pat

let rec type_alias_substitute term types : term = match term with
  | Unit
  | Bool _
  | Int _
  | String _ -> term
  | Tuple(a,b) -> Tuple(type_alias_substitute a types, type_alias_substitute b types)
  | Name _ -> term
  | Func(a,ty,t) -> Func(a,specialize_type types ty,t)
  | App(a,b) -> App(type_alias_substitute a types, type_alias_substitute b types)
  | Object c -> Object(StringMap.map (fun (ty,t) -> (specialize_type types ty, t)) c)
  | With(t,c) -> With(type_alias_substitute t types, StringMap.map (fun (ty,t) -> (specialize_type types ty, t)) c)
  | Access(t,n) -> Access(type_alias_substitute t types,n)
  | Bind(n,ty,e,b) -> Bind(n,specialize_type types ty, type_alias_substitute e types, type_alias_substitute b types)
  | TypeAlias(n,ty,t) -> type_alias_substitute t (StringMap.add n ty types)
  | WhenIs(t,alts) -> WhenIs(type_alias_substitute t types, List.map (fun ((n_opt,tp),t) -> ((n_opt, pattern_alias_subst tp types), type_alias_substitute t types)) alts)

let type_name_substitute name subst = 
  let rec type_name_substitute' typ = match typ with
    | T_Unit
    | T_Bool
    | T_Int
    | T_String -> typ
    | T_Fix(fp,t) -> T_Fix(fp,type_name_substitute' t)
    | T_Func(a_t,r_t) -> T_Func(type_name_substitute' a_t, type_name_substitute' r_t)
    | T_Object cont -> T_Object(StringMap.map type_name_substitute' cont)
    | T_Alias _ -> failwith "nope1"
    | T_Tuple(t_0, t_1) -> T_Tuple(type_name_substitute' t_0, type_name_substitute' t_1)
    | T_Alts ts -> T_Alts(List.map type_name_substitute' ts)
    | T_NameBind(n,ty) -> T_NameBind(n, type_name_substitute' ty)
    | T_Name n -> if n = name then subst else typ
    | T_Addition(ty0,ty1) -> T_Addition(type_name_substitute' ty0, type_name_substitute' ty0)
  in
  type_name_substitute'

let type_name_replace_all t =
  let rec aux t substs = match t with
    | T_Unit
    | T_Bool
    | T_Int
    | T_String -> (t, substs)
    | T_Fix(fp,t) -> (
      let (ty, _) = aux t substs in  
      (T_Fix(fp,ty), substs)
    )
    | T_Func(a_t,r_t) -> (
      let (a_t, substs') = aux a_t substs in
      let (r_t, _) = aux r_t substs' in
      (T_Func(a_t, r_t), substs)
      )
    | T_Object cont -> (T_Object(StringMap.map (fun t -> aux t substs |> fst) cont), substs)
    | T_Alias _ -> failwith "nope2"
    | T_Tuple(t_0, t_1) -> (T_Tuple(aux t_0 substs |> fst, aux t_1 substs |> fst), substs)
    | T_Alts ts -> (T_Alts(List.map (fun t -> aux t substs |> fst) ts), substs)
    | T_NameBind(n,ty) -> 
      let substs' = StringMap.add n ty substs in
      (aux ty substs' |> fst, substs')
    | T_Name n -> (match StringMap.find_opt n substs with
      | Some t -> (t, substs)
      | None -> failwith ("No such type name: "^n)
    )
    | T_Addition(ty0,ty1) -> (T_Addition(aux ty0 substs |> fst, aux ty1 substs |> fst), substs)
  in
  aux t StringMap.empty |> fst

let rec type_value binds v = match v with
  | V_Unit -> T_Unit
  | V_Int _ -> T_Int
  | V_Bool _ -> T_Bool
  | V_String _ -> T_String
  | V_Tuple(v0,v1) -> T_Tuple(type_value binds  v0, type_value binds  v1)
  | V_Func(f) -> failwith "!!"
  | V_Object c -> T_Object (StringMap.map (fun (t,_) -> t) c)

and type_pattern pat = match pat with
  | P_Type t -> t
  | P_Int _ -> T_Int
  | P_Bool _ -> T_Bool
  | P_String _ -> T_String
  | P_Tuple(p0,p1) -> T_Tuple(type_pattern p0, type_pattern p1)
  | _ -> failwith "No type can be extracted from P_Any"

and pattern_bind n_opt pat binds = Option.fold ~none:binds ~some:(fun n -> match pat with
  | P_Bool _ -> StringMap.add n T_Bool binds
  | P_Type ty -> StringMap.add n ty binds
  | P_Int _ -> StringMap.add n T_Int binds
  | P_String _ -> StringMap.add n T_String binds
  | _ -> binds (* The binding should still be created, just with the same type as before, i.e. the type has not be specialized *)
) n_opt

and when_is_type binds alts = match List.map (fun ((n_opt, pat),t) -> type_term (pattern_bind n_opt pat binds) t) alts with
  | [] -> failwith "Empty WhenIs"
  | h::t -> (match List.fold_left (fun acc ty -> if List.exists (type_equal ty) acc then acc else ty::acc) [h] t with
    | [] -> failwith "Empty alts"
    | [h] -> h
    | ts -> T_Alts ts
  )

and type_term binds t = match t with
  | Unit -> T_Unit
  | Bool _ -> T_Bool
  | Int _ -> T_Int
  | String _ -> T_String
  | Tuple(t0,t1) -> T_Tuple(type_term binds t0, type_term binds t1)
  | Name n -> (match StringMap.find_opt n binds with
    | Some t -> t
    | None -> failwith ("No such binding: "^n)
  )
  | Func (n,ty,t) -> T_Func(ty,type_term (StringMap.add n ty binds) t)
  | App(f,a) -> (match type_term binds f with
      | T_Func(T_NameBind(n,f_t),f_r) -> (
        let a_t = (type_term binds a) in 
        if type_match f_t a_t then type_name_substitute n a_t f_r |> simplify_type else failwith ("Wrong argument type: "^print_type f_t ^ " vs. " ^print_type a_t)
      )
      | T_Func(f_t,f_r) -> 
        let a_t = (type_term binds a) in 
        if type_match f_t a_t then f_r else failwith ("Wrong argument type: "^print_type f_t ^ " vs. " ^print_type a_t)
      | _ -> failwith "Not a function"
  )
  | Object content -> T_Object (StringMap.map (fun (t,_) -> t) content)
  | With (t,add) -> (match type_term binds t with
    | T_Object c as obj_t -> 
      T_Addition(obj_t, T_Object(StringMap.map fst add))
    | _ -> failwith "With on non-object"
  )
  | Access(obj,fld) -> (match type_term binds obj with
    | T_Object content -> (match StringMap.find_opt fld content with
      | Some t -> t 
      | None -> failwith ("No such field: "^fld)
    )
    (*| T_Addition(ty,add) -> (
      let content = compute_object_addition ty add in
      match StringMap.find_opt fld content with
      | Some t -> t 
      | None -> failwith ("No such field: "^fld)
    )*)
    | _ -> failwith "Access to non-object"
  )
  | Bind(n,ty,t,b) -> 
    let ty' = type_name_replace_all ty in
    let tt = type_term binds t in
    if type_match ty' tt then type_term (StringMap.add n ty binds) b
    else failwith ("Binding failure: "^print_type ty'^" vs. "^print_type tt)
  | TypeAlias(n,ty,t) -> failwith "Non-replaced type name binding"
  | WhenIs(_,[]) -> failwith "Empty WhenIs"
  | WhenIs(term,alts) -> (match type_term binds term with
    | T_Alts [] -> failwith "Empty alts type"
    | T_Alts alts_types -> (
        (*let alt_match target ty = match target with
        | P_Type t -> type_match t ty
        | P_Bool _ -> type_match T_Bool ty
        | P_Int _ -> type_match T_Int ty
        | P_String _ -> type_match T_String ty
        | P_Tuple(_,_) -> failwith "Tuple matching not implemented"
        | P_Any -> true
        in*)
        when_is_type binds alts
        (*if List.for_all (fun ty -> List.exists (fun ((n_opt,pat),_) -> alt_match pat ty) alts) alts_types then 
          when_is_type binds alts
        else failwith "WhenIs not total"*)
    )
    | T_Bool -> 
      if List.for_all (fun ((n_opt, pat), body) -> match pat with 
        | P_Bool _ 
        | P_Any -> true
        | _ -> false
      ) alts then when_is_type binds alts
      else failwith "when_is bool case failed"
    | T_Int -> 
      if List.for_all (fun ((n_opt, pat), body) -> match pat with 
        | P_Int _ 
        | P_Any -> true
        | _ -> false
      ) alts then when_is_type binds alts
      else failwith "when_is int case failed"
    | _ -> failwith "WhenIs on non-alts"
  )

let rec eval_term (binds : (value * typ) StringMap.t) t : value = match t with
  | Unit -> V_Unit
  | Bool b -> V_Bool b
  | Int i -> V_Int i
  | String s -> V_String s
  | Func(a,at,t) -> V_Func(fun v -> eval_term(StringMap.add a (v, at) binds) t)
  | Tuple(t0,t1) -> V_Tuple(eval_term binds t0, eval_term binds t1)
  | Name n -> (match StringMap.find_opt n binds with
    | Some(v,_) -> v
    | None -> failwith ("No such binding: "^n)
  )
  | App (f,a) -> (
    let a = eval_term binds a in
    match eval_term binds f with
    | V_Func f -> f a
    | _ -> failwith "Not a function"
  )
  | Object content -> V_Object (StringMap.map (fun (ty,t) -> (ty, eval_term binds t)) content)
  | With (t,add) -> (match eval_term binds t with
    | V_Object c -> V_Object (StringMap.merge (fun key origin subst -> match origin, subst with
      | _, Some(ty,t) -> Some(ty, eval_term binds t)
      | Some(ty,t), None -> Some(ty, t)
      | None, None -> None
    ) c add)
    | _ -> failwith "With on non-object"
  )
  | Access(obj,fld) -> (match eval_term binds obj with
    | V_Object content -> (match StringMap.find_opt fld content with
      | Some(_,t) -> t
      | None -> failwith ("No such field: "^fld)
    )
    | _ -> failwith "Not an oject"
  )
  | Bind(n,ty,t,b) -> eval_term (StringMap.add n (eval_term binds t,ty) binds) b
  | TypeAlias(n,ty,b) -> failwith "Named type bindings cannot evaluate, must be replaced prior to evaluation"
  | WhenIs(t,alts) -> 
    let rec alts_match target value = match target, value with
      | P_Type t, _ -> type_match t (type_value binds value)
      | P_Bool v, V_Bool actual -> v = actual
      | P_String v, V_String actual -> v = actual
      | P_Int v, V_Int actual -> v = actual
      | P_Tuple(p0,p1), V_Tuple(actual0,actual1) -> alts_match p0 actual0 && alts_match p1 actual1
      | P_Any, _ -> true
      | _ -> false
    in
    let v = eval_term binds t in
    match List.find_opt (fun ((_,tp),_) -> alts_match tp v) alts with
    | Some((Some n, pat), t) -> eval_term (StringMap.add n (v, type_pattern pat) binds) t
    | Some(_, t) -> eval_term binds t
    | None -> failwith "No matching alternative found"

let builtin_int_add = V_Func(fun v -> match v  with
  | V_Int a -> V_Func (fun v -> match v with
    | V_Int b -> V_Int(a+b) 
    | _ -> failwith "Builtin addition failed"  
  )
  | _ -> failwith "Builtin addition failed"
)

let builtin_int_sub = V_Func(fun v -> match v  with
  | V_Int a -> V_Func (fun v -> match v with
    | V_Int b -> V_Int(a-b) 
    | _ -> failwith "Builtin addition failed"  
  )
  | _ -> failwith "Builtin addition failed"
)

let builtin_int_mul = V_Func(fun v -> match v  with
  | V_Int a -> V_Func (fun v -> match v with
    | V_Int b -> V_Int(a*b) 
    | _ -> failwith "Builtin addition failed"  
  )
  | _ -> failwith "Builtin addition failed"
)

let builtin_binds = [
  ("+", (builtin_int_add, T_Func(T_Int, T_Func(T_Int, T_Int))));
  ("*", (builtin_int_mul, T_Func(T_Int, T_Func(T_Int, T_Int))));
  ("-", (builtin_int_sub, T_Func(T_Int, T_Func(T_Int, T_Int))));
]














(*
type has_num = {num: int} in
let f = \o -> {num = o.num + 2} in
f {num = 5}
*)
let program0 = 
  TypeAlias("has_num", T_Object(StringMap.of_list [("num",T_Int)]), 
    Bind("f", T_Func(T_Alias "has_num", T_Alias "has_num"), Func("o", T_Alias "has_num", Object(StringMap.of_list ["num", (T_Int, App(App(Name "+", Access(Name "o", "num")), Int 2))])), 
    App(Name "f", Object(StringMap.of_list ["num", (T_Int, Int 5)])))
  )

(*
let f = \x -> when x is
  | int -> 0
  | string -> 1
in
f ""
*)
let program1 =
  Bind("f", T_Func(T_Alts[T_Int; T_String], T_Int),
    Func("x", T_Alts[T_Int; T_String], WhenIs(Name "x", [
      ((None, P_Type T_Int), Int 0);
      ((None, P_Type T_String), Int 1);
    ])),
    App(Name "f", String "")
  )


(*
let bob = {name = "Bob", age = 40} in
bob with {age = bob.age + 1}
*)
let program2 =
  Bind("bob", T_Object(StringMap.of_list [("name", T_String);("age",T_Int)]), Object(StringMap.of_list [("name",(T_String, String "Bob"));("age",(T_Int, Int 40))]), 
    With(Name "bob", StringMap.of_list ["age",(T_Int, App(App(Name "+", Int 1), Access(Name "bob","age")))])
  )


(*
let f = \x -> when x is 
| x: int -> x 
| unit -> 0
in
f 42 + f ()
*)
let program3 =
  Bind("f", T_Func(T_Alts[T_Int; T_Unit], T_Int),
    Func("x", T_Alts[T_Int; T_Unit], WhenIs(Name "x", [
      ((None, P_Type T_Unit), Int 0);
      ((Some "x", P_Type T_Int), Name "x");
    ])),
    App(App(Name "+", 
      App(Name "f", Int 42)),
      App(Name "f", Unit)
    )
  )


(*
type aged = {age: num} in
let bob = {name = "Bob", age = 40} in
let age_incr = \a -> a with {age = a.age + 1} in
age_incr bob 
*)
let program4 =
  TypeAlias("aged",T_Object(StringMap.of_list["age",T_Int]),
    Bind("bob", T_Object(StringMap.of_list[("name", T_String);("age",T_Int)]), Object(StringMap.of_list[("name",(T_String, String "Bob"));("age",(T_Int, Int 40))]), 
      Bind("age_incr", T_Func(T_Alias "aged", T_Alias "aged"), Func("a", T_Alias "aged", With(Name "a", StringMap.of_list["age",(T_Int, App(App(Name "+", Int 1), Access(Name "a", "age")))])), 
        App(Name "age_incr", Name "bob")
      )
    )
  )


(*
type some = int in
type none = unit in
type option = some | none in
type tuple = {fst: int, snd: int} in
let max : tuple -> option = \t ->
  if t.fst = t.snd then ()
  else if t.fst > t.snd then t.fst else t.snd
in
when max {fst = 2, snd = 3} is
| i: some -> i
| none -> "equal"
*)
let program5 = Unit


(*
let add_id : int -> (A: {}) -> (A + {id: int}) = 
  \id: int -> \o: {} -> o with {id = id} in
let bob : {name: string} = {name = "Bob"} in
add_id 420 bob
*)
let program6 =
  Bind("add_id", T_Func(T_Int,T_Func(T_NameBind("A", T_Object StringMap.empty), T_Addition(T_Name "A", T_Object(StringMap.of_list["id", T_Int])))),
    Func("id", T_Int, Func("o", T_Object StringMap.empty, 
      With(Name "o", StringMap.of_list["id", (T_Int, Name "id")])
    )),
    Bind("bob", T_Object(StringMap.of_list["name", T_String]), Object(StringMap.of_list["name",(T_String, String "bob")]),
      App(App(Name "add_id", Int 420), Name "bob")
    )
  )


(*
type aged = {age: int} in
type named = {name: string} in
let bob : aged + named = {name = "bob", age = 40} in
bob
*)
let program7 =
  TypeAlias("aged", T_Object(StringMap.of_list["age", T_Int]),
    TypeAlias("named", T_Object(StringMap.of_list["name", T_String]),
      Bind("bob",T_Addition(T_Alias "aged", T_Alias "named"), Object(StringMap.of_list[("name",(T_String, String "Bob"));("age",(T_Int, Int 40));]),
        Name "bob"
      )
    )
  )


(*
let f = \i -> when i is
  | 0 -> false
  | 69 -> "funny"
  | 420 -> "weed"
  | _ -> i * 10
in
when f 2 is
| "funny" -> "nice"
| "weed" -> "haha"
| bool -> "zero"
| i: int -> i
*)
let program8 =
  Bind("f",T_Func(T_Int, T_Alts[T_Bool;T_String;T_Int]), 
    Func("i", T_Int, WhenIs(Name "i", [
      ((None, P_Int 0), Bool false);
      ((None, P_Int 69), String "funny");
      ((None, P_Int 420), String "weed");
      ((None, P_Any), App(App(Name "*", Name "i"), Int 10));
    ])),
    WhenIs(App(Name "f", Int 40), [
      ((None, P_String "funny"), String "nice");
      ((None, P_String "weed"), String "haha");
      ((None, P_Type T_Bool), String "zero");
      ((Some "i", P_Type T_Int), Name "i");
    ])
  )

let execute t =
  let defaults = StringMap.of_list builtin_binds in
  let t = type_alias_substitute t StringMap.empty in
  let ty = type_term (StringMap.map snd defaults) t in
  let v = eval_term defaults t in
  Printf.printf "%s : %s\n" (print_value v) (print_type ty)


let () = execute program8
