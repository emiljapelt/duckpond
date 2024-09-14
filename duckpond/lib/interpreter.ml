open Absyn
open Values

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
  | T_Poly _
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

let rec type_value binds v = match v with
  | V_Unit -> T_Unit
  | V_Int _ -> T_Int
  | V_Bool _ -> T_Bool
  | V_String _ -> T_String
  | V_Tuple(v0,v1) -> T_Tuple(type_value binds  v0, type_value binds  v1)
  | V_Object c -> T_Object (StringMap.map (fun (t,_) -> t) c)
  | V_Term _ -> failwith ""
  | V_Closure _ -> failwith ""
  | V_Builtin_unary _ -> failwith ""
  | V_Builtin_binary _ -> failwith ""

and type_pattern pat = match pat with
  | P_Type t -> t
  | P_Int _ -> T_Int
  | P_Bool _ -> T_Bool
  | P_String _ -> T_String
  | P_Tuple(p0,p1) -> T_Tuple(type_pattern p0, type_pattern p1)
  | _ -> failwith "No type can be extracted from P_Any"


let rec eval_term (binds : (value * typ) StringMap.t) t : value = match t with
  | Unit -> V_Unit
  | Bool b -> V_Bool b
  | Int i -> V_Int i
  | String s -> V_String s
  | Func(a,None,t) -> failwith "Inference failure"
  | Func(a,Some at,t) -> V_Closure(a,at,binds,t)
  | Tuple(t0,t1) -> V_Tuple(eval_term binds t0, eval_term binds t1)
  | Name n -> (match StringMap.find_opt n binds with
    | Some(v,_) -> v
    | None -> failwith ("No such binding: "^n)
  )
  | App (f,a) -> (
    let a' = eval_term binds a in
    match eval_term binds f with
    | V_Closure(n,nt,binds',body) -> eval_term (StringMap.add n (a',nt) binds') body
    | V_Term t -> eval_term binds (App(t, a))
    | V_Builtin_binary f -> V_Builtin_unary (f a')
    | V_Builtin_unary f -> f a'
    | v -> failwith ("Apply on non-function:"^print_value v)
  )
  | Object content -> V_Object (StringMap.map (fun (ty,t) -> (Option.get ty, eval_term binds t)) content)
  | With (t,add) -> (match eval_term binds t with
    | V_Object c -> V_Object (StringMap.merge (fun _ origin subst -> match origin, subst with
      | _, Some(ty,t) -> Some(Option.get ty, eval_term binds t)
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
  | Bind(recur,n,None,t,b) -> failwith "Inference failure"
  | Bind(recur,n,Some ty,t,b) -> 
    if recur then eval_term (StringMap.add n (eval_term (StringMap.add n (V_Term t,ty) binds) t,ty) binds) b
    else eval_term (StringMap.add n (eval_term binds t,ty) binds) b
  | TypeAlias _ -> failwith "Named type bindings cannot evaluate, must be replaced prior to evaluation"
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
