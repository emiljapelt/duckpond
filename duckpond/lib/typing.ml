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
        | Some t_o, Some t_n -> if type_equal t_o t_n then Some t_o else failwith ("Type collision: "^print_type t_o^" vs. "^print_type t_n)
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
  | Func(a,ty,t) -> Func(a,Option.map (specialize_type types) ty,t)
  | App(a,b) -> App(type_alias_substitute a types, type_alias_substitute b types)
  | Object c -> Object(StringMap.map (fun (ty,t) -> (Option.map (specialize_type types) ty, t)) c)
  | With(t,c) -> With(type_alias_substitute t types, StringMap.map (fun (ty,t) -> (Option.map (specialize_type types) ty, t)) c)
  | Access(t,n) -> Access(type_alias_substitute t types,n)
  | Bind(recu,n,ty,e,b) -> Bind(recu,n,Option.map (specialize_type types) ty, type_alias_substitute e types, type_alias_substitute b types)
  | TypeAlias(n,ty,t) -> type_alias_substitute t (StringMap.add n ty types)
  | WhenIs(t,alts) -> WhenIs(type_alias_substitute t types, List.map (fun ((n_opt,tp),t) -> ((n_opt, pattern_alias_subst tp types), type_alias_substitute t types)) alts)

let type_name_substitute name subst = 
  let rec type_name_substitute' typ = match typ with
    | T_Unit
    | T_Bool
    | T_Int
    | T_Poly _
    | T_String -> typ
    | T_Fix(fp,t) -> T_Fix(fp,type_name_substitute' t)
    | T_Func(a_t,r_t) -> T_Func(type_name_substitute' a_t, type_name_substitute' r_t)
    | T_Object cont -> T_Object(StringMap.map type_name_substitute' cont)
    | T_Alias _ -> failwith "nope1"
    | T_Tuple(t_0, t_1) -> T_Tuple(type_name_substitute' t_0, type_name_substitute' t_1)
    | T_Alts ts -> T_Alts(List.map type_name_substitute' ts)
    | T_NameBind(n,ty) -> T_NameBind(n, type_name_substitute' ty)
    | T_Name n -> if n = name then subst else typ
    | T_Addition(ty0,ty1) -> T_Addition(type_name_substitute' ty0, type_name_substitute' ty1)
  in
  type_name_substitute'

let type_name_replace_all t =
  let rec aux t substs = match t with
    | T_Unit
    | T_Bool
    | T_Int
    | T_Poly _
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
    | T_Alias a -> failwith ("Type name replace found alias: "^a)
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

let rec pattern_alias_subst types pat = match pat with
  | P_Type t -> P_Type(specialize_type types t)
  | P_Tuple(p0,p1) -> P_Tuple(pattern_alias_subst types p0, pattern_alias_subst types p1)
  | _ -> pat

let rec type_alias_substitute types term : term = match term with
  | Unit
  | Bool _
  | Int _
  | String _ -> term
  | Tuple(a,b) -> Tuple(type_alias_substitute types a, type_alias_substitute types b)
  | Name _ -> term
  | Func(a,ty,t) -> Func(a,Option.map (specialize_type types) ty,t)
  | App(a,b) -> App(type_alias_substitute types a, type_alias_substitute types b)
  | Object c -> Object(StringMap.map (fun (ty,t) -> (Option.map (specialize_type types) ty, t)) c)
  | With(t,c) -> With(type_alias_substitute types t, StringMap.map (fun (ty,t) -> (Option.map (specialize_type types) ty, t)) c)
  | Access(t,n) -> Access(type_alias_substitute types t,n)
  | Bind(recu,n,ty,e,b) -> Bind(recu,n,Option.map (specialize_type types) ty, type_alias_substitute types e, type_alias_substitute types b)
  | TypeAlias(n,ty,t) -> type_alias_substitute (StringMap.add n ty types) t
  | WhenIs(t,alts) -> WhenIs(type_alias_substitute types t, List.map (fun ((n_opt,pat),t) -> ((n_opt, pattern_alias_subst types pat), type_alias_substitute types t)) alts)

let rec type_value binds v = match v with
  | V_Unit -> T_Unit
  | V_Int _ -> T_Int
  | V_Bool _ -> T_Bool
  | V_String _ -> T_String
  | V_Tuple(v0,v1) -> T_Tuple(type_value binds  v0, type_value binds  v1)
  | V_Object c -> T_Object (StringMap.map (fun (t,_) -> t) c)
  | V_Term t -> type_term binds t
  | V_Closure _ -> failwith "1"
  | V_Builtin_unary _ -> failwith "w"
  | V_Builtin_binary _ -> failwith "w"

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
  | Func (n,Some ty,t) -> T_Func(ty,type_term (StringMap.add n ty binds) t)
  | Func (n,None,t) -> failwith "Inference missing"
  | App(f,a) -> (match type_term binds f with
      | T_Func(T_NameBind(n,f_t),f_r) -> (
        let a_t = (type_term binds a) in 
        if type_match f_t a_t then type_name_substitute n a_t f_r |> simplify_type else failwith ("Wrong argument type: "^print_type f_t ^ " vs. " ^print_type a_t)
      )
      | T_Func(f_t,f_r) -> 
        let a_t = (type_term binds a) in 
        if type_match f_t a_t then f_r else failwith ("Wrong argument type: "^print_type f_t ^ " vs. " ^print_type a_t)
      | t -> failwith ("Apply on non-function: "^print_type t)
  )
  | Object content -> T_Object (StringMap.map (fun (t,_) -> Option.get t) content)
  | With (t,add) -> (match type_term binds t with
    | T_Object c (*as obj_t*) -> 
      T_Object(compute_object_addition c (StringMap.map (fun t -> fst t |> Option.get) add))
      (*T_Addition(obj_t, T_Object(StringMap.map fst add))*)
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
  | Bind(recu,n,None,t,b) ->  failwith "Inference missing"
  | Bind(recu,n,Some ty,t,b) -> 
    let ty' = type_name_replace_all ty in
    let tt = type_term (if recu then StringMap.add n ty binds else binds) t in
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