open Absyn 
open Typing

module StringMap = Map.Make(String)
module StringSet = Set.Make(String)

type inference_info = {
  typ_var_count: int;
  type_mapping: typ StringMap.t;
  type_aliases: typ StringMap.t;
}

let empty_inference_info = {
  typ_var_count = 0; 
  type_mapping = StringMap.empty;
  type_aliases = StringMap.empty;
}

let bind_type name typ info =
  {info with type_mapping = StringMap.add name typ info.type_mapping}

let bind_alias name typ info =
  {info with type_aliases = StringMap.add name typ info.type_aliases}

let new_typ_var info = 
  ("tv_"^(string_of_int info.typ_var_count), {info with typ_var_count=info.typ_var_count+1})

let rec lookup_type name info = match StringMap.find_opt name info.type_mapping with
  | None -> failwith ("No such name: "^name)
  | Some t -> (match t with
    | T_Poly n -> if StringMap.mem n info.type_mapping then lookup_type n info else t
    | _ -> t
  )

let rec replace_poly name replacement ty = match ty with
  | T_Unit
  | T_Bool
  | T_Int
  | T_String -> ty
  | T_Fix(f,t) -> T_Fix(f,replace_poly name replacement t)
  | T_Func(at,rt) -> T_Func(replace_poly name replacement at, replace_poly name replacement rt)
  | T_Object c -> T_Object(StringMap.map (replace_poly name replacement) c )
  | T_Alias _ -> ty
  | T_Tuple(t0,t1) -> T_Tuple(replace_poly name replacement t0, replace_poly name replacement t1)
  | T_Alts alts -> T_Alts(List.map (replace_poly name replacement) alts)
  | T_NameBind(n,t) -> T_NameBind(n,replace_poly name replacement t)
  | T_Name _ -> ty
  | T_Addition(t0,t1) -> T_Addition(replace_poly name replacement t0, replace_poly name replacement t1)
  | T_Poly n -> if n = name then replacement else ty

let rec expand_type info ty = match ty with
  | T_Unit
  | T_Bool
  | T_Int
  | T_String -> ty
  | T_Fix(f,t) -> T_Fix(f,expand_type info ty)
  | T_Func(at,rt) -> T_Func(expand_type info at, expand_type info rt)
  | T_Object c -> T_Object(StringMap.map (expand_type info) c )
  | T_Alias a -> StringMap.find a info.type_aliases
  | T_Tuple(t0,t1) -> T_Tuple(expand_type info t0, expand_type info t1)
  | T_Alts alts -> T_Alts(List.map (expand_type info) alts)
  | T_NameBind(n,t) -> T_NameBind(n,expand_type info t)
  | T_Name _ -> ty
  | T_Addition(t0,t1) -> T_Addition(expand_type info t0, expand_type info t1)
  | T_Poly n -> 
    if StringMap.mem n info.type_mapping then lookup_type n info
    else ty
  
let rec coerce ty0 ty1 info = match ty0, ty1 with
  | a, b when a = b -> (ty0, info)
  | _, T_Poly p -> (ty0, bind_type p ty0 info)
  | T_Poly p, _ -> (ty1, bind_type p ty1 info)
  | T_Object c0, T_Object c1 -> 
    let (combined,info) = compute_object_addition c0 c1 info in
    (T_Object(combined), info)
  | _ -> failwith ("coerce case not handled: "^print_type ty0^" vs. "^print_type ty1)

and compute_object_addition cont0 cont1 info = 
  let keys = List.rev_append (StringMap.bindings cont0) (StringMap.bindings cont0) |> List.map fst |> StringSet.of_list |> StringSet.to_list in
  let (combined,info) = List.fold_right (fun key (acc,info) -> match StringMap.find_opt key cont0, StringMap.find_opt key cont1 with
  | Some t, None
  | None, Some t -> ((key,t)::acc,info)
  | Some t_o, Some t_n -> 
    let (ty,info) = coerce t_o t_n info in
    ((key,ty)::acc,info)
  | _,_ -> (acc,info)
  ) keys ([],info) in 
  (StringMap.of_list combined,info)
  
  (*StringMap.merge (fun _ old add -> match old, add with
    | Some t, None
    | None, Some t -> Some t
    | Some t_o, Some t_n -> Some (coerce t_o t_n info |> fst) (* if type_equal t_o t_n then Some t_o else failwith ("Type collision: "^print_type t_o^" vs. "^print_type t_n)*)
    | _,_ -> None
    ) cont0 cont1*)

let rec infer_term term info : (typ*term*inference_info) = match term with
| Unit -> (T_Unit, term, info)
| Bool _ -> (T_Bool, term, info)
| Int _ -> (T_Int ,term, info)
| String _ -> (T_String, term, info)
| Tuple(t0,t1) -> 
  let (ty0,term0,info') = infer_term t0 info in
  let (ty1,term1,info'') = infer_term t1 info' in
  (T_Tuple(ty0,ty1), Tuple(term0,term1), info'')
| Name n -> (lookup_type n info, term, info)
| Func(arg,Some ty,body) -> 
  let (body_typ,body,info) = infer_term body (bind_type arg ty info) in
  (T_Func(ty, body_typ), body, info)
| Func(arg,None,body) -> 
  let (typ_var, info) = new_typ_var info in
  let (body_typ,body,info) = infer_term body (bind_type arg (T_Poly typ_var) info) in
  (T_Func(expand_type info (T_Poly typ_var), body_typ), body, info)
| App(f,a) -> (
  let (f_ty,f_term,info') = infer_term f info in
  let (a_ty,a_term,info'') = infer_term a info' in
  match f_ty with
  | T_Func(fa_ty,fr_ty) -> 
    let (co_ty,info''') = coerce a_ty fa_ty info'' in
    (expand_type info''' fr_ty,App(f_term,a_term),info''')
  | _ -> failwith "Application of non-function"
)
| Object c -> 
  let (acc,info) = StringMap.fold (fun n (ty_opt,term) (acc,info) -> match ty_opt with
    | Some ty -> 
      let (inf_ty,t,info) = infer_term term info in
      if type_match ty inf_ty then ((n,(ty,t))::acc,info)
      else failwith "Type matching failure"
    | None -> 
      let (ty,t,info) = infer_term term info in
      ((n,(ty,t))::acc,info)
) c ([],info) in 
(T_Object(acc |> List.map (fun (n,(ty,_)) -> (n,ty)) |> StringMap.of_list), Object(acc |> List.map (fun (n,(ty,t)) -> (n,(Some ty, t))) |> StringMap.of_list), info)
| With(obj,add) -> failwith ":("
| Access(obj,field) -> (
  let (obj_ty,obj,info') = infer_term obj info in
  match obj_ty with
  | T_Object c -> (match StringMap.find_opt field c with
      | Some ty -> (ty,obj,info')
      | None -> failwith ("No such field: "^field)
  )
  | T_Poly p -> (
    let (field_typ_var, info) = new_typ_var info in
    let obj_typ = T_Object(StringMap.of_list[field,T_Poly field_typ_var]) in
    let info = bind_type p obj_typ info in
    (T_Poly field_typ_var, term, info)
  )
  | _ -> failwith ("Field access on non-object: "^print_type obj_ty)
)
| Bind(recur,name,Some ty,bind,body) -> 
  let (bind_typ,bind,info) = infer_term bind info in
  if type_match ty bind_typ then (
    let (body_typ,term,info) = infer_term body (bind_type name bind_typ info) in
    (body_typ,term,info)
  )
  else failwith "Type mismatch in binding"
| Bind(recur,name,None,bind,body) -> 
  let (bind_typ,bind,info) = infer_term bind info in
  let (body_typ,term,info) = infer_term body (bind_type name bind_typ info) in
  (body_typ,term,info)
| TypeAlias(name,ty,body) -> infer_term body (bind_alias name ty info)
| WhenIs(term,alts) -> failwith ":("
