(*
  Grop Members : 
  Shashank Mariyappa
  Jyotsha Kumar
*)
open ReM
open Dst
open Parser_plaf.Ast
open Parser_plaf.Parser
     
let rec chk_expr : expr -> texpr tea_result = function 
  | Int _n -> return IntType
  | Var id -> apply_tenv id
  | IsZero(e) ->
    chk_expr e >>= fun t ->
    if t=IntType
    then return BoolType
    else error "isZero: expected argument of type int"
  | Add(e1,e2) | Sub(e1,e2) | Mul(e1,e2)| Div(e1,e2) ->
    chk_expr e1 >>= fun t1 ->
    chk_expr e2 >>= fun t2 ->
    if (t1=IntType && t2=IntType)
    then return IntType
    else error "arith: arguments must be ints"
  | ITE(e1,e2,e3) ->
    chk_expr e1 >>= fun t1 ->
    chk_expr e2 >>= fun t2 ->
    chk_expr e3 >>= fun t3 ->
    if (t1=BoolType && t2=t3)
    then return t2
    else error "ITE: condition not boolean or types of then and else do not match"
  | Let(id,e,body) ->
    chk_expr e >>= fun t ->
    extend_tenv id t >>+
    chk_expr body
  | Proc(var,Some t1,e) ->
    extend_tenv var t1 >>+
    chk_expr e >>= fun t2 ->
    return @@ FuncType(t1,t2)
  | Proc(_var,None,_e) ->
    error "proc: type declaration missing"
  | App(e1,e2) ->
    chk_expr e1 >>=
    pair_of_funcType "app: " >>= fun (t1,t2) ->
    chk_expr e2 >>= fun t3 ->
    if t1=t3
    then return t2
    else error "app: type of argument incorrect"
  | Letrec([(_id,_param,None,_,_body)],_target) | Letrec([(_id,_param,_,None,_body)],_target) ->
    error "letrec: type declaration missing"
  | Letrec([(id,param,Some tParam,Some tRes,body)],target) ->
    extend_tenv id (FuncType(tParam,tRes)) >>+
    (extend_tenv param tParam >>+
     chk_expr body >>= fun t ->
     if t=tRes 
     then chk_expr target
     else error
         "LetRec: Type of recursive function does not match
declaration")
  | BeginEnd(es) ->
    List.fold_left (fun c e -> c >>= fun _ -> chk_expr e) (return UnitType) es
  | NewRef(e) ->
    chk_expr e >>= fun t ->
    return (RefType t)
  | DeRef(e) ->
    chk_expr e >>= fun t ->
    (match t with 
    | RefType inner_type -> return inner_type
    | _ -> error "expected reference type")
  | SetRef(e1, e2) ->
    chk_expr e1 >>= fun t1 ->
    chk_expr e2 >>= fun t2 ->
    (match t1 with
    | RefType inner_t ->
      if inner_t = t2 then return UnitType else error "setref: type mismatch"
    | _ -> error "Expected a reference type")
  | EmptyList(Some t) -> return (ListType t)
  | Cons(e1, e2) -> 
    chk_expr e1 >>= fun t1 -> 
    chk_expr e2 >>= fun t2 -> 
    (match t2 with
    | ListType inner_type -> 
        if t1 = inner_type then return (ListType t1) else error "type of head and tail dont match"
    | _ -> error "second agr must be list")
  | IsEmpty(e) -> 
    chk_expr e >>= fun t ->
      (match t with
      | ListType _ -> return BoolType
      | TreeType _ -> return BoolType
      | _ -> error "expected list or tree type")
  | Hd(e) -> 
    chk_expr e >>= fun t -> 
    (match t with 
    | ListType inner_type -> return inner_type
    | _ -> error "expected list type")
  | Tl(e) -> 
    chk_expr e >>= fun t -> 
    (match t with 
    | ListType _ -> return t
    | _ -> error "expected list type")
  | EmptyTree(t) -> 
    (match t with
    | Some typ -> return (TreeType typ)
    | None -> error "emptytree: type annotation required")

  | Node(de, le, re) ->
      chk_expr de >>= fun t_data ->
      chk_expr le >>= fun t_left ->
      chk_expr re >>= fun t_right ->
      (match (t_left, t_right) with
      | (TreeType t1, TreeType t2) ->
          if t1 = t_data && t2 = t_data
          then return (TreeType t_data)
          else error "node: all subtrees and data must have the same type"
      | _ -> error "node: expected tree types for left and right subtrees")

  | IsEmpty(e) ->
      chk_expr e >>= fun t ->
      (match t with
      | ListType _ -> return BoolType
      | TreeType _ -> return BoolType
      | _ -> error "empty?: expected list or tree type")

  | CaseT(target, emptycase, id1, id2, id3, nodecase) ->
      chk_expr target >>= fun target_type ->
      (match target_type with
      | TreeType t ->
          chk_expr emptycase >>= fun empty_type ->
          extend_tenv id1 t >>+
          extend_tenv id2 (TreeType t) >>+
          extend_tenv id3 (TreeType t) >>+
          chk_expr nodecase >>= fun node_type ->
          if empty_type = node_type
          then return empty_type
          else error "caseT: empty case and node case must have the same type"
      | _ -> error "caseT: expected tree type for target expression")
  | Debug(_e) ->
    string_of_tenv >>= fun str ->
    print_endline str;
    error "Debug: reached breakpoint"
  | _ -> failwith "chk_expr: implement"    
and
  chk_prog (AProg(_,e)) =
  chk_expr e

(* Type-check an expression *)
let chk (e:string) : texpr result =
  let c = e |> parse |> chk_prog
  in run_teac c

let chkpp (e:string) : string result =
  let c = e |> parse |> chk_prog
  in run_teac (c >>= fun t -> return @@ string_of_texpr t)



