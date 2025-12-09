open Ds
open Parser_plaf.Ast
open Parser_plaf.Parser

(* Name : Shashank Mariyappa *)

let g_store = Store.empty_store 20 (NumVal 0)

let rec eval_expr : expr -> exp_val ea_result = fun e ->
  match e with
  | Int(n) -> return @@ NumVal n
  | Var(id) -> apply_env id
  | Add(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    return @@ NumVal (n1+n2)
  | Sub(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    return @@ NumVal (n1-n2)
  | Mul(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    return @@ NumVal (n1*n2)
  | Div(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    if n2==0
    then error "Division by zero"
    else return @@ NumVal (n1/n2)
  | Let(v,def,body) ->
    eval_expr def >>= 
    extend_env v >>+
    eval_expr body 
  | ITE(e1,e2,e3) ->
    eval_expr e1 >>=
    bool_of_boolVal >>= fun b ->
    if b 
    then eval_expr e2
    else eval_expr e3
  | IsZero(e) ->
    eval_expr e >>=
    int_of_numVal >>= fun n ->
    return @@ BoolVal (n = 0)
  | Pair(e1,e2) ->
    eval_expr e1 >>= fun ev1 ->
    eval_expr e2 >>= fun ev2 ->
    return @@ PairVal(ev1,ev2)
  | Fst(e) ->
    eval_expr e >>=
    pair_of_pairVal >>= fun p ->
    return @@ fst p 
  | Snd(e) ->
    eval_expr e >>=
    pair_of_pairVal >>= fun p ->
    return @@ snd p
  | Proc(id,_,e)  ->
    lookup_env >>= fun en ->
    return (ProcVal(id,e,en))
  | App(e1,e2)  -> 
    eval_expr e1 >>= 
    clos_of_procVal >>= fun (id,e,en) ->
    eval_expr e2 >>= fun ev ->
    return en >>+
    extend_env id ev >>+
    eval_expr e
  | Letrec([(id,par,_,_,e)],target) ->
    extend_env_rec id par e >>+
    eval_expr target 
  | NewRef(e) ->
    eval_expr e >>= fun ev ->
    return (RefVal (Store.new_ref g_store ev))
  | DeRef(e) ->
    eval_expr e >>=
    int_of_refVal >>= 
    Store.deref g_store
  | SetRef(e1,e2) ->
    eval_expr e1 >>=
    int_of_refVal >>= fun l ->
    eval_expr e2 >>= fun ev ->
    Store.set_ref g_store l ev >>= fun _ ->
    return UnitVal    
  | BeginEnd([]) ->
    return UnitVal
  | BeginEnd(es) ->
    sequence (List.map eval_expr es) >>= fun l ->
    return (List.hd (List.rev l))
  | Unit -> return UnitVal
  | Debug(_e) ->
    string_of_env >>= fun str_env ->
    let str_store = Store.string_of_store string_of_expval g_store 
    in (print_endline (str_env^"\n"^str_store);
    error "Reached breakpoint")
  | IsEqual(e1, e2) -> 
    eval_expr e1 >>= 
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>= 
    int_of_numVal >>= fun n2 -> 
    return @@ BoolVal (n1 = n2)
  | IsGT(e1, e2) -> 
    eval_expr e1 >>= 
    int_of_numVal >>= fun n1 -> 
    eval_expr e2 >>= 
    int_of_numVal >>= fun n2 -> 
    return @@ BoolVal (n1 > n2)
  | IsLT(e1, e2) -> 
    eval_expr e1 >>= 
    int_of_numVal >>= fun n1 -> 
    eval_expr e2 >>= 
    int_of_numVal >>= fun n2 -> 
    return @@ BoolVal (n1 < n2)
  | IsNumber(e) -> 
    eval_expr e >>= fun ev -> 
      (match ev with
      | NumVal _ -> return (BoolVal true)
      | _ -> return (BoolVal false))
  | Record(fs) -> 
    eval_fields fs >>= fun evs -> 
      let rec build_record f v = 
        match f, v with
        | [], [] -> []
        | (id, (is_mut, _)) :: ft, vh :: vt -> 
          (id, (is_mut, vh)) :: (build_record ft vt)
        | _ -> failwith "Record Mismatch!"
        in return (RecordVal (build_record fs evs))
  | Proj(e, id) -> 
    eval_expr e >>= 
    fields_of_recordVal >>= fun fs ->
      (match List.assoc_opt id fs with 
      | Some (is_mut, ev) -> if is_mut then 
                              int_of_refVal ev >>= Store.deref g_store
                            else return ev
      | None -> error("Field not found!"))
  | SetField(e1, id, e2) -> 
    eval_expr e1 >>= 
    fields_of_recordVal >>= fun fs -> 
      (match List.assoc_opt id fs with
      | Some (is_mut, ev) -> 
        if is_mut then
        int_of_refVal ev >>= fun l -> 
          eval_expr e2 >>= fun new_ev -> 
            Store.set_ref g_store l new_ev >>= fun _ -> 
              return UnitVal
        else 
          error "Field not mutable!"
      | None -> error ("Field not found!"))
  | _ -> failwith ("Not implemented: "^string_of_expr e)
  and 
  eval_fields fs = 
  match fs with
  | [] -> return []
  | (_id, (is_mutable,e)) :: t -> 
    eval_expr e >>= fun ev -> 
    eval_fields t >>= fun evs -> 
      if is_mutable 
        then return ((RefVal (Store.new_ref g_store ev)) :: evs)
    else return (ev::evs)

let eval_prog (AProg(_,e)) =
  eval_expr e         

(** [interp s] parses [s] and then evaluates it *)
let interp (s:string) : exp_val result =
  let c = s |> parse |> eval_prog
  in run c

let interpf (s:string) : exp_val result =
  let s = String.trim s 
  in let file_name = 
    match String.index_opt s '.' with None -> s^".exr" | _ -> s
  in interp @@ read_file file_name
