open Ds
open Parser_plaf.Ast
open Parser_plaf.Parser
    
(** [eval_expr e] evaluates expression [e] *)
let rec eval_expr : expr -> int result =
  fun e ->
  match e with
  | Int n      -> return n
  | Add(e1,e2) ->
    eval_expr e1 >>= fun n ->
    eval_expr e2 >>= fun m ->
    return (n+m)   
  | Sub(e1,e2) ->
    eval_expr e1 >>= fun n ->
    eval_expr e2 >>= fun m ->
    return (n-m)   
  | Mul(e1,e2) ->
    eval_expr e1 >>= fun n ->
    eval_expr e2 >>= fun m ->
    return (n*m)   
  | Div(e1,e2) ->
    eval_expr e1 >>= fun n ->
    eval_expr e2 >>= fun m ->
    if m=0
    then error "Division by zero" 
    else return (n/m)
  | Abs(e) ->
    eval_expr e >>= fun n -> 
      return (abs n)
  | Avg([]) ->
      error "No arguments"
  | Avg(es) -> 
      eval_exprs es >>= fun lst -> 
        let lst_sum = List.fold_left (+) 0 lst in 
        let lst_length = List.length es in
        return (lst_sum / lst_length) 
  
  | _ -> failwith "Not implemented yet!"
and 
   eval_exprs es =   (* evaluates a list of expressions es; should call eval_expr *)
    match es with
    | [] -> return []
    | h::t -> 
      eval_expr h >>= fun h' -> 
      eval_exprs t >>= fun t' -> 
        return (h' :: t')

(** [eval_prog e] evaluates program [e] *)
let eval_prog (AProg(_,e)) =
  eval_expr e

(** [interp s] parses [s] and then evaluates it *)
let interp (e:string) : int result =
  e |> parse |> eval_prog



