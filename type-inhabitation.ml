open List

(* monadic let *)     
let ( let* ) o f =
  match o with
  | None -> None
  | Some x -> f x

     
type term =  Var    of int
           | Abs    of term
           | App    of term * term
           | Pair   of term * term
           | Pi1    of term
           | Pi2    of term
           | Inl    of term
           | Inr    of term
           | Case   of term * term * term
           | Absurd of term
           | I                 

type typ = Atom  of string
         | Arrow of typ * typ
         | Prod  of typ * typ
         | Sum   of typ * typ
         | False
         | Unit

type ctx = (int * typ) list
         
(* aux list functions *)
let rec list_pos x l =
  match l with
  | []      -> None
  | n :: l' -> if n = x then Some 0 else let* m = list_pos x l' in Some (m + 1)

let rec set_pos n x l =
  match (n, l) with
  | _, []     -> []
  | 0, _ :: l -> x :: l
  | m, y :: l -> y :: (set_pos (m - 1) x l)

let rec remove_pos n l =
  match (n, l) with
  | _, [] -> []
  | 0,  x :: l' -> l'
  | n', x :: l' -> x :: (remove_pos (n' - 1) l')

let rec range n =
  match n with
  | 0  -> []
  | n' -> (n' - 1) :: (range (n' - 1))

(* aux maybe monad function *)
let (>?=) (x : 'a option) (y : 'a option) : 'a option =
  match x with
  | Some x'-> Some x'
  | None   -> y

                         
let rec option_get_some (l : 'a option list) : 'a option =
  match l with
  | x :: l' -> x >?= option_get_some l'
  | [] -> None


let rec lift_var (t : term) (n : int) : term =
  let rec lift_var' t n num_lamb =
    match t with
    | Var m      -> let m' = if m < num_lamb then m else m + n in
                    Var m'
    | I -> I
    | Inl u    -> Inl (lift_var' u n num_lamb)
    | Inr u    -> Inr (lift_var' u n num_lamb)
    | Pi1 u    -> Pi1 (lift_var' u n num_lamb)
    | Pi2 u    -> Pi2 (lift_var' u n num_lamb)
    | Absurd u -> Absurd (lift_var' u n num_lamb)                                                
    | App (u, s)  -> let u' = lift_var' u n num_lamb in
                     let s' = lift_var' s n num_lamb in
                     App (u', s')
    | Pair (u, s) -> let u' = lift_var' u n num_lamb in
                     let s' = lift_var' s n num_lamb in
                     Pair (u', s')
    | Case (u, s, p) -> let u' = lift_var' u n num_lamb in
                        let s' = lift_var' s n (num_lamb + 1) in
                        let p' = lift_var' p n (num_lamb + 1) in
                        Case (u', s', p')
    | Abs u          -> Abs (lift_var' u n (num_lamb + 1))                                
  in lift_var' t n 0

let rec lift_subst (subst : int -> term) (n : int) : int -> term =
  fun m ->
  if m < n
  then Var m
  else let t = subst (m - n) in lift_var t n
    
let rec apply_subst (subst : int -> term) (t : term) : term =
  match t with
  | Var n      -> subst n
  | I -> I
  | Inl u      -> Inl (apply_subst subst u)
  | Inr u      -> Inr (apply_subst subst u)
  | Pi1 u      -> Pi1 (apply_subst subst u)
  | Pi2 u      -> Pi2 (apply_subst subst u)
  | Absurd u   -> Absurd (apply_subst subst u)                                                                
  | App (u, s)  -> App (apply_subst subst u, apply_subst subst s)
  | Pair (u, s) -> Pair (apply_subst subst u, apply_subst subst s)
  | Case (u, s, p) -> let subst' = lift_subst subst 1 in
                      Case (apply_subst subst u, apply_subst subst' s, apply_subst subst' p)                                 
  | Abs u      -> Abs (apply_subst (lift_subst subst 1) u)
(*   
let rec subst (t : term) (n : int) (new_u : term) : term =
  let rec subst' t n new_u num_lamb =
    match t with
    | Var m      -> if m = n + num_lamb then lift_var new_u num_lamb else Var m
    | Abs u      -> Abs (subst' u n new_u (num_lamb + 1))
    | App (u, s) -> App (subst' u n new_u num_lamb, subst' s n new_u num_lamb)
  in subst' t n new_u 0
 *)
type ctx = typ list

         
let rec find_term (c : ctx) (a : typ) : term option =
  match a with
  | Prod (a1, a2) -> let* a1'= find_term c a1 in
                     let* a2'= find_term c a2 in
                     Some (Pair (a1', a2'))
  | Sum  (a1, a2) -> (let* a1' = find_term c a1 in
                      Some (Inl a1')) >?=
                       (let* a2' = find_term c a2 in
                        Some (Inr a2'))
  | Unit          -> Some I
  | Arrow (a1, a2) -> let c' = a1 :: c in
                      let* t  = find_term c' a2 in
                      Some (Abs t)
  | Atom _ | False -> let maybe_term = option_get_some (map (split_ctx c a) (range (length c))) in
                       maybe_term >?= match list_pos a c with   (* conjecture: by checking the context  *)
                                      | Some n -> Some (Var n)  (* only at the end we calculate the     *)
                                      | None   -> None          (* eta-long form of the type            *)
and split_ctx (c : ctx) (a : typ) (n : int) : term option =
  let* elem = nth_opt c n in
  match elem with
  | Atom _ | Unit   -> None
  | Prod (b1, b2)  ->
     let c' = b1 :: (set_pos n b2 c) in
     let* t = find_term c' a in
     let subst1 x = if x = 0 then Inl (Var n) else
                      if x = n + 1 then Inr (Var n) else
                        Var (x - 1) in
     Some (apply_subst subst1 t)
  | Sum (b1, b2)   ->
     let c' = remove_pos n c in
     let c1 = b1 :: c' in     
     let c2 = b2 :: c' in
     let* t1 = find_term c1 a in
     let* t2 = find_term c2 a in
     let t1' = apply_subst (fun x -> if x > n then Var (x + 1) else Var x) t1 in
     let t2' = apply_subst (fun x -> if x > n then Var (x + 1) else Var x) t2 in     
     Some (Case (Var n, t1', t2'))
  | Arrow (b1, b2) ->
     let right_c = set_pos n b2 c in
     let left_c  = remove_pos n c in
     let* left   = find_term left_c b1 in
     let* right  = find_term right_c a in
     let left'   = apply_subst (fun x -> if x >= n then Var (x + 1) else Var x) left in
     let term_b2 = App (Var n, left') in
     Some (apply_subst (fun x -> if x = n then term_b2 else Var x) right)
  | False -> Some (Absurd (Var n))                     


let rec print_term (t : term) : string =
  let rec print_term' t nested num_lamb =
    match t with
    | I -> "I"
    | Var n     -> let res = string_of_int (abs (n + num_lamb)) in
                   if (n + num_lamb) < 0 then "v" ^ res else res
    | App (u, s) -> let res = (print_term' u false num_lamb) ^ " " ^ (print_term' s true num_lamb) in
                    if nested then "(" ^ res ^ ")" else res
    | Pair (u, s) -> "(" ^ print_term' u false num_lamb ^ ", " ^ print_term' s false num_lamb ^ ")"
    | Abs u      -> "(\\v" ^ string_of_int (abs (num_lamb - 1)) ^
                      ". " ^ print_term' u false (num_lamb - 1) ^ ")"
    | Inl u      -> "Inl(" ^ print_term' u false num_lamb ^ ")"
    | Inr u      -> "Inr(" ^ print_term' u false num_lamb ^ ")"
    | Pi1 u      -> "Pi1(" ^ print_term' u false num_lamb ^ ")"
    | Pi2 u      -> "Pi2(" ^ print_term' u false num_lamb ^ ")"
    | Absurd u   -> "Absurd(" ^ print_term' u false num_lamb ^ ")"
    | Case (u, s, p) -> let res1 = print_term' u false num_lamb in
                        let res2 = print_term' s false (num_lamb - 1) in
                        let res3 = print_term' p false (num_lamb - 1) in
                        let bound = "v" ^ string_of_int (abs (num_lamb - 1)) in
                        "(case " ^ res1 ^
                          " of ([" ^ bound ^ "]" ^ res2 ^
                            ") ([" ^ bound ^ "]" ^ res3 ^ "))"
  in print_term' t false 0

