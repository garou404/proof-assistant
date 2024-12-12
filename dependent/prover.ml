let () = Printexc.record_backtrace true

(** Variables. *)
type var = string

(** Expressions. *)
type expr =
  | Type
  | Var of var
  | App of expr * expr
  | Abs of var * expr * expr
  | Pi of var * expr * expr
  | Nat
  | Z
  | S of expr
  | Ind of expr * expr * expr * expr 
  | Eq of expr * expr
  | Refl of expr
  | J of expr * expr * expr * expr * expr

(* Fill me in! *)

let rec to_string e =
  match e with
  | Type -> "Type"
  | Var x -> x
  | App(a, b) -> "("^to_string a^" "^to_string b^")"
  | Abs (a, e1, e2) -> "(λ "^a^" : "^to_string e1^". "^to_string e2^" )"
  | Pi(x, e1, e2) -> "Π("^x^" : "^to_string e1^")."^to_string e2
  | Nat -> assert false
  | Z -> assert false
  | S x -> assert false
  | Ind (e1, e2, e3, e4) -> assert false 
  | Eq (e1, e2) -> assert false
  | Refl e -> assert false
  | J(e1, e2, e3, e4, e5) -> assert false

let n = ref 0

let fresh_var () : var =
  let new_var = "x"^string_of_int !n in
  n := !n + 1;
  new_var

(* u[t/x] *)
let rec subst x t u =
  match u with
  | Var y when y = x -> t
  | Var y -> Var y
  | Abs(va, y, z) ->(
    let frsh_var = fresh_var () in
    let y_frshvar = subst va (Var frsh_var) y in
    let z_frshvar = subst va (Var frsh_var) z in
    Abs(frsh_var, subst x t y_frshvar, subst x t z_frshvar)
  )
  | Pi(va, a, b) ->(
    let frsh_var = fresh_var () in
    let a_frshvar = subst va (Var frsh_var) a in
    let b_frshvar = subst va (Var frsh_var) b in
    Pi(frsh_var, subst x t a_frshvar, subst x t b_frshvar)    
  )
  | App(y, z) -> App(subst x u y, subst x u z)
  | Type -> Type
  | Nat -> assert false
  | Z -> assert false
  | S x -> assert false
  | Ind (e1, e2, e3, e4) -> assert false 
  | Eq (e1, e2) -> assert false
  | Refl e -> assert false
  | J(e1, e2, e3, e4, e5) -> assert false


type context = (var * (expr * expr option)) list

let rec string_of_context ctxt =
  String.concat " , " (
      List.map (
          fun x -> (
            match x with
            | (a, (b, Some c)) -> a^" : "^to_string b^" = "^to_string c
            | (a, (b, None)) -> a ^" : "^to_string b
          )
        ) ctxt
    )

let rec red ctxt e =
  match e with
  | Var x ->(
    match List.assoc x ctxt with
    | (a, (b, Some c)) -> Some c
    | (a, (b, None)) -> None
  )
  | Abs(va, x, y) -> (
    match red ctxt x with
    | Some w -> Some( Abs(va, w, y))
    | None -> (
      match red ctxt y with
      | Some v -> Some( Abs(va, x, v))
      | None -> None
    )
  )
  | App(Abs(va, x, t), u) -> Some (subst va u t)
  | App(x, y) -> (
    match red ctxt x with
    | Some z -> Some (App(z, y))
    | None -> (
      match red ctxt y with
      | Some w -> Some (App(x, w))
      | None -> None
    )
  )
  | Pi(va, x, y) ->(
    match red ctxt x with
    | Some w -> Some( Pi(va, w, y))
    | None -> (
      match red ctxt y with
      | Some v -> Some( Pi(va, x, v))
      | None -> None
    )
  )
  | Type -> None
  | Nat -> assert false
  | Z -> assert false
  | S x -> assert false
  | Ind (e1, e2, e3, e4) -> assert false 
  | Eq (e1, e2) -> assert false
  | Refl e -> assert false
  | J(e1, e2, e3, e4, e5) -> assert false

let rec normalize ctxt e =
  match red ctxt e with
  | Some u -> normalize ctxt u
  | None -> e

let rec alpha e1 e2 =
  match (e1, e2) with
  | (Var x1, Var x2) -> x1 = x2
  | (Abs (x1, y1, z1), Abs(x2, y2, z2)) ->(
    let frsh_var = fresh_var () in
    if alpha y1 y2 then
      alpha (subst x1 (Var frsh_var) z1) (subst x2 (Var frsh_var) z2)
    else
      false
  )
  | (Pi (x1, y1, z1), Pi(x2, y2, z2)) -> (
    let frsh_var = fresh_var () in
    if alpha y1 y2 then
      alpha (subst x1 (Var frsh_var) z1) (subst x2 (Var frsh_var) z2)
    else
      false
  )
  | (App(x1, y1), App(x2, y2)) -> if alpha x1 x2 then alpha y1 y2 else false
  | (Type, Type) -> true
  | (Nat, Nat) -> assert false
  | (Z, Z) -> assert false
  | (S x, S y) -> assert false
  | (Ind (e1, e2, e3, e4), Ind (u1, u2, u3, u4)) -> assert false 
  | (Eq (e1, e2), Eq (u1, u2)) -> assert false
  | (Refl e, Refl u) -> assert false
  | (J(e1, e2, e3, e4, e5), J(u1, u2, u3, u4, u5)) -> assert false
  | _ -> false

let conv ctxt e e' =
  let normalized_e = normalize ctxt e in
  let normalized_e' = normalize ctxt e' in
  alpha normalized_e normalized_e'

exception Type_error of string

let rec infer ctxt e =
  match e with
  | Var x -> List.assoc x ctxt
  | Abs(va, x, y) -> Pi(va, x, infer (ctxt y)
  | App(x, y) -> subst (infer ctxt x)
  | Pi(va, x, y) -> Type
  | Type -> Type
  | Nat -> assert false
  | Z -> assert false
  | S x -> assert false
  | Ind (e1, e2, e3, e4) -> assert false 
  | Eq (e1, e2) -> assert false
  | Refl e -> assert false
  | J(e1, e2, e3, e4, e5) -> assert false
 
