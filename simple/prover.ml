let () = Printexc.record_backtrace true

(** Type variables. *)
type tvar = string

(** Term variables. *)
type var = string

(** Types. *)
type ty =
  | Type of tvar
  | Imp of ty * ty
  | Pro of ty * ty
  | True

type tm =
  | Var of var
  | App of tm * tm
  | Abs of ty * var * tm
  | Pair of tm * tm
  | Fst of tm
  | Snd of tm
  | Tt

(*(((A -> B) -> A) -> C)  =  (((A -> B) -> A) -> C) *)
let test = Imp(Imp(Imp(Type "A",Type "B"), Type "A"), Type "C")

(*(A -> (B -> (C -> D)))  =  A -> B -> C -> D  *) 
let test = Imp(Type "A", Imp(Type "B", Imp(Type "C", Type "D")))

(*((A -> B) -> (C -> D)))  =  (A -> B) -> C -> D *)
let test = Imp(Imp(Type "A", Type "B"), Imp(Type "A", Type "C"))

let rec string_of_ty ty =
  match ty with
  | Type x -> x
  | Imp(x, y) -> "("^string_of_ty x^" => "^string_of_ty y^")"
  | Pro(x, y) -> "("^string_of_ty x^" ∧ "^string_of_ty y^")"
  | True -> "⊤"

let () = print_endline(string_of_ty (test))

let rec string_of_tm tm =
  match tm with
  | Var x -> x
  | App(x, y) -> "("^string_of_tm x ^" "^ string_of_tm y^")"
  | Abs(ty, v, t) -> "(fun (" ^v^" : "^string_of_ty ty^") -> "^string_of_tm t^")"
  | Pair(x, y) -> "⟨"^string_of_tm x^", "^string_of_tm y^"⟩"
  | Fst(x) -> "πl("^string_of_tm x^")"
  | Snd(x) -> "πr("^string_of_tm x^")"
  | Tt -> "⟨⟩"
(*| Tt -> ""*)

let test = Abs(Imp(Type "A", Type "B"), "f", Abs(Type "A", "x", App(Var "f", Var "x")))

let () = print_endline(string_of_tm(test))

type context = (var * ty) list

exception Type_error

let rec infer_type ctxt tm =
  match tm with
  | Var x -> List.assoc x ctxt
  | App(a, b) -> (
    let type_a = infer_type ctxt a in
    match type_a with
    | Imp(x, y) -> check_type ctxt b x; y
    | _ -> raise Type_error
  )
  | Abs(ty, v, t) -> Imp(ty, infer_type ((v, ty)::ctxt) t)
  | Pair(a, b) -> Pro(infer_type ctxt a, infer_type ctxt b)
  | Fst t -> (
    match infer_type ctxt t with
    | Pro(t_a, t_b) -> t_a
    | _ -> raise Type_error
  )
  | Snd t -> (
    match infer_type ctxt t with
    | Pro(t_a, t_b) -> t_b
    | _ -> raise Type_error
  )
  | Tt -> True

and check_type ctxt tm ty =
  if infer_type ctxt tm = ty then () else raise Type_error

let test = Abs(Imp(Type "A", Type "B"), "f", Abs(Imp(Type "B", Type "C"), "g", Abs(Type "A", "x", App(Var "g", App(Var "f", Var "x")))))

let u = string_of_ty (infer_type ([("f", Imp(Type "A", Type "B")); ("g", Imp(Type "B", Type "C")); ("x", Type "A")]) test)

let () = check_type ([("x", Type "A")]) (Abs (Type "A", "x", Var "x")) (Imp (Type "A", Type "A"))

let and_comm = Abs(Pro(Type "A", Type "B"), "t", Pair(Snd (Var "t"), Fst (Var "t")))

let u = infer_type [] and_comm

let () = print_endline (string_of_ty (infer_type [] and_comm))

let () = print_endline (string_of_tm and_comm)


let test = Imp(Imp(True, Type "A"), Type "A")

let () = print_endline( string_of_ty(test))

let test2 = Abs(Imp(True, Type "A"), "f", App(Var "f", Tt))

let () = print_endline( string_of_tm test2)

let () = print_endline(string_of_ty( infer_type [] test2))

