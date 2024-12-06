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
  | Cop of ty * ty

type tm =
  | Var of var
  | App of tm * tm
  | Abs of ty * var * tm
  | Pair of tm * tm
  | Fst of tm
  | Snd of tm
  | Tt
  | Left of tm
  | Right of tm
  | Case of tm * tm * tm

let rec string_of_ty ty =
  match ty with
  | Type x -> x
  | Imp(x, y) -> "("^string_of_ty x^" => "^string_of_ty y^")"
  | Pro(x, y) -> "("^string_of_ty x^" ∧ "^string_of_ty y^")"
  | True -> "⊤"
  | Cop(x, y) -> "("^string_of_ty x^"\\/"^string_of_ty y^")"

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
  | Left x -> 
  | Right x -> 

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


(* ((A /\ B) => (B /\ A)) *)
let and_comm = Abs(Pro(Type "A", Type "B"), "t", Pair(Snd (Var "t"), Fst (Var "t")))
let () = print_endline (string_of_ty (infer_type [] and_comm))
let () = print_endline (string_of_tm and_comm)

(* (⊤⇒A)⇒A *)
let () = print_endline( string_of_ty(Imp(Imp(True, Type "A"), Type "A")))
let () = print_endline( string_of_tm (Abs(Imp(True, Type "A"), "f", App(Var "f", Tt))))
let () = print_endline(string_of_ty( infer_type [] (Abs(Imp(True, Type "A"), "f", App(Var "f", Tt)))))

