let () = Printexc.record_backtrace true

(** Type variables. *)
type tvar = string

(** Term variables. *)
type var = string

(** Types. *)
type ty =
  | Type of tvar
  | Imp of ty * ty

type tm =
  | Var of var
  | App of tm * tm
  | Abs of ty * var  * tm

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

let () = print_endline(string_of_ty (test))

let rec string_of_tm tm =
  match tm with
  | Var x -> x
  | App(x, y) -> "("^string_of_tm x ^" "^ string_of_tm y^")"
  | Abs(ty, v, t) -> "(fun (" ^v^" : "^string_of_ty ty^") -> "^string_of_tm t^")"

let test = Abs(Imp(Type "A", Type "B"), "f", Abs(Type "A", "x", App(Var "f", Var "x")))

let () = print_endline(string_of_tm(test))

type context = (var * ty) list

exception Type_error

let rec infer_type ctxt tm =
  match tm with
  | Var x -> List.assoc x ctxt
  | App(a, b) -> (
    let type_a = infer_type ctxt a in
    let type_b = infer_type ctxt b in
    match type_a with
    | Imp(x, y) ->(
      match x = type_b with
      | true -> y
      | false -> raise Type_error
    )
    | _ -> raise Type_error
  )
  | Abs(ty, v, t) -> Imp(ty, infer_type ctxt t)


let test = Abs(Imp(Type "A", Type "B"), "f", Abs(Imp(Type "B", Type "C"), "g", Abs(Type "A", "x", App(Var "g", App(Var "f", Var "x")))))

let u = string_of_ty (infer_type ([("f", Imp(Type "A", Type "B")); ("g", Imp(Type "B", Type "C")); ("x", Type "A")]) test)


let check_type ctxt tm ty =
  if infer_type ctxt tm = ty then () else raise Type_error

let () = check_type ([("x", Type "A")]) (Abs (Type "A", "x", Var "x")) (Imp (Type "A", Type "A"))

let () = check_type ([("x", Type "A")]) (Abs (Type "A", "x", Var "x")) (Imp (Type "B", Type "B"))

let () = check_type ([]) (Var "x") (Type "A")

(*Mutually recursive:*)

let rec even n =
  if n = 0 then true
  else odd (n-1)

and odd n =
  if n = 0 then false
  else even (n-1)
