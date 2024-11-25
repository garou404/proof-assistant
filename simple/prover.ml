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
