(** Type variables. *)
type tvar = string

(** Term variables. *)
type var = string

(** Types. *)
type ty =
  | TVar of tvar
  | Imp of ty * ty
  | And of ty * ty
  | True
  | Or of ty * ty
  | False

type tm =
  | Var of var
  | App of tm * tm
  | Abs of var * ty * tm
  | Pair of tm * tm
  | Fst of tm
  | Snd of tm
  | Unit
  | Left of tm * ty
  | Right of ty * tm
  | Case of tm * var * tm * var *  tm
  | Absurd of tm * ty
