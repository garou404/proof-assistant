let () = Printexc.record_backtrace true

open Expr

let ty_of_string s = Parser.ty Lexer.token (Lexing.from_string s)

let tm_of_string s = Parser.tm Lexer.token (Lexing.from_string s)

let rec string_of_ty ty =
  match ty with
  | TVar x -> x
  | Imp(x, y) -> "("^string_of_ty x^" => "^string_of_ty y^")"
  | And(x, y) -> "("^string_of_ty x^" ∧ "^string_of_ty y^")"
  | True -> "⊤"
  | Or(x, y) -> "("^string_of_ty x^" \\/ "^string_of_ty y^")"
  | False -> "⊥"
  | Nat -> "Nat"


let rec string_of_tm tm =
  match tm with
  | Var x -> x
  | App(x, y) -> "("^string_of_tm x ^" "^ string_of_tm y^")"
  | Abs(v ,ty , t) -> "(fun (" ^v^" : "^string_of_ty ty^") -> "^string_of_tm t^")"
  | Pair(x, y) -> "⟨"^string_of_tm x^", "^string_of_tm y^"⟩"
  | Fst(x) -> "πl("^string_of_tm x^")"
  | Snd(x) -> "πr("^string_of_tm x^")"
  | Unit -> "⟨⟩"
  | Left(x, y) -> "left("^string_of_tm x^", "^string_of_ty y^")"
  | Right(y, x) -> "right("^string_of_tm x^", "^string_of_ty y^")"
  | Case(t, x, u, y, v) -> "case "^string_of_tm t^" of "^x^" -> "^string_of_tm u^" | "^y^" -> "^string_of_tm v
  | Absurd(x, y) -> "case("^string_of_tm x^", "^string_of_ty y^")"
  | Zero -> "Z"
  | S x -> "S( "^string_of_tm x^")"
  | Rec(n, z, x, y, s) -> "rec("^string_of_tm n^", "^string_of_tm z^", "^x^y^" -> "^string_of_tm s^")"


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
  | Abs(v, ty, t) -> Imp(ty, infer_type ((v, ty)::ctxt) t)
  | Pair(a, b) -> And(infer_type ctxt a, infer_type ctxt b)
  | Fst t -> (
    match infer_type ctxt t with
    | And(t_a, _) -> t_a
    | _ -> raise Type_error
  )
  | Snd t -> (
    match infer_type ctxt t with
    | And(_, t_b) -> t_b
    | _ -> raise Type_error
  )
  | Unit -> True
  | Left (x, a) -> Or(infer_type ctxt x, a)
  | Right (a, x) -> Or(a, infer_type ctxt x)
  | Case(t, x, u, y, v) -> (
    match infer_type ctxt t with
    | Or(a, b) ->(
      let type_1 = infer_type ((x,a)::ctxt) u in
      let type_2 = infer_type ((y,b)::ctxt) v in
      if type_1 = type_2 then type_1 else raise Type_error
    )
    | _ -> raise Type_error
  )
  | Absurd(x, y) -> check_type ctxt x False; y
  | Zero -> Nat
  | S(x) -> infer_type ctxt x
  | Rec(n, z, x, y, s) -> (
    check_type ctxt n Nat;
    let type_1 = infer_type ctxt z in
    let type_2 = infer_type ((x,Nat)::(y,type_1)::ctxt) s in
    if type_1 = type_2 then type_1 else raise Type_error
  )

and check_type ctxt tm ty =
  if infer_type ctxt tm = ty then () else raise Type_error

let test = S(S(Zero))

(*
(* ((A /\ B) => (B /\ A)) *)
let and_comm = Abs("t", And(TVar "A", TVar "B"), Pair(Snd (Var "t"), Fst (Var "t")))
let () = print_endline (string_of_ty (infer_type [] and_comm))
let () = print_endline (string_of_tm and_comm)

(* (⊤⇒A)⇒A *)
let () = print_endline( string_of_ty(Imp(Imp(True, TVar "A"), TVar "A")))
let () = print_endline( string_of_tm (Abs("f", Imp(True, TVar "A"), App(Var "f", Unit))))
let () = print_endline(string_of_ty( infer_type [] (Abs("f", Imp(True, TVar "A"), App(Var "f", Unit)))))

(* ((A \/ B) => (B \/ A)) *)
let or_comm = Abs("t", Or(TVar "A", TVar "B"), Case(Var "t", "x", Right(TVar "B", Var "x"), "y", Left(Var "y", TVar "A")))
let () = print_endline (string_of_ty(infer_type [] or_comm))

(* (A∧(A⇒⊥))⇒B *)
let and_false = Abs("t", And(TVar "A", Imp(TVar "A", False)), Absurd(App(Snd(Var "t"), Fst(Var "t")), TVar "B"))
let () = print_endline (string_of_ty( infer_type [] and_false))


let test_ctxt = [("x" , Imp(TVar "A", TVar "B")); ("y", And(TVar "A", TVar "B")); ("Z", True)]
 *)
let string_of_ctxt ctxt =
  String.concat " , " (List.map (fun x -> match x with (a, b) -> a ^" : "^string_of_ty b) ctxt)

type sequent = context * ty

let string_of_seq sqt =
  match sqt with (ctxt, a) -> string_of_ctxt ctxt^" |- "^string_of_ty a


let rec prove env a =
  print_endline (string_of_seq (env,a));
  print_string "? "; flush_all ();
  let error e = print_endline e; prove env a in
  let cmd, arg =
    let cmd = input_line stdin in
    let n = try String.index cmd ' ' with Not_found -> String.length cmd in
    let c = String.sub cmd 0 n in
    let a = String.sub cmd n (String.length cmd - n) in
    let a = String.trim a in
    c, a
  in
  match cmd with
  | "intro" -> (
    match a with
    | Imp (a, b) ->
       if arg = "" then error "Please provide an argument for intro." else
         let x = arg in
         let t = prove ((x,a)::env) b in
         Abs (x, a, t)
    | And(a, b) ->
       let x = prove env a in
       let y = prove env b in
       Pair(x, y)
    | True -> Unit
    | Nat -> (
      print_endline "TEST";
      print_endline arg;
      if arg = "" then error "Please provide an argument for intro." else
        let t = tm_of_string arg in
        print_endline(string_of_tm t);
        match t with
        | Zero -> Zero
        | _ -> prove env Nat
    )
    | _ ->
       error "Don't know how to introduce this."
  )
  | "exact" ->
     let t = tm_of_string arg in
     if infer_type env t <> a then error "Not the right type."
     else t
  | "elim" ->(
    if arg = "" then error "Please provide an argument for elim." else
      let tx = List.assoc arg env in
      match tx with
      | Imp(ta, tb) when tb = a ->(
        let y = prove env ta in
        App(Var arg, y)
      )
      | Or(ta, tb) ->(
        (*let t = prove env tx in*)
        let u = prove ((arg,ta)::env) a in
        let v = prove ((arg,tb)::env) a in
        Case(Var arg, arg, u, arg, v)
      )
      | False -> Absurd(Var arg, a)
      | Nat -> (
        let z = prove env a in
        let s = prove (("x",Nat)::("y",a)::env) a in
        Rec(Var arg,z,"x","y",s)
      )
      | _ ->
         error "Don't know how to eliminate this."
  )
  | "cut"-> (
    if arg = "" then error "Please provide an argument for elim." else
      let b = ty_of_string arg in
      let tm1 = prove env (Imp(b, a)) in
      let tm2 = prove env (b) in
      App(tm1, tm2)
  )
  | "fst" -> (
    if arg = "" then error "Please provide an argument for elim." else
      let x = arg in
      match (List.assoc x env) with
      | And(a1, _) when a1 = a -> Fst(Var x)
      | _ -> error "Type error"
  )
  | "snd" -> (
    if arg = "" then error "Please provide an argument for elim." else
      let x = arg in
      match (List.assoc x env) with
      | And(_, b1) when b1 = a -> Snd(Var x)
      | _ -> error "Type error"
  )
  | "left" -> (
    match a with
    | Or(a, b) -> (
      let c = prove env a in
      Left(c, b)
    )
    | _ -> error ("Type error")
  )
  | "right" -> (
    match a with
    | Or(a, b) -> (
      let x = prove env b in
      Right(a, x)
    )
    | _ -> error ("Type error")
  )
  | cmd -> error ("Unknown command: " ^ cmd)
         
let () =
  print_endline "Please enter the formula to prove:";
  let a = input_line stdin in
  let a = ty_of_string a in
  print_endline "Let's prove it.";
  let t = prove [] a in
  print_endline "done.";
  print_endline "Proof term is";
  print_endline (string_of_tm t);
  print_string  "Typechecking... "; flush_all ();
  assert (infer_type [] t = a);
  print_endline "ok."
