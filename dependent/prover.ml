let () = Printexc.record_backtrace true

open Expr

let of_string s = Parser.expr Lexer.token (Lexing.from_string s)


let rec to_string e =
  match e with
  | Type -> "Type"
  | Var x -> x
  | App(a, b) -> "("^to_string a^" "^to_string b^")"
  | Abs (a, e1, e2) -> "(fun ("^a^" : "^to_string e1^") -> "^to_string e2^")"
  | Pi(x, e1, e2) -> "(Pi ("^x^" : "^to_string e1^") -> "^to_string e2^")"
  | Nat -> assert false
  | Z -> assert false
  | S _ -> assert false
  | Ind (_, _, _, _) -> assert false 
  | Eq (_, _) -> assert false
  | Refl _ -> assert false
  | J(_, _, _, _, _) -> assert false

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
  | S _ -> assert false
  | Ind (_, _, _, _) -> assert false 
  | Eq (_, _) -> assert false
  | Refl _ -> assert false
  | J(_, _, _, _, _) -> assert false



type context = (var * (expr * expr option)) list

exception Type_error of string

let string_of_context ctxt =
  String.concat " \n" (
      List.map (
          fun x -> (
            match x with
            | (a, (b, Some c)) -> a^" : "^to_string b^" = "^to_string c
            | (a, (b, None)) -> a ^" : "^to_string b
          )
        ) ctxt
    )

let rec red (ctxt : context) e =
  match e with
  | Var x ->(
    try
      match List.assoc x ctxt with
      | (_, Some c) -> Some c
      | (_, None) -> None
    with
      Not_found -> None
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
  | App(Abs(va, _, t), u) -> Some (subst va u t)
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
  | S _ -> assert false
  | Ind (_, _, _, _) -> assert false 
  | Eq (_, _) -> assert false
  | Refl _ -> assert false
  | J(_, _, _, _, _) -> assert false

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
  | (S _, S _) -> assert false
  | (Ind (_, _, _, _), Ind (_, _, _, _)) -> assert false 
  | (Eq (_, _), Eq (_, _)) -> assert false
  | (Refl _, Refl _) -> assert false
  | (J(_, _,_, _, _), J(_, _, _,_, _)) -> assert false
  | _ -> false

let conv ctxt e e' =
  let normalized_e = normalize ctxt e in
  let normalized_e' = normalize ctxt e' in
  alpha normalized_e normalized_e'


let rec infer (ctxt : context) e =
  match e with
  | Var x ->(
    match List.assoc x ctxt with
    | (a, _) -> a
  )
  | Abs(va, x, y) -> (
    print_endline "Abs(va, x, y)";
    print_endline (va^" : "^to_string x^",  "^to_string y);
      Pi(va, x, infer ((va, (x, None))::ctxt) y)
  )
  | App(x, y) -> (
    let t1 = infer ctxt x in
    let t2 = infer ctxt y in
    match t1 with
    | Pi(n, m, p) ->(
      if conv ctxt m t2 then subst n y p else
        raise (Type_error ("error: "^to_string m^" and "^to_string t1^"should be the same type"))
    )
    | Abs(n, m, p) ->(
      let p1 = infer ((n, (m, None))::ctxt) p in 
      if conv ctxt m t2 then subst n y p1 else
        raise (Type_error ("error: "^to_string m^" and "^to_string t1^"should be the same type"))
    )
    | _ -> raise (Type_error (to_string t2^" should be of type Pi"))
  )
  | Pi(va, x, y) -> (
    let t1 = infer ctxt x in
    let t2 = infer ((va, (x, None))::ctxt) y in
    if conv ctxt t1 t2 then t1 else
      raise (Type_error ("error: "^to_string t1^" and "^to_string t2^"should be the same type"))
  )
  | Type -> Type
  | Nat -> assert false
  | Z -> assert false
  | S _ -> assert false
  | Ind (_, _, _, _) -> assert false 
  | Eq (_, _) -> assert false
  | Refl _ -> assert false
  | J(_, _, _, _, _) -> assert false

let check ctxt e e' =
  print_endline (string_of_context ctxt);
  print_endline (to_string e');
  print_endline (to_string e);
  print_endline (to_string (infer ctxt e));
  if (infer ctxt e) = e' then () else raise (Type_error "Wrong type")

let () =
  let env = ref [] in
  let loop = ref true in
  let file = open_out "interactive.proof" in
  let split c s =
    try
      let n = String.index s c in
      String.trim (String.sub s 0 n), String.trim (String.sub s (n+1) (String.length s - (n+1)))
    with Not_found -> s, ""
  in
  while !loop do
    try
      print_string "? ";
      flush_all ();
      let cmd, arg =
        let cmd = input_line stdin in
        output_string file (cmd^"\n");
        (*print_endline cmd;*)
        split ' ' cmd
      in
      match cmd with
      | "assume" ->
        let x, sa = split ':' arg in
        let a = of_string sa in
        check !env a Type;
        env := (x,(a,None)) :: !env;
        print_endline (x^" assumed of type "^to_string a)
      | "define" ->
        let x, st = split '=' arg in
        let t = of_string st in
        let a = infer !env t in
        env := (x,(a,Some t)) :: !env;
        print_endline (x^" defined to "^to_string t^" of type "^to_string a)
      | "context" ->
         print_endline (string_of_context !env)
      | "type" ->
         let t = of_string arg in
         let a = infer !env t in
         print_endline (to_string t^" is of type "^to_string a)
      | "check" ->
        let t, a = split '=' arg in
        let t = of_string t in
        let a = of_string a in
        check !env t a;
        print_endline "Ok."
      | "eval" ->
        let t = of_string arg in
        let _ = infer !env t in
        print_endline (to_string (normalize !env t))
      | "exit" -> loop := false
      | "" | "#" -> ()
      | cmd -> print_endline ("Unknown command: "^cmd)
    with
    | End_of_file -> loop := false
    | Failure err -> print_endline ("Error: "^err^".")
    | Type_error err -> print_endline ("Typing error :"^err^".")
    | Parsing.Parse_error -> print_endline ("Parsing error.")
  done;
  print_endline "Bye."
