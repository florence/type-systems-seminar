open Core
open Syntax

exception Type_error of string

(* Throws a type error contrasting what we got and expected. *)
let got_exp got exp =
  raise (Type_error ("got " ^ Printer.type_to_string got ^
                     " where " ^ exp ^ " expected"))

(* Asserts that the given type is int. *)
let assert_int = function
  | IntT -> ()
  | t    -> got_exp t "int"

(* Asserts that the given type is a function type. *)
let assert_arr = function
  | ArrT _ -> ()
  | t      -> got_exp t "arrow type"

(* Asserts that two types are the same. *)
let assert_same_type t1 t2 =
  if t1 = t2
  then ()
  else raise (Type_error ("type mismatch: " ^
                          Printer.type_to_string t1 ^ " ≠ " ^
                          Printer.type_to_string t2))

(* Asserts that two lists of types are the same. *)
let assert_same_types = List.iter2_exn ~f:assert_same_type

(* Projects the `i`th element of a tuple type. *)
let prj_tup t0 i = match t0 with
  | TupT ts as t ->
      (match List.nth ts i with
       | Some t -> t
       | None   ->
           got_exp t ("tuple of size at least " ^ string_of_int (i + 1)))
  | t -> got_exp t "tuple type"

(* Unpacks an arrow type of arity `i`. *)
let un_arr i = function
  | ArrT(ts, tr) as t ->
      if i = List.length ts
      then (ts, tr)
      else got_exp t ("arrow of arity " ^ string_of_int i)
  | t -> got_exp t "arrow type"

let rec tysubst var ty = function
  | IntT -> IntT
  | ArrT(lot,ty1) -> ArrT(List.map ~f:(tysubst var ty) lot, tysubst var ty ty1)
  | TupT(lot) -> TupT(List.map ~f:(tysubst var ty) lot)
  | All(var1,ty1) -> if var1 = var then All(var1,ty) else All(var1,tysubst var ty ty1)
  | VarT(x) -> if x = var then ty else VarT(x)

(* Type checks a term in the given environment. *)
let rec tc tyenv env = function
  | VarE x ->
      (match Env.lookup env x with
       | Some t -> t
       | None   -> raise (Type_error ("unbound variable: " ^ x)))
  | LetE(xes, body) ->
      let xts  = List.map ~f:(fun (x, e) -> (x, tc tyenv env e)) xes in
      let env' = Env.extend_list env xts in
        tc tyenv env' body
  | IntE _ -> IntT
  | SubE(e1, e2) ->
      assert_int (tc tyenv env e1);
      assert_int (tc tyenv env e2);
      IntT
  | MulE(e1, e2) ->
      assert_int (tc tyenv env e1);
      assert_int (tc tyenv env e2);
      IntT
  | If0E(e1, e2, e3) ->
      assert_int (tc tyenv env e1);
      let t2 = tc tyenv env e2 in
      let t3 = tc tyenv env e3 in
      assert_same_type t2 t3;
      t2
  | TupE(es) ->
      TupT(List.map ~f:(tc tyenv env) es)
  | PrjE(e, ix) ->
      prj_tup (tc tyenv env e) ix
  | LamE(xts, body) ->
      let env' = Env.extend_list env xts in
      let tr   = tc tyenv env' body in
      ArrT(List.map ~f:snd xts, tr)
  | AppE(e0, es) ->
      let (tas, tr) = un_arr (List.length es) (tc tyenv env e0) in
      let ts        = List.map ~f:(tc tyenv env) es in
      assert_same_types tas ts;
      tr
  | FixE(x, t, e) ->
      assert_arr t;
      let env' = Env.extend env x t in
      let t'   = tc tyenv env' e in
      assert_same_type t t';
      t
  | TyLamE(x,body) -> All(x, tc (Env.extend tyenv x ()) env body)
  | TyAppE(e,ty) ->
     let tye = tc tyenv env e in
     (match tye with
      | All(x,tyeb) -> tysubst x ty tyeb
      | _ -> raise (Type_error "that ain't on tylam"))

let tc' term =
  let module Set = Var.Set in
  match Set.to_list (ftv_of_e term) with
  | (a :: b) -> raise (Type_error ("unbound variable: " ^ a))
  | [] -> tc Env.empty Env.empty term
