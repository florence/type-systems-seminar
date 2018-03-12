open Core

(* Variables *)
type var = Var.t

(* Types *)
type typ = IntT
         | ArrT of typ list * typ
         | TupT of typ list
         | VarT of var
         | All of var * typ

(* Expressions *)
type exp =
         | VarE of var
         | LetE of (var * exp) list * exp
         | IntE of int
         | SubE of exp * exp
         | MulE of exp * exp
         | If0E of exp * exp * exp
         | TupE of exp list
         | PrjE of exp * int
         | LamE of (var * typ) list * exp
         | AppE of exp * exp list
         | FixE of var * typ * exp
         | TyLamE of var * exp
         | TyAppE of exp * typ

let rec tfv =
  let module Set = Var.Set in
  function
  | IntT -> Set.empty
  | ArrT(tys,ty) -> Set.union (Set.union_list (List.map ~f:tfv tys)) (tfv ty)
  | TupT(tys) -> (Set.union_list (List.map ~f:tfv tys))
  | VarT(var) -> Set.singleton var
  | All(var,typ) -> Set.remove (tfv typ) var

(* Computes the free variables of an expression. *)
let rec fv e0 =
  let module Set = Var.Set in
  let remove_bindings bindings fvset =
    List.fold ~f:Set.remove ~init:fvset (List.map ~f:fst bindings) in
  match e0 with
  | VarE x -> Set.singleton x
  | LetE(bindings, body) -> remove_bindings bindings (fv body)
  | IntE _ -> Set.empty
  | SubE(e1, e2) -> Set.union (fv e1) (fv e2)
  | MulE(e1, e2) -> Set.union (fv e1) (fv e2)
  | If0E(e1, e2, e3) -> Set.union_list [fv e1; fv e2; fv e3]
  | TupE es -> Set.union_list (List.map ~f:fv es)
  | PrjE(e, _) -> fv e
  | LamE(bindings, body) -> remove_bindings bindings (fv body)
  | AppE(e, es) -> Set.union_list (List.map ~f:fv (e :: es))
  | FixE(x, _, e) -> Set.remove (fv e) x
  | TyLamE(x, e) -> Set.remove (fv e) x
  | TyAppE(e1, e2) -> Set.union (fv e1) (tfv e2)
