(*****************************************************************************)
(*                                                                           *)
(*  Syntax.v                                                                 *)
(*                                                                           *)
(*  The data types defined here model the syntax of the 'TensorIR'.          *)
(*                                                                           *)
(*****************************************************************************)


Require Import PeanoNat.

Require Import TensorIR.Safety.Rlist.
Require Import TensorIR.Safety.Tuple.


(* Identifier: *)

Inductive Id : Set := I : nat -> Id.


Definition id_eq (x : Id) (y : Id) :=
  match x, y with
    | I n, I m => n = m
  end.


Lemma id_eq_dec : forall (x y:Id), {x = y} + {x <> y}.
Proof with auto.
  intros x y.
  destruct x as [n]; destruct y as [m]; destruct (Nat.eq_dec n m)...
  right. intuition. inversion H...
Defined.


(* Variable declaration: *)

Inductive Decl : Set := DeclVar : Id -> Tuple -> Decl.


(* Tensor expressions: *)

Inductive Expr : Set :=
  | Var    : Id -> Expr
  | Prod   : Expr -> Expr -> Expr
  | Add    : Expr -> Expr -> Expr
  (* 'Mul' is used for both scalar and *)
  (* element-wise multiplication:      *)
  | Mul    : Expr -> Expr -> Expr
  (* Transpose adjacent dimensions: *)
  | Transp : nat -> Expr -> Expr
  (* Contract over the first two dimensions: *)
  | Contr  : Expr -> Expr
  (* Project out the first dimension at a fixed index: *)
  | Proj   : nat -> Expr -> Expr
  (* Take the diagonal of the first two dimensions: *)
  | Diag   : Expr -> Expr
  (* Expand in the first dimension: *)
  | Expand : nat -> Expr -> Expr
  (* Reduce over the first dimension: *)
  | Red    : Expr -> Expr.


(* Notes on the generality of expressions:                          *)
(*   - Arbitrary transpositions of dimensions can be obtained       *)
(*     by composing transpositions of adjacent dimensions.          *)
(*   - Arbitrary permutations of dimensions can be obtained         *)
(*     by composing transpositions.                                 *)
(*   - Contractions over arbitrary pairs of dimensions can be       *)
(*     obtained by pre- and post-composing 'Contr' with             *)
(*     suitable permutations.                                       *)
(*   - Projections of arbitrary dimensions can be obtained by       *)
(*     pre- and post-composing 'Proj' with suitable transpositions. *)
(*   - The diagonal of an arbitrary pair of dimensions can be       *)
(*     obtained by pre- and post-composing 'Diag' with suitable     *)
(*     transpositions.                                              *)
(*   - Expansion in an arbitrary dimension can be obtained by pre-  *)
(*     and post-composing 'Expand' with suitable transpositions.    *)
(*   - Reduction over an arbitrary dimension can be obtained by     *)
(*     pre- and post-composing 'Red' with suitable transpositions.  *)


(* Statements assign expressions to identifiers: *)

Inductive Stmt : Set := StmtAssign : Id -> Expr -> Stmt.


(* A program is a sequence of declarations *)
(* followed by a sequence of statements:   *)

Definition Decls := rlist (A:=Decl).

Definition Stmts := rlist (A:=Stmt).

Definition Prog : Set := (Decls * Stmts)%type.
