(*****************************************************************************)
(*                                                                           *)
(*  Vector.v                                                                 *)
(*                                                                           *)
(*  This file defines fixed-length vectors of natural numbers.               *)
(*                                                                           *)
(*  Some definitions and results about vectors are borrowed from a later     *)
(*  version of Coq.                                                          *)
(*                                                                           *)
(*****************************************************************************)


Require Import Vector.
Require Import PeanoNat.

Require Export Vector.

Import Vector.VectorNotations.



Open Scope vector_scope.

(* Notation for 'append' is available in Coq 8.10: *)

Infix "++" := append : vector_scope.


(* The function 'splitat' is available in Coq 8.10: *)

Fixpoint splitat {A} (l : nat) {r : nat} : t A (l + r) -> t A l * t A r :=
  match l with
  | 0 => fun v => ([], v)
  | S l' => fun v =>
    let (v1, v2) := splitat l' (tl v) in
    (hd v::v1, v2)
  end.


(* The Lemma 'splitat_append' is available in Coq 8.10: *)

Lemma splitat_append {A} (l : nat) {r : nat} (b0 : t A l) (b1 : t A r) :
  splitat l (b0 ++ b1) = (b0, b1).
Proof with auto.
  induction b0; simpl...
  rewrite IHb0...
Qed.


(* In the present development, only vectors of natural numbers are needed: *)

Definition NVect := Vector.t nat.

Lemma fst_splitat_append (l : nat) {r : nat} (b0 : NVect l) (b1 : NVect r) :
  fst (splitat l (b0 ++ b1)) = b0.
Proof with auto.
  rewrite splitat_append...
Qed.

Lemma snd_splitat_append (l : nat) {r : nat} (b0 : NVect l) (b1 : NVect r) :
  snd (splitat l (b0 ++ b1)) = b1.
Proof with auto.
  rewrite splitat_append...
Qed.


(* Equality is decidable for 'NVect': *)

Definition nvect_eq_dec := (@VectorEq.eq_dec nat Nat.eqb Nat.eqb_eq).

Close Scope vector_scope.

