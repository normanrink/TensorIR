(*****************************************************************************)
(*                                                                           *)
(*  Array.v                                                                  *)
(*                                                                           *)
(*  This file introduces multi-dimensional arrays and defines them as total  *)
(*  maps from finite domains of type 'DomainT sh'. The argument 'sh' is a    *)
(*  vector of (bounded) natural numbers that is commonly referred to as the  *)
(*  shape of a multi-dimensional array.                                      *)
(*                                                                           *)
(*  The operations 'sep' and 'join' that are defined in this file manipulate *)
(*  pairs of bounded natural numbers (bounded by 'm' and 'n' respectively).  *)
(*  These operations are useful for defining the array operations 'split'    *)
(*  and 'append'. (Definitions of which appear in a separate file.)          *)
(*                                                                           *)
(*****************************************************************************)


Require Import Program.Equality.

Require Import TensorIR.Equations.Shallow.Domain.
Require Import TensorIR.Equations.Shallow.Vectors.

Import VectorNotations.



Definition Array {r : nat} (sh : NVect r) (a : Type) := DomainT sh -> a.


Fixpoint sep {m n : nat} : Fin.t (m+n) -> (Fin.t m) + (Fin.t n) :=
  match m return Fin.t (m+n) -> sum (Fin.t m) (Fin.t n) with
    | 0    => fun i => inr i
    | S m' => fun i => 
              match i in Fin.t (S k) 
                      return (k = m'+n -> sum (Fin.t (S m')) (Fin.t n)) with
                | Fin.F1    => fun _  => inl Fin.F1
                | Fin.FS i' => fun eq => let i'' := eq_rec _ _ i' _ eq in
                                         match sep i'' with
                                           | inl j => inl (Fin.FS j)
                                           | inr j => inr j
                                         end
              end eq_refl
  end.


Fixpoint join {m n : nat} : (Fin.t m) + (Fin.t n) -> Fin.t (m+n) :=
  match m return sum (Fin.t m) (Fin.t n) -> Fin.t (m+n) with
    | 0    => fun i => match i with
                         | inl i' => match i' with end
                         | inr i' => i'
                       end
    | S m' => fun i => match i with
                         | inl i' => Fin.L n i'
                         | inr i' => Fin.R (S m') i'
                       end
  end.


Lemma sep_join {m n : nat} : forall (j : (Fin.t m) + (Fin.t n)),
  sep (join j) = j.
Proof.
  induction m; intuition.
  + inversion a.
  + dependent destruction a; simpl; auto.
    destruct m.
    - inversion a.
    - specialize IHm with (inl a).
      unfold join in IHm.
      rewrite IHm; auto.
  + simpl.
    specialize IHm with (inr b).
    destruct m; simpl; auto.
    unfold join in IHm; simpl in IHm.
    rewrite IHm; auto.
Qed.


Lemma join_sep {m n : nat} : forall (j : Fin.t (m+n)),
  join (sep j) = j.
Proof.
  induction m; intuition.
  dependent destruction j; simpl; auto.
  specialize IHm with j.
  destruct (sep j) eqn:?.
  + simpl.
    destruct m.
    - inversion t.
    - simpl in IHm. rewrite IHm; auto.
  + destruct m; simpl in *; rewrite IHm; auto.
Qed.


(* Weakening of the bound 'm' by one: *)

Fixpoint wkS {m : nat} (i : Fin.t m) : Fin.t (S m) :=
  match i with
    | Fin.F1   => Fin.F1
    | Fin.FS j => Fin.FS (wkS j)
  end.


(* The empty array: *)

Definition empty {a : Type} {r : nat} (sh : NVect r) :  Array (0::sh) a :=
  fun i => let (i0,i') := i in
           Fin.case0 _ i0.
