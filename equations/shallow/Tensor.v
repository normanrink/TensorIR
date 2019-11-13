(*****************************************************************************)
(*                                                                           *)
(*  Tensor.v                                                                 *)
(*                                                                           *)
(*  This file defines a tensor as a total map from a finite domain of tuples *)
(*  to the reals. The tuples of the finite domain have type 'DomainT b',     *)
(*  where 'b' is a vector of natural numbers.                                *)
(*                                                                           *)
(*  Common tensor operations are defined in this file. Simple equalities     *)
(*  between tensor expressions formed from the defined operations are also   *)
(*  established.                                                             *)
(*                                                                           *)
(*****************************************************************************)


Require Import Eqdep_dec.
Require Import FunctionalExtensionality.
Require Import Reals.

Require Import TensorIR.Equations.Shallow.Domain.
Require Import TensorIR.Equations.Shallow.Vectors.

Import VectorNotations.



Open Scope vector_scope.

(* A Tensor is a (total) map from a finite domain to the reals: *)

Definition Tensor {r : nat} (bounds : NVect r) := DomainT bounds -> R.


(* Addition of tensors: *)

Definition Tadd {r : nat} {b : NVect r} : Tensor b -> Tensor b -> Tensor b :=
  fun t0 t1 i => (t0 i + t1 i)%R.


(* (Elementwise) multiplication of tensors: *)

Definition Tmul {r : nat} {b : NVect r} : Tensor b -> Tensor b -> Tensor b :=
  fun t0 t1 i => (t0 i * t1 i)%R.


(* Multiplication of a tensor with a scalar (from the ring/field 'R'): *)

Definition Tsmul {r : nat} {b : NVect r} : R -> Tensor b -> Tensor b :=
  fun r t i => (r * t i)%R.


(* Projection of a tensor, restricting the
   first dimension to a fixed index 'i':   *)

Definition Tproj {r : nat} {b : NVect r} {b0 : nat} (i : Fin b0) : 
  Tensor (b0::b) -> Tensor b :=
  fun t j => (t (i,j)).


(* Expansion of a tensor along the first dimension: *)

Definition Texpa {r : nat} {b : NVect r} (b0 : nat) : 
  Tensor b -> Tensor (b0::b) :=
  fun t i => let (i0,i') := i in t i'.


(* The diagonal along the first two dimensions: *)

Definition Tdiag {r : nat} {b : NVect r} {b0 : nat} : 
  Tensor (b0::b0::b) -> Tensor (b0::b) :=
  fun t i => let (i0,i) := i in t (i0,(i0,i)).


(* Transposition of a tensor. Note that since 'bijection' is used in the
   following definition of 'Ttrans', the 'Ttrans' operation really defines
   any form of reshaping or viewing of a tensor:                           *)

Definition Ttrans {r : nat} {b0 b1 : NVect r} (tr : bijection b0 b1) :
  Tensor b0 -> Tensor b1 :=
  fun t i => t (g tr i).


(* Helper function for the definition of reduction below: *)

Fixpoint reduce {r : nat} {b : NVect r} {b0 : nat} {k : nat} (le : k <= b0) :
  Tensor (b0::b) -> Tensor b :=
    match k as k'' return (k'' <= b0 -> Tensor (b0::b) -> Tensor b) with
       | 0    => fun _   _ _ => 0%R
       | S k' => 
          fun le' t i => 
            let lt   := (Nat.lt_le_trans _ _ _ (Nat.lt_succ_diag_r k') le') in
            let fk   := Fin.of_nat_lt lt in
            let le'' := le_Sn_le _ _ le' in
            (t (fk,i) + reduce le'' t i)%R
     end le.

(* Reduction along the first dimension, 
   based on addition (aka. contraction): *)

Definition Tred {r : nat} {b : NVect r} {b0 : nat} {k : nat} (le : k <= b0) :
  Tensor (b0::b) -> Tensor b :=
  fun t => reduce le t.


(* Tensor product (aka. outer product of two tensors): *)

Definition Tprod' {r0 r1 : nat} {b0 : NVect r0} {b1 : NVect r1} : 
  Tensor b0 -> Tensor b1 -> Tensor (b0 ++ b1).
  refine(fun t0 t1 i => let (i1,i2) := split' r0 i in _).
Proof.
  rewrite fst_splitat_append in i1.
  rewrite snd_splitat_append in i2.
  exact ((t0 i1) * (t1 i2))%R.
Defined.

(* Since the definition of "Tprod'" relies on lemmata, it makes sense to
   check that it is correctly defined (i.e. that it is defined as intended): *)

Lemma prod_correct' {r0 r1 : nat} {b0 : NVect r0} {b1 : NVect r1} :
  forall (t0 : Tensor b0) (t1 : Tensor b1) (j : DomainT (b0 ++ b1)),
    let (j0,j1) := split' r0 j in 
    let j0' := eq_rec _ _ j0 b0 (fst_splitat_append r0 b0 b1) in
    let j1' := eq_rec _ _ j1 b1 (snd_splitat_append r0 b0 b1) in
    (Tprod' t0 t1) j = ((t0 j0') * (t1 j1'))%R.
Proof with auto.
  unfold Tprod'; intros.
  destruct (split' r0 j)...
Qed.


(* Simpler definition of the tensor product (using the
   function "split" instead of "split'" as above):     *)

Definition Tprod {r0 r1 : nat} {b0 : NVect r0} {b1 : NVect r1} : 
  Tensor b0 -> Tensor b1 -> Tensor (b0 ++ b1) :=
    fun t0 t1 i => let (i1,i2) := split r0 i in
                   ((t0 i1) * (t1 i2))%R.


(* Two versions of the same simple lemma,
   once for "TProd'" and once for "TProd": *)

Lemma proj_ones_prod' {k : nat} {b : NVect k} :
  forall (t : Tensor b) (n : nat) (i : Fin n),
    let t1 := fun i : DomainT [n] => 1%R in
      forall (j : DomainT b), (Tproj i (Tprod' t1 t)) j = t j.
Proof with auto.
  intros. unfold Tproj. rewrite (prod_correct' t1 t (i,j)). simpl.
  rewrite Rmult_1_l.
  rewrite (@UIP_dec (NVect k) (nvect_eq_dec k)
                    (snd (splitat 1 (append [n] b))) b 
                    (snd_splitat_append 1 [n] b) eq_refl)...
Qed.

Lemma proj_ones_prod {k : nat} {b : NVect k} :
  forall (t : Tensor b) (n : nat) (i : Fin n),
    let t1 := fun i : DomainT [n] => 1%R in
      forall (j : DomainT b), (Tproj i (Tprod t1 t)) j = t j.
Proof with auto.
  intros. unfold Tproj, Tprod; simpl.
  rewrite Rmult_1_l...
Qed.

(* Only assumptions about the reals are
   required for the previous lemmata:   *)

Print Assumptions prod_correct'.
Print Assumptions proj_ones_prod'.
Print Assumptions proj_ones_prod.


(* Some simple equalities for tensor expressions: *)

Theorem add_equiv_smul {k : nat} {b : NVect k} :
  forall (t : Tensor b) (j : DomainT b), Tadd t t j = Tsmul 2 t j.
Proof with auto.
  intros; unfold Tadd, Tsmul...
  rewrite double...
Qed.

Theorem proj_inv_expa {r : nat} (b : NVect r) (b0 : nat) (i : Fin b0) : 
  forall (j : DomainT b) (t : Tensor b), Tproj i (Texpa b0 t) j = t j.
Proof with auto.
  unfold Texpa, Tproj...
Qed.

Theorem diag_transp_eq_diag {r : nat} (b0 : nat) (bnds : NVect r) : 
  forall (j : DomainT (b0::bnds)) (t : Tensor (b0::b0::bnds)), 
    let tr := transp_01 b0 b0 bnds in
    Tdiag (Ttrans tr t) j = Tdiag t j.
Proof with auto.
  unfold Ttrans, Tdiag...
Qed.

Theorem red_expa_equals_smul {r : nat} (b0 : nat) {bnds : NVect r}
                             (k : nat) (le : k <= b0):
  forall (i : DomainT bnds) (t : Tensor bnds),
  Tred le (Texpa b0 t) i = Tsmul (INR k) t i.
Proof with auto.
  induction k; intros i t; simpl; unfold Tsmul.
  + rewrite Rmult_0_l...
  + destruct k.
    * rewrite Rmult_1_l; rewrite Rplus_0_r...
    * rewrite Rmult_plus_distr_r; rewrite Rmult_1_l; rewrite Rplus_comm;
        apply Rplus_eq_compat_r.
      unfold Tsmul in IHk; rewrite <- (IHk (le_Sn_le _ _ le))...
Qed.

Close Scope vector_scope.

