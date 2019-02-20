(*****************************************************************************)
(*                                                                           *)
(*  Tensor.v                                                                 *)
(*                                                                           *)
(*  Tensors are represented as maps from tuples to values.                   *)
(*                                                                           *)
(*  For the purpose of discussing (memory) safety, it suffices to consider   *)
(*  only two values:                                                         *)
(*    (1) the undefined value 'VUndef', which represents a memory location   *)
(*        that does not carry a defined value; and                           *)
(*    (2) any other value 'VSome', which represents any and all              *)
(*        meaningfully defined memory locations.                             *)
(*                                                                           *)
(*  For a map from tuples to values to be considered a tensor, the map must  *)
(*  satisfy the 'DomainBound' predicate, which says that there is a (unique) *)
(*  tuple 't' such that the map is defined for all tuples below 't'          *)
(*  ("below" in the relation '.<=.', i.e. for all tuples 'i' with 'i.<=.t'). *)
(*                                                                           *)
(*****************************************************************************)


Require Import FunctionalExtensionality.
Require Import List.
Require Import PeanoNat.

Import ListNotations.

Require Import TensorIR.Safety.Tuple.



Inductive Value : Set :=
  | VUndef : Value
  | VSome  : Value.


Definition DomainBound (x:Tuple -> Value) (t:Tuple) :=
  forall (i:Tuple), x i = VSome <-> i.<=.t.

Definition DomainBound_undef (x:Tuple -> Value) (t:Tuple) :=
  forall (i:Tuple), x i <> VUndef <-> i.<=.t.

Definition DomainBound_nle (x:Tuple -> Value) (t:Tuple) :=
  forall (i:Tuple), x i = VUndef <-> ~i.<=.t.


Definition Tensor : Set :=
  {x:Tuple -> Value | exists (t:Tuple), DomainBound x t}.


Lemma ten_some_not_undef : forall (x:Tuple -> Value) (i:Tuple),
  x i = VSome <-> x i <> VUndef.
Proof with auto.
  intuition. rewrite H in H0. inversion H0.
  destruct (x i) eqn:xieq... contradiction.
Qed.


Lemma ten_undef_not_some : forall (x:Tuple -> Value) (i:Tuple),
  x i = VUndef <-> x i <> VSome.
Proof with auto.
  intuition. rewrite H in H0. inversion H0.
  destruct (x i) eqn:xieq... contradiction.
Qed.


(* Equivalence of the different versions of 'DomainBound': *)

Lemma ten_domain_domain_undef : forall (x:Tuple -> Value) (t: Tuple),
  DomainBound x t <-> DomainBound_undef x t.
Proof with auto.
  unfold DomainBound_undef. unfold DomainBound. intuition.
  apply ten_some_not_undef in H0; apply H in H0...
  apply H in H0; apply ten_some_not_undef in H0...
  apply ten_some_not_undef in H0; apply H in H0...
  destruct (x i) eqn:xieq... apply H in xieq... contradiction.
Qed.


Lemma ten_domain_undef_domain_nle : forall (x:Tuple -> Value) (t: Tuple),
  DomainBound_undef x t <-> DomainBound_nle x t.
Proof with auto.
  unfold DomainBound_undef. unfold DomainBound_nle. intuition.
  apply H in H1...
  destruct (x i) eqn:xieq... rewrite ten_some_not_undef in xieq.
    apply H in xieq. contradiction.
  destruct (tup_le_dec i t)... apply H in n. contradiction.
  apply H in H1...
Qed.


Lemma ten_domain_nle_domain : forall (x:Tuple -> Value) (t: Tuple),
  DomainBound_nle x t <-> DomainBound x t.
Proof with auto.
  unfold DomainBound_nle. unfold DomainBound. intuition...
  destruct (tup_le_dec i t)... apply H in n. rewrite H0 in n. inversion n.
  apply ten_some_not_undef. destruct (x i) eqn:xieq.
    apply H in xieq... intro F; inversion F.
  apply H in H1. rewrite H0 in H1. inversion H1.
  destruct (x i) eqn:xieq... apply H in xieq. contradiction.
Qed.


(* Tensors with a bound of '[]' (i.e. the empty tuple) have exactly *)
(* one entry. Such tensors should be thought of as scalars:         *)

Theorem ten_domain_one_entry : forall (x:Tuple -> Value),
  DomainBound x [] -> x [] = VSome /\ forall i, i <> [] -> x i = VUndef.
Proof with auto.
  intuition.
  destruct (x []) eqn:xnileq... rewrite ten_domain_domain_undef in H.
    apply H in xnileq. contradiction. simpl; trivial.
  destruct (x i) eqn:xieq...
    apply H in xieq. destruct i; contradiction.
Qed.


(* The proof of uniqueness of the tuple (i.e. the bound) *)
(* in 'DomainBound' is split into a couple of lemmas :   *)

Definition ten_projection (x:Tuple -> Value) (i:nat) := fun j => x (i::j).

Lemma ten_projection_domain :
  forall (t:Tuple) (n i:nat) (x:Tuple -> Value),
  DomainBound x (n::t) -> i <= n ->
    DomainBound (ten_projection x i) t.
Proof with auto.
  intros. unfold DomainBound in H. unfold DomainBound. intuition.
  apply H in H1. simpl in H1. destruct H1...
  assert((i::i0).<=.(n::t)). simpl...
  apply H in H2...
Qed.


(* Helper lemma for the uniqueness of bounds: *)

Lemma ten_domain_unique' : forall (m n:nat) (t t':Tuple) (x:Tuple -> Value),
  DomainBound x (m::t) ->
  DomainBound x (n::t') ->
    m = n.
Proof with auto.
  intuition.
  destruct (Compare_dec.lt_eq_lt_dec m n). destruct s...
    destruct (x (n::t')) eqn:xeq.
      assert((n::t').<=.(n::t')) by apply tup_le_refl. apply H0 in H1.
        rewrite xeq in H1. inversion H1.
      assert(~(n::t').<=.(m::t)). intro. destruct H1. 
        apply (Nat.lt_le_trans m n m l) in H1. apply Nat.lt_irrefl in H1...
          rewrite <- ten_domain_nle_domain in H. apply H in H1.
            rewrite xeq in H1. inversion H1.
    destruct (x (m::t)) eqn:xeq.
      assert((m::t).<=.(m::t)) by apply tup_le_refl. apply H in H1.
        rewrite xeq in H1. inversion H1.
      assert(~(m::t).<=.(n::t')). intro. destruct H1. 
        apply (Nat.lt_le_trans n m n l) in H1. apply Nat.lt_irrefl in H1...
          rewrite <- ten_domain_nle_domain in H0. apply H0 in H1.
            rewrite xeq in H1. inversion H1.
Qed.


(* Finally, uniqueness lemma for bounds in 'DomainBound': *)

Theorem ten_domain_unique : forall (t t':Tuple) (x:Tuple -> Value),
  DomainBound x t ->
  DomainBound x t' ->
    t = t'.
Proof with auto.
  induction t. destruct t'; intuition.
    destruct (x (n::t')) eqn:xeq.
      assert((n::t').<=.(n::t')) by apply tup_le_refl. apply H0 in H1.
      rewrite xeq in H1. inversion H1.
      apply H in xeq. inversion xeq.
    intuition. destruct t'.
      destruct (x (a::t)) eqn:xeq.
        assert((a::t).<=.(a::t)) by apply tup_le_refl. apply H in H1.
        rewrite xeq in H1. inversion H1.
        apply H0 in xeq. inversion xeq.
    pose proof (ten_domain_unique' a n _ _ x H H0). subst.
      pose proof (ten_projection_domain _ _ _ _ H (Nat.le_refl n)).
      pose proof (ten_projection_domain _ _ _ _ H0 (Nat.le_refl n)).
      apply (IHt _ _ H1) in H2. subst...
Qed.


(* The following definition constructs a tensor from a given bound 't'. *)
(* Since 'VSome' is the only meaningful value, there is precisely one   *)
(* tensor for any given bound 't'.                                      *)

Definition ten_tensor_from_tuple (t:Tuple) : Tensor.
  refine(exist _ (fun i => if i.<=?.t then VSome else VUndef) _).
Proof with auto.
  exists t. unfold DomainBound. intro i.
  destruct (i.<=?.t) eqn:iteq.
    apply tup_le_leb in iteq. intuition.
    intuition. inversion H. apply tup_nle_nleb in H... inversion H.
Defined.


Lemma ten_from_tuple_bound : forall (t:Tuple),
  DomainBound (proj1_sig (ten_tensor_from_tuple t)) t.
Proof with auto.
  simpl. unfold DomainBound. split.
  destruct (i.<=?.t) eqn:itle. apply tup_le_leb in itle... inversion 1.
  intro H. destruct (i.<=?.t) eqn:itle... apply tup_nle_nleb in itle.
    contradiction.
Qed.


(* The following uniqueness lemma relies on functional extensionality: *)

Lemma ten_tensor_unique : forall (t:Tuple) (x:Tuple -> Value),
  DomainBound x t -> x = proj1_sig (ten_tensor_from_tuple t).
Proof with auto.
  intuition. simpl. apply functional_extensionality. intro i.
  destruct (i.<=?.t) eqn:itle.
    apply tup_le_leb in itle. apply H in itle...
    apply tup_nle_nleb in itle. apply ten_domain_nle_domain in H.
      unfold DomainBound_nle in H. apply H in itle...
Qed.

