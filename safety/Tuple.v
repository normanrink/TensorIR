(*****************************************************************************)
(*                                                                           *)
(*  Tuple.v                                                                  *)
(*                                                                           *)
(*  Tuples of natural numbers are used as multi-indices for indexing         *)
(*  arbitrary tensors. The types of tensors, i.e. their dimensions, are      *)
(*  also represented as tuples of natural numbers.                           *)
(*                                                                           *)
(*  We represent tuples as lists of natural numbers. The operations on       *)
(*  tuples that are defined in this file either make assumptions about the   *)
(*  lengths of operands or have consequences for the lengths of results.     *)
(*  Therefore many lemmas in this file make statements about the structure   *)
(*  (i.e. the length) of tuples.                                             *)
(*                                                                           *)
(*  Of the operations on tuples defined in this file, the comparison of      *)
(*  tuples '.<=.' plays the most central role in the subsequent development  *)
(*  of type safety for tensors.                                              *)
(*                                                                           *)
(*****************************************************************************)


Require Import Arith.
Require Import List.
Require Import PeanoNat.

Import ListNotations.



Definition Tuple := list nat.


Lemma tup_eq_dec : forall (t t':Tuple), {t = t'} + {t <> t'}.
Proof with auto.
  induction t; destruct t'. left... right; inversion 1.
  right; inversion 1.
  destruct (Nat.eq_dec a n).
    subst. destruct (IHt t'). subst; left...
      right; inversion 1...
      right; inversion 1...
Qed.


Lemma tup_length_le_length_append : forall (i j:Tuple),
  length i <= length (i ++ j).
Proof with auto.
  induction i. simpl; intro j; apply (le_0_n (length j)).
  simpl. intro j; apply (le_n_S (length i) (length (i++j)))...
Qed.


Lemma tup_firstn_append : forall (n:nat) (i0 i1:Tuple),
  length i0 = n -> firstn n (i0 ++ i1) = i0.
Proof.
  induction n;
  intros; destruct i0; simpl... trivial. inversion H.
  simpl in H. inversion H.
  rewrite IHn; inversion H; trivial.
Qed.


Lemma tup_skipn_append : forall (n:nat) (i0 i1:Tuple),
  length i0 = n -> skipn n (i0 ++ i1) = i1.
Proof.
  induction n;
  intros; destruct i0; simpl... trivial. inversion H. inversion H.
  apply IHn; inversion H; trivial.
Qed.


(* Elementwise comparison of tuples (both as 'Prop' and as 'bool'): *)

Fixpoint tup_le (t1 t2:Tuple) : Prop :=
  match t1, t2 with
    | [], [] => True
    | (i1::t1'), (i2::t2') => (le i1 i2) /\ (tup_le t1' t2')
    | _,_  => False
  end.


Fixpoint tup_leb (t1 : Tuple) (t2 : Tuple) : bool :=
  match t1, t2 with
    | [], [] => true
    | (i1::t1'), (i2::t2') => (Nat.leb i1 i2) && (tup_leb t1' t2')
    | _, _ => false
  end.

Notation "i .<=.  j" := (tup_le i j)  (at level 40, left associativity).
Notation "i .<=?. j" := (tup_leb i j) (at level 40, left associativity).


Lemma tup_le_dec : forall (t1 t2:Tuple), {t1.<=.t2} + {~t1.<=.t2}.
Proof with auto.
  induction t1; destruct t2... left; simpl...
  pose proof (IHt1 t2) as H; destruct H.
  pose proof (le_dec a n) as lt; destruct lt.
    left; simpl...
    right; simpl; intuition...
    right; simpl; intuition...
Qed.


Lemma tup_le_leb : forall (t1 t2:Tuple),
  t1.<=.t2 <-> t1.<=?.t2 = true.
Proof with auto.
  induction t1; destruct t2; intuition; inversion H.
  simpl. apply Bool.andb_true_iff. split.
    apply Nat.leb_le... apply IHt1...
  apply Bool.andb_true_iff in H1. destruct H1.
    simpl. split. apply Nat.leb_le... apply IHt1...
Qed.


Lemma tup_nle_nleb : forall t1 t2 : Tuple,
  ~t1.<=.t2 <-> t1.<=?.t2 = false.
Proof with auto.
  intuition.
  destruct (t1.<=?.t2) eqn:teq. apply tup_le_leb in teq.
    contradiction. trivial.
  apply tup_le_leb in H0. rewrite H in H0. inversion H0.
Qed.


Lemma tup_le_length_eq : forall (t1 t2: Tuple),
  t1.<=.t2 -> (length t1) = (length t2).
Proof with auto.
  induction t1, t2; inversion 1...
  simpl. apply eq_S. apply IHt1...
Qed.


Lemma tup_le_trans : forall (t1 t2 t3:Tuple),
  t1.<=.t2 -> t2.<=.t3 -> t1.<=.t3.
Proof with auto.
  induction t1, t2; destruct t3; inversion 1...
  intro. destruct H2. simpl. split. apply (Nat.le_trans _ n)...
    apply (IHt1 t2)...
Qed.


Lemma tup_le_refl : forall (t:Tuple),
  t.<=.t.
Proof.
  induction t; simpl; intuition...
Qed.


Lemma tup_le_antisymm : forall (t t':Tuple),
  t.<=.t' -> t'.<=.t -> t = t'.
Proof.
  induction t; destruct t'; inversion 1; trivial.
  intro; destruct H2; apply (IHt _ H1) in H3;
    apply (Nat.le_antisymm _ _ H0) in H2; subst; trivial.
Qed.


Lemma tup_firstn_preserves_le : forall t0 t1 i : Tuple, 
  i.<=.(t0 ++ t1) -> firstn (length t0) i.<=.t0.
Proof with auto.
  induction t0. intuition. simpl...
  simpl. destruct i... intro H. destruct H. simpl. intuition.
  apply (IHt0 t1)...
Qed.

Lemma tup_skipn_preserves_le : forall t0 t1 i : Tuple, 
  i.<=.(t0 ++ t1) -> skipn (length t0) i.<=.t1.
Proof with auto.
  induction t0. intuition.
  simpl. destruct i...
    intro H. inversion H.
    simpl. intuition.
Qed.


(* Swap (viz. transpose) adjacent entries in a tuple.  *)
(* Swapping only yields a defined result if there are  *)
(* more than 'k' entries in the tuple:                 *)

Fixpoint tup_swap (k:nat) (t:Tuple) : option Tuple :=
  match k with
    | 0 => match t with
            | t0 :: t1 :: t' => Some (t1 :: t0 :: t')
            | _ => None
          end
    | S k' => match t with
                | t0 :: t' => match tup_swap k' t' with
                                | Some t'' => Some (t0 :: t'')
                                | _ => None
                              end
                | _ => None
              end
  end.


Lemma tup_swap_defined_some : forall (m:nat) (t:Tuple), 
  S m < length t ->
    exists t', tup_swap m t = Some t'.
Proof with auto.
  induction m. destruct t. inversion 1.
    intro H. destruct t. inversion H. inversion H1. exists (n0::n::t)...
    destruct t. inversion 1.
      intro H. simpl in H. apply Lt.lt_S_n in H. apply IHm in H. destruct H.
      simpl. rewrite H. exists (n::x)...
Qed.


Lemma tup_swap_defined : forall (m:nat) (t:Tuple),
  S m < length t ->
    tup_swap m t <> None.
Proof with auto.
  intuition. apply tup_swap_defined_some in H. destruct H.
  rewrite H in H0. inversion H0.
Qed.


Lemma tup_swap_undefined : forall (m:nat) (t:Tuple),
  length t <= S m -> tup_swap m t = None.
Proof with auto.
  induction m. destruct t... destruct t... intro H. simpl in H.
    inversion H. inversion H1.
  destruct t... intro H. simpl in H. apply le_S_n in H. apply IHm in H.
    simpl. rewrite H...
Qed.


Lemma tup_length_eq_swap_defined' : forall (m:nat) (t0 t1:Tuple),
  length t0 = length t1 ->
    tup_swap m t0 <> None ->
    tup_swap m t1 <> None.
Proof with auto.
  intuition. destruct (Compare_dec.le_lt_dec (length t0) (S m)).
    apply tup_swap_undefined in l...
    rewrite H in l. apply tup_swap_defined in l. contradiction.
Qed.


Lemma tup_length_eq_swap_defined : forall (m:nat) (t0 t1:Tuple),
  length t0 = length t1 ->
  (tup_swap m t0 <> None <-> tup_swap m t1 <> None).
Proof with auto.
  intros. split.
    apply tup_length_eq_swap_defined'...
    apply tup_length_eq_swap_defined'...
Qed.


Lemma tup_swap_nil_undefined : forall (m:nat),
  tup_swap m [] = None.
Proof with auto.
  destruct m...
Qed.


Lemma tup_swap_not_nil : forall (m:nat) (t:Tuple),
  tup_swap m t <> Some [].
Proof with auto.
  intuition. destruct m, t; inversion H.
  destruct t; inversion H1.
  destruct (tup_swap m t); inversion H1.
Qed.


Lemma tup_swap_preserves_length : forall (m:nat) (t t':Tuple),
  tup_swap m t = Some t' -> length t = length t'.
Proof with auto.
  induction m; destruct t; inversion 1.
  destruct t; inversion H...
  destruct (tup_swap m t) eqn:tseq; inversion H1.
  apply IHm in tseq; simpl...
Qed.


Lemma tup_swap_idempotent : forall (m:nat) (i i':Tuple),
  tup_swap m i = Some i' ->
  tup_swap m i' = Some i.
Proof with auto.
  induction m.
  destruct i, i'; intro H; simpl in H; inversion H;
    destruct i; inversion H; subst...
  destruct i, i'; inversion 1;
    destruct (tup_swap m i) eqn:tseq; inversion H1; subst...
      apply IHm in tseq; simpl; rewrite tseq...
Qed.


Lemma tup_swap_preserves_le : forall (m:nat) (i i' j j':Tuple),
  tup_swap m i = Some i' ->
  tup_swap m j = Some j' ->
  i.<=.j ->
    i'.<=.j'.
Proof with auto.
  induction m.
  destruct i, i'; inversion 1.
    apply tup_swap_not_nil in H; contradiction.
    destruct i, i'; inversion H; subst...
      destruct j, j'; inversion 1.
        apply tup_swap_not_nil in H0; contradiction.
          destruct j; inversion H3; subst...
            intro H2; destruct H2 as [H4 [H5 H6]]; simpl; intuition.
  intuition. destruct i, i'. apply tup_swap_not_nil in H; inversion H.
    inversion H. apply tup_swap_not_nil in H; inversion H.
    destruct j, j'... inversion H0. apply tup_swap_not_nil in H0. inversion H0.
      inversion H. destruct (tup_swap m i) eqn:tsmi...
      inversion H3; subst... clear H3.
      inversion H0. destruct (tup_swap m j) eqn:tsmj...
      inversion H3; subst... clear H3.
      apply (IHm _ _ _ _ tsmi) in tsmj;
        destruct H1; simpl; intuition. inversion H3. inversion H3.
Qed.

