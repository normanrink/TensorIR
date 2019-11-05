(*****************************************************************************)
(*                                                                           *)
(*  Tensor.v                                                                 *)
(*                                                                           *)
(*  A tensor of type 't' (where 't' is a tuple) is defined as a 'PreTensor'  *)
(*  that satisfies the domain predicate 'PreDomainP t'. This means that a    *)
(*  a tensor of type 't' is defined for all tuples that are below 't' (when  *)
(*  tuples are compared with '.<=.').                                        *)
(*                                                                           *)
(*  This file also defines common operations on tensors. Note that these     *)
(*  definitions require proofs that the defined object is indeed a 'Tensor', *)
(*  i.e. satisfies the precidate 'PreDomainP' with a suitable tuple that     *)
(*  specifies the type of the tensor resulting from the defined operation.   *)
(*                                                                           *)
(*****************************************************************************)


Require Import List.

Require Import TensorIR.Equations.Deep.PreTensor.

Require Export TensorIR.Equations.Deep.PreTensor.



(* A 'Tensor' of type 't' is a map from 'Tuple' to 'Value'
   (aka. a 'PreTensor') together with a proof that the domain
   of the map is given by 't':                                *)

Definition Tensor (t : Tuple) := {x : PreTensor | PreDomainP t x}.


Definition pre {t : Tuple} : Tensor t -> PreTensor :=
  fun tens => proj1_sig tens.


(* In the following, tensor operations are defined.
   The definitions always follow the same pattern:
     (1) Define the operation on tensors, yielding a 'PreTensor'.
     (2) Prove a lemma that the domain of the 'PreTensor' from (1) 
         is suitably bounded.
     (3) Combine the results from (1) and (2) to define a 'Tensor'. *)

Open Scope list_scope.
Open Scope pre_scope.
Open Scope val_scope.

(* Some tactics for proof steps that are commonly
   applied in proving the lemmata about domains:  *)

Ltac tens_unfold op := unfold op, pre, pre_access.

Ltac tens_destruct pre Hdom :=
  match goal with
    | t : Tensor _ |- _ => destruct t as [pre Hdom]
  end.

Ltac tens_domain_1 op pre Hdom := 
  tens_unfold op;
  tens_destruct pre Hdom;
  simpl; 
  (* Rewrite PreDomainP into PreDomainP': *)
  autorewrite with core in *; 
  try (unfold PreDomainP' in *); try (unfold pre_access in *);
  split.

Ltac tens_domain_2 op pre1 Hdom1 pre2 Hdom2 := 
  tens_unfold op;
  tens_destruct pre1 Hdom1; tens_destruct pre2 Hdom2;
  simpl;
  (* Rewrite PreDomainP into PreDomainP': *)
  autorewrite with core in *; 
  try (unfold PreDomainP' in *); try (unfold pre_access in *);
  split.


(* Addition of tensors: *)

Definition tens_add_pre {t : Tuple} : Tensor t -> Tensor t -> PreTensor :=
  fun t1 t2 i => (pre t1).[i] + (pre t2).[i].

Lemma tens_add_domain {t : Tuple} : 
  forall (t1 t2 : Tensor t), PreDomainP t (tens_add_pre t1 t2).
Proof with auto.
  intros t1 t2; tens_domain_2 @tens_add_pre p2 H2 p1 H1.
  + destruct 1 as [r Hr].
    apply val_plus_some_inv in Hr; destruct Hr as [rv [rw [Hrv Hrw]]].
    apply H1.
    exists rv...
  + intro le.
    apply H1 in le as H1'; destruct H1' as [rv Hv].
    apply H2 in le as H2'; destruct H2' as [rw Hw].
    exists (rv + rw)%R.
    rewrite Hv, Hw...
Qed.

Definition tens_add {t : Tuple} : Tensor t -> Tensor t -> Tensor t :=
  fun t1 t2 => exist _ (tens_add_pre t1 t2) (tens_add_domain t1 t2).


(* Projection of a tensor, restricting the
   first dimension to a fixed index 'i':   *)

Definition tens_proj_pre {t : Tuple} {d : nat} : nat -> Tensor (d::t) -> 
                                                 PreTensor :=
  fun m t1 i => (pre t1).[m::i].

Lemma tens_proj_domain {t : Tuple} {d m : nat} :
  (m <= d) -> forall (t' : Tensor (d::t)), PreDomainP t (tens_proj_pre m t').
Proof with auto.
  intros le t'; tens_domain_1 @tens_proj_pre p' H'.
  + destruct 1 as [r Hr].
    specialize H' with (m::i).
    assert (HEx: exists r, p'(m::i) = Some r) by (exists r; auto).
    apply H' in HEx; destruct HEx...
  + intro le'; apply H'; constructor...
Qed.

Definition tens_proj {t : Tuple} {d m : nat} (le : m <= d) : 
  Tensor (d::t) -> Tensor t :=
    fun t => exist _ (tens_proj_pre m t) (tens_proj_domain le t).


(* Tensor product (aka. outer product of two tensors): *)

Definition tens_prod_pre {t1 t2 : Tuple} : 
  Tensor t1 -> Tensor t2 -> PreTensor :=
    fun t1' t2' i => (pre t1').[firstn (length t1) i]
                     * (pre t2').[skipn (length t1) i].

Lemma tens_prod_domain {t1 t2 : Tuple} : 
  forall (t1' : Tensor t1) (t2' : Tensor t2), 
    PreDomainP (t1++t2) (tens_prod_pre t1' t2').
Proof with auto.
  intros t1' t2'; tens_domain_2 @tens_prod_pre p2 H2 p1 H1;
  specialize H1 with (firstn (length t1) i);
  specialize H2 with (skipn (length t1) i).
  + destruct 1 as [r Hr]; apply val_mult_some_inv in Hr.
    destruct Hr as [rv [rw [Hrv Hrw]]].
    assert (HExv: exists r, p1 (firstn (length t1) i) = Some r)
      by (exists rv; auto); apply H1 in HExv.
    assert (HExw: exists r, p2 (skipn (length t1) i) = Some r)
      by (exists rw; auto); apply H2 in HExw.
    rewrite <- firstn_skipn with (n := length t1) (l := i).
    apply tup_append_preserves_le...
  + intro le.
    apply tup_firstn_preserves_le in le as le1; apply H1 in le1;
      destruct le1 as [rv Hv].
    apply tup_skipn_preserves_le in le as le2; apply H2 in le2;
      destruct le2 as [rw Hw].
    apply val_mult_some_some with (x := rv) (y := rw)...
Qed.

Definition tens_prod {t1 t2 : Tuple} : 
  Tensor t1 -> Tensor t2 -> Tensor (t1++t2) :=
    fun t1' t2' => exist _ (tens_prod_pre t1' t2') (tens_prod_domain t1' t2').


(* Multiplication of a tensor with a scalar (from the ring/field 'R'): *)

Definition tens_smul_pre {t : Tuple} : R -> Tensor t -> PreTensor :=
  fun r t' i => (Some r) * (pre t' i).

Lemma tens_smul_domain {t : Tuple} : 
  forall (r : R) (t' : Tensor t), PreDomainP t (tens_smul_pre r t').
Proof with auto.
  intros r t'; tens_domain_1 @tens_smul_pre p' H'.
  + destruct 1 as [v Hv].
    destruct (p' i) as [w |] eqn:?.
    * apply H'.
      exists w...
    * inversion Hv.
  + intro le.
    apply H' in le.
    destruct le as [rv Hv].
    exists (r * rv)%R.
    rewrite Hv...
Qed.

Definition tens_smul {t : Tuple} : R -> Tensor t -> Tensor t :=
  fun r t' => exist _ (tens_smul_pre r t') (tens_smul_domain r t').


(* Expansion of a tensor along the first dimension: *)

Definition tens_expa_pre {t : Tuple} : nat -> Tensor t -> PreTensor :=
  fun d t' i => match i with
                  | [] => None
                  | m::j => if m <=? d then (pre t' j) else None
              end.

Lemma tens_expa_domain {t : Tuple}:
  forall (t' : Tensor t) (d : nat), PreDomainP (d::t) (tens_expa_pre d t').
Proof with auto.
  intros t' d; tens_domain_1 @tens_expa_pre p' H'; destruct i.
  1,2: destruct 1 as [r Hr].
  3,4: intro le.
  + inversion Hr.
  + revert Hr.
    pose proof (Nat.leb_spec0 n d) as H; inversion H.
    * intros Hr. 
      assert(HEx: exists r, p' i = Some r) by (exists r; auto).
      apply H' in HEx.
      constructor...
    * inversion 1.
  + inversion le.
  + pose proof (Nat.leb_spec0 n d) as H; inversion H; inversion le.
    * apply H'...
    * contradiction.
Qed.

Definition tens_expa {t : Tuple} (d : nat) : Tensor t -> Tensor (d::t) :=
  fun t' => exist _ (tens_expa_pre d t') (tens_expa_domain t' d).


(* The diagonal along the first two dimensions: *)

Definition tens_diag_pre {t : Tuple} : Tensor t -> PreTensor :=
  fun t' i => match i with
                | []   => None
                | m::j => pre t' (m::m::j)
              end.

Lemma tens_diag_domain {t : Tuple} {d : nat} :
  forall (t' : Tensor (d::d::t)), PreDomainP (d::t) (tens_diag_pre t').
Proof with auto.
  intros t'; tens_domain_1 @tens_diag_pre p' H'; destruct i.
  1,2: destruct 1 as [r Hr].
  3,4: intros le; inversion le...
  + inversion Hr.
  + specialize H' with (n::n::i); apply H'.
    exists r...
  + apply H'; constructor...
Qed.

Definition tens_diag {t : Tuple} {d: nat} :
  Tensor (d::d::t) -> Tensor (d::t) :=
    fun t' => exist _ (tens_diag_pre t') (tens_diag_domain t').


(* Transposition between adjacent dimensions: *)

Definition tens_transp_pre {t : Tuple} : nat -> Tensor t -> PreTensor :=
  fun m t' i => match tup_swap m i with
                  | None => None
                  | Some i' => pre t' i'
                end.

Lemma tens_transp_domain {t0 t1: Tuple} 
                         {m : nat} (eq : tup_swap m t0 = Some t1) :
  forall (t' : Tensor t0), PreDomainP t1 (tens_transp_pre m t').
Proof with auto.
  intros t'; tens_domain_1 @tens_transp_pre p' H';
  remember (tup_swap m i) as tsi; destruct tsi; try (rename t into j).
  3,4: intro le.
  1,2: destruct 1 as [r Hr]; inversion Hr...
  + assert(HEx: exists r, p' j = Some r) by (exists r; auto).
    apply H' in HEx.
    symmetry in Heqtsi; apply tup_swap_idempotent in Heqtsi.
    pose proof (tup_swap_preserves_le m _ _ _ _ Heqtsi eq HEx)...
  + apply tup_swap_idempotent in eq.
    symmetry in Heqtsi.
    apply (tup_swap_preserves_le m _ _ _ _ Heqtsi eq) in le.
    apply H'...
  + apply tup_le_length_eq in le.
    assert(Hnn: tup_swap m t0 <> None) by (rewrite eq; inversion 1).
    rewrite <- (tup_swap_preserves_length m _ _ eq) in le.
    pose proof (tup_length_eq_swap_defined' m t0 i (eq_sym le) Hnn) as H.
    rewrite Heqtsi in H; contradiction.
Qed.

Definition tens_transp {t0 t1 : Tuple} 
                       {m : nat} (eq : tup_swap m t0 = Some t1) :
  Tensor t0 -> Tensor t1 :=
    fun t'' => exist _ (tens_transp_pre m t'') (tens_transp_domain eq t'').


(* Reduction along the first dimension,
   based on addition (aka. contraction): *)

Fixpoint tens_red_pre {t : Tuple} {d : nat} (k : nat) (t' : Tensor (d::t)) :
  PreTensor :=
    fun i => match k with
               | 0    => pre t' (0::i)
               | S k' => pre t' (k::i) + tens_red_pre k' t' i
             end.

Lemma tens_red_defined_1 {t : Tuple} {d : nat} : 
  forall (k : nat) (i : Tuple), (k::i).<=.(d::t) -> 
    forall (t' : Tensor (d::t)), exists r : R, tens_red_pre k t' i = Some r.
Proof with auto.
  intros k i le t'; destruct t' as [p' H'].
  induction k.
  + tens_unfold @tens_red_pre; simpl.
    apply H' in le; unfold pre_access in le.
    destruct (p' (0::i)).
    * exists r...
    * contradiction.
  + (* effectively unfold 'tens_red_pre' once: *)
    unfold tens_red_pre; fold (@tens_red_pre t).
    unfold pre; simpl.
    destruct (IHk (tup_le_Sn_le _ _ _ _ le)) as [s Hs]; rewrite Hs; 
      clear Hs; clear IHk.
    autorewrite with core in H'; apply H' in le; destruct le as [r Hr].
    unfold pre_access in Hr; rewrite Hr.
    exists (r+s)%R...
Qed.

Lemma tens_red_defined_2 {t : Tuple} {d : nat} : 
  forall (k : nat) (i : Tuple) (t' : Tensor (d::t)), 
    (exists r : R, tens_red_pre k t' i = Some r) -> ((k::i).<=.(d::t)).
Proof with auto.
  intros k i t'; destruct t' as [p' H'].
  induction k.
  + tens_unfold @tens_red_pre; simpl; autorewrite with core in H'.
    intro HEx; apply H' in HEx...
  + (* effectively unfold 'tens_red_pre' once: *)
    unfold tens_red_pre; fold (@tens_red_pre t).
    unfold pre; simpl.
    destruct 1 as [r Hr]; apply val_plus_some_inv in Hr; 
      destruct Hr as [rv [rw [Hv Hw]]].
    split.
    * clear IHk; clear Hw; autorewrite with core in H'.
      assert(HEx: exists r, p' (S k::i) = Some r) by (exists rv; auto).
      apply H' in HEx; destruct HEx...
    * rewrite Hw in IHk.
      assert (HEx: exists r, Some rw = Some r) by (exists rw; auto).
      apply IHk in HEx; inversion HEx...
Qed.

Lemma tens_red_domain {t : Tuple} {d : nat} :
  forall (t' : Tensor (d::t)), PreDomainP t (tens_red_pre d t').
Proof.
  intros t'; autorewrite with core; split.
  + apply tens_red_defined_2.
  + intro.
    assert(le: (d::i).<=.(d::t)) by (constructor; auto).
    apply (@tens_red_defined_1 t d d i le).
Qed.

Definition tens_red {t : Tuple} {d : nat} : Tensor (d::t) -> Tensor t :=
  fun t' => exist _ (tens_red_pre d t') (tens_red_domain t').


(* Convolution along the first two dimensions: *)

Fixpoint tens_conv_pre {t : Tuple} (k : nat) (t' : Tensor t) : PreTensor :=
  fun i => match i with
             | [] => None
             | j::i' => match k with
                          | 0    => pre t' (j::0::i')
                          | S k' => (pre t' ((j+(S k'))%nat::(S k')::i'))
                                    + tens_conv_pre k' t' (j::i')
                        end
          end.

Lemma tens_conv_defined_1 {t : Tuple} {m n : nat} (le_nm : n <= m) : 
  forall (k : nat), (k <= n) -> 
    forall (t' : Tensor (m::n::t)) (i : Tuple), i.<=.(m-k::t) ->
      exists r : R, tens_conv_pre k t' i = Some r.
Proof with auto.
  intros k le_kn t' i le_tup; destruct t' as [p' H'].
  induction k; destruct i; inversion le_tup; simpl.
  + autorewrite with core in H'.
    rewrite Nat.sub_0_r in *.
    assert(le: (n0::0::i).<=.(m::n::t)). constructor... constructor...
    apply H' in le...
  + apply tup_le_minus_Sk_le_minus_k in le_tup.
    2: exact (Nat.le_trans _ _ _ le_kn le_nm).
    destruct (IHk (le_Sn_le _ _ le_kn) le_tup) as [r Hr]; clear IHk;
      rewrite Hr; clear Hr.
    assert(le: ((n0 + S k)%nat::(S k)::i).<=.(m::n::t)).
      constructor; pose proof (plus_le_compat_r _ _ (S k) H);
        rewrite (Nat.sub_add _ _ (Nat.le_trans _ _ _ le_kn le_nm)) in H1...
        constructor...
    autorewrite with core in H'; apply H' in le; destruct le as [s Hs];
      unfold pre_access in Hs; rewrite Hs.
    exists (s+r)%R...
Qed.

Lemma tens_conv_defined_2 {t : Tuple} {m n : nat} (le_nm : n <= m) : 
  forall (k : nat), (k <= n) -> 
    forall (t' : Tensor (m::n::t)) (i : Tuple),
      (exists r : R, tens_conv_pre k t' i = Some r) -> i.<=.(m-k::t).
Proof with auto.
  intros k le_kn t' i H.
  induction k; simpl in H; destruct i;
    destruct t' as [p' H']; unfold pre in *; simpl in *; 
    autorewrite with core in H'.
  1,3: destruct H as [r Hr]; inversion Hr.
  + apply H' in H; inversion H as [H0 H1]; inversion H1; intuition.
  + destruct H as [r Hr]; apply val_plus_some_inv in Hr;
      destruct Hr as [rv [rw [Hv Hw]]].
    rewrite Hw in IHk; clear Hw.
    destruct (IHk (le_Sn_le _ _ le_kn)) as [rx Hx].
    * exists rw...
    * intuition...
      assert(HEx: exists r, p' ((n0 + S k)%nat::S k::i) = Some r)
        by (exists rv; auto).
      autorewrite with core in H'; apply H' in HEx; inversion HEx.
      apply Nat.le_add_le_sub_r...
Qed.

Lemma tens_conv_domain {t : Tuple} {m n : nat} (le_nm : n <= m) :
  forall (t' : Tensor (m::n::t)), PreDomainP (m-n::t) (tens_conv_pre n t').
Proof with auto.
  intros t'; autorewrite with core; split.
  + apply (tens_conv_defined_2 le_nm)...
  + apply tens_conv_defined_1...
Qed.

Definition tens_conv {t : Tuple} {m n : nat} (le_nm : n <= m) : 
  Tensor (m::n::t) -> Tensor (m-n::t) :=
    fun t' => exist _ (tens_conv_pre n t') (tens_conv_domain le_nm t').

Close Scope val_scope.
Close Scope pre_scope.
Close Scope list_scope.

