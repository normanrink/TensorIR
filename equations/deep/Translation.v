(*****************************************************************************)
(*                                                                           *)
(*  Translation.v                                                            *)
(*                                                                           *)
(*  Tensor expressions are translated to tensors (while preserving tensor    *)
(*  types). Translation is straightforward, based on the tensor operations   *)
(*  defined in 'Tensor.v'.                                                   *)
(*                                                                           *)
(*  The only subtlety in the translation from an expression 'ex' to a tensor *)
(*  is that translation takes place in an environment 'env' that must be     *)
(*  compatible with the typing context 'ctx' in which 'ex' is well-typed.    *)
(*  During translation, the environment 'env' is used to look up the values  *)
(*  of tensor expressions constructed with 'Tens'.                           *)
(*                                                                           *)
(*  Translation gives a meaning, i.e. semantics, to tensor expressions.      *)
(*  Based on this meaning, one can define what it means for two expressions  *)
(*  to be equivalent. This file introduces the equivalence relations "~='"   *)
(*  and "~=" between tensor expressions.                                     *)
(*                                                                           *)
(*  Some simple equivalences between tensor expressions are established.     *)
(*                                                                           *)
(*****************************************************************************)

Require Import TensorIR.Tuple.Tuple.
Require Import TensorIR.Equations.Deep.Expr.
Require Import TensorIR.Equations.Deep.Tensor.



Open Scope list_scope.

(* Environment of tensors must be compatible with a context: *)

Inductive Environment : Context -> Type :=
  | EnvNil  : Environment []
  | EnvCons : forall {t : Tuple} {ctx : Context},
              Tensor t -> 
              Environment ctx -> 
              Environment (t::ctx).


Definition cons_eq_empty_list_False {X : Type} :
  forall {x : X} {l : list X}, [] = x :: l -> False :=
    fun x l eq => let P := fun li => match li with
                                       | [] => True
                                       | _::_ => False
                                     end in
                  eq_ind [] P I _ eq.

Definition in_empty_ctx_False : forall {t : Tuple}, (InCtx t []) -> False :=
  fun t ic => match ic in InCtx t ctx
                       return ([] = ctx -> False)
              with
                | Here    => fun eq => cons_eq_empty_list_False eq 
                | There _ => fun eq => cons_eq_empty_list_False eq 
              end eq_refl.


(* Get a tensor from the given environment 'env' (in a type-safey way): *)

Fixpoint getTensor {t : Tuple} {ctx : Context}
                   (env : Environment ctx) (ic : InCtx t ctx) : Tensor t :=
  match env in Environment ctx' return (InCtx t ctx' -> Tensor t) with
    | EnvNil => 
        fun ic0 => False_rec _ (in_empty_ctx_False ic0)
    | EnvCons tensor env' =>
        fun ic0 => match ic0 
                   in InCtx t0 ctx0 
                   return (match ctx0 with
                             | [] => unit (* bogus *)
                             | t'::ctx0' => (Tensor t' ->
                                             (InCtx t0 ctx0' -> Tensor t0) ->
                                             Tensor t0)
                           end)
                   with
                     | Here       => fun tens getTens => tens
                     | There ic0' => fun tens getTens => getTens ic0'
                   end tensor (@getTensor t _ env')
  end ic.

Close Scope list_scope.


(* Translation of tensor expressions to tensors: *)

Fixpoint translate' {t : Tuple} {ctx : Context} (env : Environment ctx) 
                    (ex : @expr (fun t => Tensor t) ctx t) : Tensor t :=
  match ex with
     | Tens i      => getTensor env i
     | Var tens    => tens
     | Let e f     => let x := translate' env e in translate' env (f x)
     | Add e1 e2   => tens_add (translate' env e1) (translate' env e2)
     | Proj le e   => tens_proj le (translate' env e)
     | Prod e1 e2  => tens_prod (translate' env e1) (translate' env e2)
     | SMul r e    => tens_smul r (translate' env e)
     | Expa d e    => tens_expa d (translate' env e)
     | Diag e      => tens_diag (translate' env e)
     | Transp eq e => tens_transp eq (translate' env e)
     | Red e       => tens_red (translate' env e)
     | Conv le e   => tens_conv le (translate' env e)
  end.

Definition translate {t : Tuple} {ctx : Context} (env : Environment ctx) : 
  Expr ctx t -> Tensor t :=
  fun e => translate' env (e (fun t' => Tensor t')).


(* Equivalence of expressions is defined in terms of equality of the
   translations of expressions to tensors:
   (Note that functional extensionality is 'baked' into the following
   definition of equivalence.)                                        *)

Definition equiv' {t : Tuple} {ctx : Context} :
  expr t -> expr t -> Prop :=
    fun e1 e2 => forall (env : Environment ctx) (i : Tuple),
      pre (translate' env e1) i = pre (translate' env e2) i.

Notation "e1 ~=' e2" := (equiv' e1 e2) (at level 60).

(* The relation "~='" is an equivalence relation: *)

Lemma equiv'_refl {t : Tuple} {ctx : Context} :
  forall (e : @expr _ ctx t), e ~=' e.
Proof with auto.
  unfold equiv'...
Qed.

Lemma equiv'_symm {t : Tuple} {ctx : Context} :
  forall (e1 e2 : @expr _ ctx t), e1 ~=' e2 -> e2 ~=' e1.
Proof with auto.
  unfold equiv'...
Qed.

Lemma equiv'_trans {t : Tuple} {ctx : Context} :
  forall (e1 e2 e3 : @expr _ ctx t), 
    e1 ~=' e2 -> e2 ~=' e3 -> e1 ~=' e3.
Proof with auto.
  intros e1 e2 e3; unfold equiv'; intros eq12 eq23 env i.
  rewrite (eq_trans (eq12 env i) (eq23 env i))...
Qed.


Definition equiv {t : Tuple} {ctx : Context} :
  Expr ctx t -> Expr ctx t -> Prop :=
    fun e1 e2 => forall (env : Environment ctx) (i : Tuple),
      pre (translate env e1) i = pre (translate env e2) i.

Notation "e1 ~= e2" := (equiv e1 e2) (at level 60).

(* The relation "~=" is an equivalence relation: *)

Lemma equiv_refl {t : Tuple} {ctx : Context} :
  forall (e : Expr ctx t), e ~= e.
Proof with auto.
  unfold equiv...
Qed.

Lemma equiv_symm {t : Tuple} {ctx : Context} :
  forall (e1 e2 : Expr ctx t), e1 ~= e2 -> e2 ~= e1.
Proof with auto.
  unfold equiv...
Qed.

Lemma equiv_trans {t : Tuple} {ctx : Context} :
  forall (e1 e2 e3 : Expr ctx t), 
    e1 ~= e2 -> e2 ~= e3 -> e1 ~= e3.
Proof with auto.
  intros e1 e2 e3; unfold equiv; intros eq12 eq23 env i.
  rewrite (eq_trans (eq12 env i) (eq23 env i))...
Qed.


(* Some simple equivalences: *)

Theorem add_equiv_smul' {t : Tuple} {ctx : Context} :
  forall (e : @expr _ ctx t), Add e e ~=' SMul 2 e.
Proof with auto.
  unfold equiv'; intros; simpl.
  unfold tens_add_pre, tens_smul_pre, pre_access.
  destruct (pre (translate' env e) i)...
  unfold plus, mult. rewrite double...
Qed.

Theorem add_equiv_smul {t : Tuple} {ctx : Context} : forall (e : Expr ctx t),
  (fun v => @Add v _ _ (e _) (e _)) ~= (fun v => @SMul v _ _ 2 (e _)).
Proof.
  intro e; apply add_equiv_smul'.
Qed.


Theorem proj_inv_expa' {t : Tuple} {ctx : Context}
                       {m  d : nat} (le : m <= d) :
  forall (e : @expr _ ctx t), e ~=' Proj le (Expa d e).
Proof with auto.
  unfold equiv'; intros; simpl; rewrite (leb_correct _ _ le)...
Qed.

Theorem proj_inv_expa {t : Tuple} {ctx : Context}
                      {m  d : nat} (le : m <= d) :
  forall (e : Expr ctx t),
    (fun v => e v) ~= (fun v => @Proj v _ _ _ _ le (Expa d (e _))).
Proof.
  intro e; apply proj_inv_expa'.
Qed.

Open Scope list_scope.

Theorem diag_transp_eq_diag' {t : Tuple} {d : nat} {ctx : Context} :
  let t' := d::d::t in
  forall (e : @expr _ ctx t') (eq : tup_swap 0 t' = Some t'),
    Diag (Transp eq e) ~=' Diag e.
Proof.
  unfold equiv'; reflexivity.
Qed.

Theorem diag_transp_eq_diag {t : Tuple} {d : nat} {ctx : Context} :
  let t' := d::d::t in
  forall (e : Expr ctx t') (eq : tup_swap 0 t' = Some t'),
    (fun v => @Diag v _ _ _ (Transp eq (e _))) 
    ~= (fun v => @Diag v _ _ _ (e _)).
Proof.
  intros t' e; apply diag_transp_eq_diag'.
Qed.

Close Scope list_scope.


(* The easy equivalence "Red (Expa k e) ~=' SMul (S k) e"
   is not so easy to prove. Two lemmas are required:      *)

Open Scope pre_scope.
Open Scope val_scope.

Lemma smul_1_eq_plus : forall (r : R) (t i : Tuple) (t' : Tensor t),
  tens_smul_pre (1 + r) t' i = (pre t').[i] + tens_smul_pre r t' i.
Proof with auto.
  intuition.
  unfold tens_smul_pre, pre_access, pre.
  destruct (proj1_sig t' i)...
  simpl; rewrite Rmult_plus_distr_r, Rmult_1_l...
Qed.

Lemma red_short : forall (k l m : nat) (t i : Tuple) (t' : Tensor t),
  k <= l -> k <= m -> 
  tens_red_pre k (tens_expa l t') i = tens_red_pre k (tens_expa m t') i.
Proof with auto.
  induction k...
  + intros l m t i t' lel lem.
    simpl; destruct l, m...
    * inversion lel.
    * inversion lem.
    * rewrite (IHk _ _ t i t' (le_Sn_le _ _ lel) (le_Sn_le _ _ lem)).
      apply le_S_n in lel; rewrite (leb_correct _ _ lel). 
      apply le_S_n in lem; rewrite (leb_correct _ _ lem)...
Qed.

Theorem red_expa_eq_smul' {t : Tuple} {d : nat} {ctx : Context} :
  forall (k : nat) (e: @expr _ ctx t), Red (Expa k e) ~=' SMul (INR (S k)) e.
Proof with auto.
  intros k e; induction k; unfold equiv'; intros env i.
  + simpl; unfold tens_smul_pre, pre.
    destruct (proj1_sig (translate' env e) i)...
    simpl; rewrite Rmult_1_l...
  + simpl. 
    rewrite Nat.leb_refl.
    rewrite (red_short _ _ _ _ i (translate' env e) 
                                 (Nat.le_succ_diag_r k) (Nat.le_refl k)).
    rewrite Rplus_comm; rewrite smul_1_eq_plus.
    unfold equiv' in IHk; simpl in IHk; rewrite <- IHk...
Qed.

Theorem red_expa_eq_smul {t : Tuple} {d : nat} {ctx : Context} :
  forall (k : nat) (e: Expr ctx t), 
    (fun v => @Red v _ _ _ (Expa k (e _))) 
    ~= (fun v => @SMul v _ _ (INR (S k)) (e _)).
Proof.
  intros k e. apply (@red_expa_eq_smul' _ d).
Qed.

Close Scope val_scope.
Close Scope pre_scope.


Require Import List.

(* Correctness of the expansion of 'Let' expressions, analogous
   to the treatment in Section 17.2 of "Certified Programming 
   with Dependent Types" by Adam Chlipala, 2013:                *)

Section correct_let_expansion.
  Variable ctx : Context.

  Definition v1 := fun t => Tensor t.
  Definition v2 := (@expr v1 ctx).

  Definition wf_vars {var1 var2 : Tuple -> Set}
                     (vars : list (@varEntry var1 var2))
                     (p : @varEntry var1 var2 -> Prop) :=
    forall ve, In ve vars -> p ve.

  Lemma expandLet'_red_correct' (env : Environment ctx)
                                (vars : list (@varEntry v1 v2))
                                {d k : nat} (le : k <= d) {t : Tuple}
                                (e e' : expr (d::t)) :
    (forall i, pre (translate' env e) i 
                 = pre (translate' env (expandLet' e')) i) ->
    (forall i, tens_red_pre k (translate' env e) i
                 = tens_red_pre k (translate' env (expandLet' e')) i).
  Proof with auto.
    induction k; intuition; simpl; rewrite H...
    + apply le_Sn_le in le.
      rewrite (IHk le H)...
  Qed.

  Lemma expandLet'_conv_correct' (env : Environment ctx)
                                 (vars : list (@varEntry v1 v2))
                                 {m n k : nat} (le : k <= n) {t : Tuple}
                                 (e e' : expr (m::n::t)) :
    (forall i, pre (translate' env e) i 
                 = pre (translate' env (expandLet' e')) i) ->
    (forall i, tens_conv_pre k (translate' env e) i
                 = tens_conv_pre k (translate' env (expandLet' e')) i).
  Proof with auto.
    induction k; intuition; simpl; destruct i...
    + rewrite H.
      apply le_Sn_le in le.
      rewrite (IHk le H)...
  Qed.


  Definition wf_vars_translate' (env : Environment ctx)
                                (vars : list (@varEntry v1 v2)) :=
    wf_vars vars (fun ve => forall i,
                    pre (first ve) i = pre (translate' env (second ve)) i).

  Lemma expandLet'_correct' (env : Environment ctx) {t : Tuple} :
    forall (vars : list varEntry) (e1 : @expr v1 ctx t) (e2 : @expr v2 ctx t),
    wf vars t e1 e2 -> 
      wf_vars_translate' env vars -> forall i,
          pre (translate' env e1) i = pre (translate' env (expandLet' e2)) i.
  Proof with auto.
    intros e1 e2; induction 1; intros Hwfvars i; simpl.
    + auto.
    + unfold tens_add_pre, pre_access.
      rewrite IHwf1... rewrite IHwf2...
    + unfold tens_proj_pre, pre_access.
      rewrite IHwf...
    + unfold tens_prod_pre, pre_access.
      rewrite IHwf1... rewrite IHwf2...
    + unfold tens_smul_pre, pre_access.
      rewrite IHwf...
    + unfold tens_expa_pre.
      destruct i...
      rewrite IHwf...
    + unfold tens_diag_pre.
      destruct i...
    + unfold tens_transp_pre.
      destruct (tup_swap m i)...
    + apply expandLet'_red_correct'...
    + apply Hwfvars in H...
    + remember (translate' env ex) as x.
      remember (expandLet' ex') as x'.
      remember ({| type := tx; first := x; second := x' |} :: vars) as vars'.
      assert(Hwfvars': wf_vars_translate' env vars').
      * unfold wf_vars; intros ve; rewrite Heqvars'; destruct 1.
        - rewrite <- H2; simpl.
          intro i0; rewrite IHwf...
        - apply Hwfvars in H2.
          intro i0; rewrite H2...
      * rewrite (H1 x x')...
        subst...
    + apply expandLet'_conv_correct'...
  Qed.

  Lemma expandLet'_correct {t : Tuple} : forall (e1 : @expr v1 ctx t)
                                                (e2 : @expr v2 ctx t),
    wf [] t e1 e2 -> e1 ~=' expandLet' e2.
  Proof with auto.
    unfold equiv'; intros.
    apply @expandLet'_correct' with (vars:=[])...
    unfold wf_vars; inversion 1.
  Qed.

  Theorem expandLet_correct {t : Tuple} :
    forall (e : Expr ctx t),
      Wf e -> e ~= (expandLet e).
  Proof.
    unfold Wf; intros e HWf.
    apply (expandLet'_correct); apply HWf.
  Qed.
End correct_let_expansion.


Section preserves_wf_let_expansion.
  Variable ctx : Context.
  Variable t : Tuple.

  Variables var1 var2 : Tuple -> Set.

  Definition v3 := (@expr var1 ctx).
  Definition v4 := (@expr var2 ctx).


  Definition wf_vars_wf_vars' (vars  : list (@varEntry v3 v4))
                              (vars' : list (@varEntry var1 var2)) :=
    wf_vars vars (fun ve => wf vars' (type ve) (first ve) (second ve)).

  Lemma expandLet'_preserves_wf' : forall (e1 : @expr v3 ctx t)
                                          (e2 : @expr v4 ctx t)
                                          (vars : list varEntry),
    wf vars t e1 e2 ->
      forall (vars' : list varEntry), wf_vars_wf_vars' vars vars' ->
        wf vars' t (expandLet' e1) (expandLet' e2).
  Proof with auto.
    intros e1 e2 vars Hwf vars' H.
    induction Hwf; try constructor...
    + apply (H {| type := t; first := x1; second := x2 |} H0).
    + apply (H1 (expandLet' ex) (expandLet' ex')); simpl in *.
      intros ve [Hve | HIn]...
      * rewrite <- Hve; apply IHHwf...
  Qed.

  Lemma expandLet'_preserves_wf : forall (e1 : @expr v3 ctx t)
                                         (e2 : @expr v4 ctx t),
    wf [] t e1 e2 -> wf [] t (expandLet' e1) (expandLet' e2).
  Proof with auto.
    intros; apply expandLet'_preserves_wf' with (vars:=[])...
    inversion 1.
  Qed.
End preserves_wf_let_expansion.

Theorem expandLet_preserves_Wf {t : Tuple} {ctx : Context} :
  forall (e : Expr ctx t),
    Wf e -> Wf (expandLet e).
Proof.
  unfold Wf; intros e HWf var1' var2'; unfold expandLet.
  eapply expandLet'_preserves_wf; apply HWf.
Qed.

