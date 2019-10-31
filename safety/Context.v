(*****************************************************************************)
(*                                                                           *)
(*  Context.v                                                                *)
(*                                                                           *)
(*  The static context for typing tensor expressions is modelled as a        *)
(*  partial map from identifiers to tuples. Note that tuples represent       *)
(*  the types of tensor expressions.                                         *)
(*                                                                           *)
(*****************************************************************************)


Require Import TensorIR.Safety.Rlist.
Require Import TensorIR.Safety.Syntax.
Require Import TensorIR.Tuple.Tuple.



Definition Context : Set := Id -> option Tuple.


Definition EmptyContext : Context := fun _ => None.


Definition CtxInDomain (x:Id) (ctx:Context) : Prop := ctx x <> None.

Definition CtxInDomain' (x:Id) (ctx:Context) : Prop := 
  exists (t:Tuple), ctx x = Some t.


Lemma ctx_domain_domain' : forall (x:Id) (ctx:Context),
  CtxInDomain x ctx <-> CtxInDomain' x ctx.
Proof with auto.
  intuition.
  unfold CtxInDomain in H. unfold CtxInDomain'. destruct (ctx x) eqn:xeq.
    exists t... contradiction.
  unfold CtxInDomain' in H. unfold CtxInDomain. destruct H. rewrite H.
    intuition. inversion H0.
Qed.


Definition ExtendContext (ctx:Context) (x:Id) (t:Tuple) : Context :=
  fun x' => if (id_eq_dec x x') then Some t else ctx x'.


Open Scope rlist_scope.

(* Judgement that a context is compatible with a sequence of declarations: *)

Inductive CtxCompatible : Decls -> Context -> Prop :=
  | S_Empty : CtxCompatible [] EmptyContext
  | S_Var   : forall {decls:Decls} {ctx:Context} {x:Id} {t:Tuple},
                CtxCompatible decls ctx ->
                ~(CtxInDomain x ctx) ->
                  CtxCompatible (decls;;DeclVar x t) (ExtendContext ctx x t).

Close Scope rlist_scope.

Lemma ctx_compatible_unique : forall (decls:Decls) (ctx ctx':Context),
  CtxCompatible decls ctx ->
  CtxCompatible decls ctx' ->
    ctx = ctx'.
Proof with auto.
  induction decls; intuition; inversion H; inversion H0; subst; trivial.
  inversion H7; subst.
  assert(ctx0 = ctx1). apply IHdecls... subst...
Qed.


Lemma ctx_extended_lookup : forall (ctx:Context) (x:Id) (t:Tuple),
    (ExtendContext ctx x t) x = Some t.
Proof with auto.
  intros ctx x. unfold ExtendContext. destruct (id_eq_dec x x)...
  contradiction.
Qed.


Lemma ctx_x_in_empty_P : forall (x:Id) (P:Prop), 
  CtxInDomain x EmptyContext -> P.
Proof with auto.
  unfold CtxInDomain. unfold EmptyContext. intuition...
Qed.


Lemma ctx_not_in_domain_none : forall (ctx:Context) (x:Id),
  ~CtxInDomain x ctx <-> ctx x = None.
Proof with auto.
  intuition. unfold CtxInDomain in H. destruct (ctx x)...
  assert(Some t <> None). intro H1. inversion H1.
  contradiction.
Qed.


(* Characterization of compatible contexts. Identifiers appear *)
(* in the domain of the compatible context precisely if they   *)
(* are declared in 'decls':                                    *)

Lemma ctx_declared_in_compatible : forall (decls:Decls) (ctx:Context)
                                          (x:Id) (t:Tuple),
  CtxCompatible decls ctx ->
  (RIn (DeclVar x t) decls <-> ctx x = Some t).
Proof with auto.
  induction decls.
  split.
    inversion 1.
    inversion H. intro H0. unfold EmptyContext in H0. inversion H0.
  destruct a. split; inversion H; subst; intro.
    unfold ExtendContext. inversion H0.
      inversion H1; subst. destruct (id_eq_dec x x)... contradiction.
      apply (IHdecls ctx0 _ _ H4) in H1.
        destruct (id_eq_dec i x)... subst.
          apply ctx_not_in_domain_none in H5. rewrite H5 in H1. inversion H1.
  unfold ExtendContext in H0. destruct (id_eq_dec i x).
      subst. destruct (id_eq_dec x x).
        inversion H0. constructor... contradiction.
      unfold RIn. right. fold (RIn (A:=Decl)).
        apply (IHdecls ctx0 x t0) in H4. apply H4 in H0...
Qed.
