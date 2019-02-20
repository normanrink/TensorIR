(*****************************************************************************)
(*                                                                           *)
(*  Memory.v                                                                 *)
(*                                                                           *)
(*  Memory is modelled as a partial map from identifiers to tensors.         *)
(*  Note that this is a very abstract model of memory.                       *)
(*                                                                           *)
(*****************************************************************************)


Require Import FunctionalExtensionality.

Require Import TensorIR.Safety.Context.
Require Import TensorIR.Safety.Rlist.
Require Import TensorIR.Safety.Syntax.
Require Import TensorIR.Safety.Tensor.
Require Import TensorIR.Safety.Tuple.



Definition Memory : Set := Id -> option Tensor.


Definition EmptyMemory : Memory := fun _ => None. 


Definition MemInDomain (x:Id) (mu:Memory) : Prop := mu x <> None.

Definition MemInDomain' (x:Id) (mu:Memory) : Prop :=
  exists (t:Tensor), mu x = Some t.


Lemma mem_domain_domain' : forall (x:Id) (mu:Memory),
  MemInDomain x mu <-> MemInDomain' x mu.
Proof with auto.
  intuition.
  unfold MemInDomain in H. unfold MemInDomain'. destruct (mu x) eqn:xeq.
    exists t... contradiction.
  unfold MemInDomain' in H. unfold MemInDomain. destruct H. rewrite H.
    intuition. inversion H0.
Qed.


Definition ExtendMemory (mu:Memory) (x:Id) (t:Tensor) : Memory :=
  fun x' => if (id_eq_dec x x') then Some t else mu x'.


(* Judgement that a memory is compatible with a sequence of declarations: *)

Inductive MemCompatible : Decls -> Memory -> Prop :=
  | D_Empty : MemCompatible [] EmptyMemory
  | D_Var   : forall {decls:Decls} {mu:Memory} {x:Id} {t:Tuple},
                MemCompatible decls mu ->
                  MemCompatible (decls;;DeclVar x t)
                                (ExtendMemory mu x (ten_tensor_from_tuple t)).


Lemma mem_compatible_unique : forall (decls:Decls) (mu mu':Memory),
  MemCompatible decls mu ->
  MemCompatible decls mu' ->
    mu = mu'.
Proof with auto.
  induction decls; intuition; inversion H; inversion H0; subst; trivial.
  inversion H7; subst.
  assert(mu0 = mu1). apply IHdecls... subst...
Qed.


Lemma mem_extended_lookup : forall (mu:Memory) (x:Id) (t:Tensor),
  (ExtendMemory mu x t) x = Some t.
Proof with auto.
  intros mu x. unfold ExtendMemory. destruct (id_eq_dec x x)...
  contradiction.
Qed.


(* Since 'VSome' is the only meaningful value, it is easy    *)
(* to define *the* memory that is compatible with a sequence *)
(* of declarations:                                          *)

Fixpoint mem_memory_from_decls (decls:Decls) : Memory :=
  match decls with
    | [] => EmptyMemory
    | (decls';;DeclVar x t) => let mu := mem_memory_from_decls decls' in
                               ExtendMemory mu x (ten_tensor_from_tuple t)
  end.


Lemma mem_from_decls_compatible : forall (decls:Decls),
  MemCompatible decls (mem_memory_from_decls decls).
Proof with auto.
  induction decls. simpl. constructor.
  simpl. destruct a... constructor...
Qed.


Lemma mem_compatible_from_decls : forall (decls:Decls) (mu:Memory),
  MemCompatible decls mu <-> mu = mem_memory_from_decls decls.
Proof with auto.
  intuition. pose proof (mem_from_decls_compatible decls).
  apply (mem_compatible_unique decls)...
  rewrite H. apply mem_from_decls_compatible.
Qed.


Lemma mem_from_decls_lookup :
  forall (decls:Decls) (ctx:Context) (x:Id) (t:Tuple),
  CtxCompatible decls ctx ->
  ctx x = Some t ->
    let mu := mem_memory_from_decls decls in
    mu x = Some (ten_tensor_from_tuple t).
Proof with auto.
  induction decls.
  intros. inversion H. rewrite <- H2 in H0. unfold EmptyContext in H0.
    inversion H0.
  intros ctx x t CompC CtxxEq. destruct a; simpl.
  unfold ExtendMemory. destruct (id_eq_dec i x). subst.
    assert(RIn (DeclVar x t0) (decls;;DeclVar x t0)). simpl. left...
      pose proof (ctx_declared_in_compatible _ ctx x t0 CompC).
      apply H0 in H. rewrite H in CtxxEq. inversion CtxxEq...
    inversion CompC; subst.
      unfold ExtendContext in CtxxEq. destruct (id_eq_dec i x). contradiction.
      pose proof (IHdecls ctx0 x t H3 CtxxEq)...
Qed.


Lemma mem_compatible_lookup :
  forall (decls:Decls) (ctx:Context) (mu:Memory) (x:Id) (t:Tuple),
    (* Compatible context ensures that there is only *)
    (* one declaration of the identifier 'x'.        *)
    CtxCompatible decls ctx -> 
    MemCompatible decls mu ->
    RIn (DeclVar x t) decls ->
      mu x = Some (ten_tensor_from_tuple t).
Proof with auto.
  intros decls ctx mu x t CompC CompM In.
  apply mem_compatible_from_decls in CompM. rewrite CompM.
  apply (mem_from_decls_lookup decls ctx)...
  pose proof (ctx_declared_in_compatible decls ctx x t CompC).
    apply H in In...
Qed.


(* The following theorem relies on functional extensionality: *)

Theorem mem_extend_preserves_from_decls :
  forall (decls:Decls) (ctx:Context) (x:Id) (t:Tuple),
  CtxCompatible decls ctx ->
  ctx x = Some t ->
    let mu := mem_memory_from_decls decls in
    mu = ExtendMemory mu x (ten_tensor_from_tuple t).
Proof with auto.
  intros decls ctx x t CompC CtxxEq.
  apply functional_extensionality. intro y.
  unfold ExtendMemory. destruct (id_eq_dec x y)...
  rewrite (mem_from_decls_lookup decls ctx y t)... subst...
Qed.

