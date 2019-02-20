(*****************************************************************************)
(*                                                                           *)
(*  Semantics.v                                                              *)
(*                                                                           *)
(*  Static and dynamic semantics of the 'TensorIR'.                          *)
(*                                                                           *)
(*  The static semantics consists of the judgement 'HasType' for typing of   *)
(*  expressions, and a number of 'OK' judgements for statements, sequences   *)
(*  of statements, and programs.                                             *)
(*                                                                           *)
(*  The dynamic (evaluation) semantics relies on the function 'eval' for     *)
(*  evaluation of a tensor expression at a multi-index (i.e. tuple) 'i'.     *)
(*  Establishing that 'eval' is a well-defined function (in a compatible     *)
(*  static context and compatible memory) takes up a large fraction of the   *)
(*  present file.                                                            *)
(*                                                                           *)
(*  The evaluation of statements, sequences of statements, and programs is   *)
(*  defined by the 'Step' judgements and the 'Eval_Prog' judgement. These    *)
(*  judgements control how memory is updated when (assignment) statements,   *)
(*  sequences of statements, and programs are evaluated.                     *)
(*  (Note that program evaluation always starts with compatible memory,      *)
(*  cf. the definition of 'Eval_Prog'.)                                      *)
(*                                                                           *)
(*****************************************************************************)


Require Import List.
Require Import PeanoNat.

Import ListNotations.

Require Import TensorIR.Safety.Context.
Require Import TensorIR.Safety.Memory.
Require Import TensorIR.Safety.Rlist.
Require Import TensorIR.Safety.Syntax.
Require Import TensorIR.Safety.Tensor.
Require Import TensorIR.Safety.Tuple.



(* Judgement for well-typed expressions: *)

Inductive HasType : Context -> Expr -> Tuple -> Prop :=
  | T_Var : forall (ctx:Context) (x:Id) (t:Tuple),
      ctx x = Some t ->
      HasType ctx (Var x) t
  | T_Prod : forall (ctx:Context) (e0 e1:Expr) (t0 t1:Tuple),
      HasType ctx e0 t0 ->
      HasType ctx e1 t1 ->
      HasType ctx (Prod e0 e1) (t0++t1)
  | T_Add : forall (ctx:Context) (e0 e1:Expr) (t:Tuple),
      HasType ctx e0 t ->
      HasType ctx e1 t ->
      HasType ctx (Add e0 e1) t
  | T_Mul : forall (ctx:Context) (e0 e1:Expr) (t:Tuple),
      HasType ctx e0 t ->
      HasType ctx e1 t ->
      HasType ctx (Mul e0 e1) t
  | T_SMul : forall (ctx:Context) (e0 e1:Expr) (t:Tuple),
      HasType ctx e0 []%list ->
      HasType ctx e1 t ->
      HasType ctx (Mul e0 e1) t
  | T_Transp : forall (ctx:Context) (m:nat) (e:Expr) (t t':Tuple) ,
      HasType ctx e t ->
      tup_swap m t = Some t' ->
      HasType ctx (Transp m e) t'
  | T_Contr : forall (ctx:Context) (e:Expr) (t:Tuple) (d:nat),
      HasType ctx e (d::d::t) ->
      HasType ctx (Contr e) t
  | T_Proj : forall (ctx:Context) (e:Expr) (t:Tuple) (d m:nat),
      HasType ctx e (d::t) ->
      m <= d ->
      HasType ctx (Proj m e) t
  | T_Diag : forall (ctx:Context) (e:Expr) (t:Tuple) (d:nat),
      HasType ctx e (d::d::t) ->
      HasType ctx (Diag e) (d::t)
  | T_Expand : forall (ctx:Context) (e:Expr) (t:Tuple) (d:nat),
      HasType ctx e t ->
      HasType ctx (Expand d e) (d::t).

Hint Constructors HasType.


(* Judgements for well-formed statements, *)
(* sequences of statements, and programs: *)

Inductive OK_Stmt : Context -> Stmt -> Prop :=
  | OK_stmt : forall (ctx:Context) (x:Id) (t:Tuple) (e:Expr),
      CtxInDomain x ctx ->
      ctx x = Some t ->
      HasType ctx e t ->
        OK_Stmt ctx (StmtAssign x e).


Inductive OK_Seq : Context -> Stmts -> Prop :=
  | OK_empty : forall (ctx : Context),
      OK_Seq ctx []
  | OK_seq : forall (ctx:Context) (stmt:Stmt) (stmts:Stmts),
      OK_Seq ctx stmts ->
      OK_Stmt ctx stmt ->
        OK_Seq ctx (stmts;;stmt).


Inductive OK_Prog : Prog -> Prop :=
  | OK_prog : forall (ctx:Context) (decls:Decls) (stmts:Stmts),
      CtxCompatible decls ctx ->
      OK_Seq ctx stmts ->
        OK_Prog (decls, stmts).


(* A variable 'x' that is assigned to in a sequence of statements that *)
(* satisfies 'OK_Seq' necessarily appears in the static context:       *)

Lemma sem_ok_id_in_stmt : 
  forall (decls:Decls) (ctx:Context) (x:Id) (e:Expr) (stmts:Stmts),
    CtxCompatible decls ctx ->
    OK_Seq ctx stmts ->
    RIn (StmtAssign x e) stmts ->
      CtxInDomain x ctx.
Proof with auto.
  intros decls ctx x e stmts Comp OK.
  induction OK.
    inversion 1.
    intuition. inversion H0...
      subst. inversion H...
Qed.


(* If the assignment 'x = e' occurs in a sequence of statements that *)
(* satisfies 'OK_Seq', then both 'x' and 'e' are well-typed:         *)

Lemma sem_typable_expr_in_stmt :
  forall (decls:Decls) (ctx:Context) (x:Id) (e:Expr) (stmts:Stmts),
    CtxCompatible decls ctx ->
    OK_Seq ctx stmts ->
    RIn (StmtAssign x e) stmts ->
      exists (t:Tuple) , ctx x = Some t /\ HasType ctx e t.
Proof with auto.
  intros decls ctx x e stmts Comp OK.
  induction OK.
    inversion 1.
    intuition. inversion H0...
      subst. inversion H; subst. exists t...
Qed.


(* In order to evaluate expressions, the function 'eval' (to be defined *)
(* below) must compute types of (sub-)expressions. For this purpose,    *)
(* a function that computes the type of an expression is defined here.  *)

Fixpoint compute_type (ctx:Context) (e:Expr) : option Tuple :=
  match e with
    | Var x => ctx x
    | Prod e0 e1 => match compute_type ctx e0, compute_type ctx e1 with
                      | Some t0, Some t1 => Some (t0 ++ t1)
                      | _, _ => None
                    end
    | Add e0 e1 => match compute_type ctx e0, compute_type ctx e1 with
                      | Some t0, Some t1 => if (tup_eq_dec t0 t1)
                                               then Some t0
                                               else None
                      | _, _ => None
                    end
    | Mul e0 e1 => match compute_type ctx e0, compute_type ctx e1 with
                      | Some []%list, Some t => Some t
                      | Some t0, Some t1 => if (tup_eq_dec t0 t1)
                                               then Some t0
                                               else None
                      | _, _ => None
                    end
    | Transp m e => match compute_type ctx e with
                      | Some t => tup_swap m t
                      | _ => None
                    end
    | Contr e => match compute_type ctx e with
                   | Some (d0::d1::t) => if (d0 =? d1)
                                            then Some t
                                            else None
                   | _ => None
                 end
    | Proj m e => match compute_type ctx e with
                   | Some (d::t) => if (m <=? d)
                                       then Some t
                                       else None
                   | _ => None
                 end
    | Diag e => match compute_type ctx e with
                  | Some (d0::d1::t) => if (d0 =? d1)
                                           then Some (d1::t)
                                           else None
                  | _ => None
                 end
    | Expand m e => match compute_type ctx e with
                      | Some d => Some (m::d)
                      | _ => None
                    end
  end.


(* The function 'compute_type' agrees with the judgement 'HasType': *)

Lemma sem_typing_computable : forall (ctx:Context) (e:Expr) (t:Tuple),
    HasType ctx e t <-> compute_type ctx e = Some t.
Proof with auto.
  split.
    (* -> *)
    generalize dependent ctx; generalize dependent t. induction e;
    intros t ctx H; inversion H; subst; simpl...
      (* Prod *)
      apply IHe1 in H3; rewrite H3; apply IHe2 in H5; rewrite H5...
      (* Add *)
      apply IHe1 in H3; rewrite H3; apply IHe2 in H5; rewrite H5...
        destruct (tup_eq_dec)... contradiction.
      (* Mul *)
      apply IHe1 in H3; rewrite H3; apply IHe2 in H5; rewrite H5...
        destruct t... destruct (tup_eq_dec (n::t) (n::t))... contradiction.
      apply IHe1 in H3; rewrite H3; apply IHe2 in H5; rewrite H5...
      (* Transp *)
      apply IHe in H3; rewrite H3...
      (* Contr *)
      apply IHe in H2; rewrite H2... destruct (d =? d) eqn:deq...
        apply Nat.eqb_neq in deq; contradiction. 
      (* Proj *)
      apply IHe in H3; rewrite H3... apply Nat.leb_le in H5. rewrite H5...
      (* Diag *)
      apply IHe in H2; rewrite H2... destruct (d =? d) eqn:deq...
        apply Nat.eqb_neq in deq; contradiction.
      (* Expand *)
      apply IHe in H4; rewrite H4...
    (* <- *)
    generalize dependent ctx; generalize dependent t. induction e;
    intros t ctx H; inversion H; subst; simpl...
      (* Prod *)
      destruct (compute_type ctx e1) eqn:e1eq. apply IHe1 in e1eq.
        destruct (compute_type ctx e2) eqn:e2eq. apply IHe2 in e2eq.
        inversion H1; subst... inversion H1. inversion H1.
      (* Add *)
      destruct (compute_type ctx e1) eqn:e1eq. apply IHe1 in e1eq.
        destruct (compute_type ctx e2) eqn:e2eq. apply IHe2 in e2eq.
        destruct (tup_eq_dec t0 t1)...
        inversion H1; subst... inversion H1. inversion H1. inversion H1.
      (* Mul *)
      destruct (compute_type ctx e1) eqn:e1eq... apply IHe1 in e1eq.
        destruct (compute_type ctx e2) eqn:e2eq... apply IHe2 in e2eq.
        destruct t0... inversion H1; subst...
        destruct (tup_eq_dec (n::t0) t1)... inversion H1; subst.
        constructor...
        inversion H1.
        destruct t0... inversion H1; subst... inversion H1. inversion H1.
      (* Transp *)
      destruct (compute_type ctx e) eqn:eeq. apply IHe in eeq.
        apply T_Transp with (t:=t0)... inversion H1.
      (* Contr *)
      destruct (compute_type ctx e) eqn:eeq. apply IHe in eeq.
        destruct t0. inversion H1.
        destruct t0. inversion H1.
        destruct (Nat.eq_dec n n0)... subst...
        destruct (n0 =? n0). inversion H1; subst.
        apply T_Contr with (d:=n0)... inversion H1.
        apply Nat.eqb_neq in n1. rewrite n1 in H1.
        inversion H1. inversion H1.
      (* Proj *)
      destruct (compute_type ctx e) eqn:eeq. apply IHe in eeq.
        destruct t0. inversion H1.
        destruct (n <=? n0) eqn:nn0eq. inversion H1; subst...
        apply T_Proj with (d:=n0)... apply Nat.leb_le in nn0eq...
        inversion H1. inversion H1.
      (* Diag *)
      destruct (compute_type ctx e) eqn:eeq. apply IHe in eeq.
        destruct t0. inversion H1.
        destruct t0. inversion H1.
        destruct (n =? n0) eqn:nn0eq. apply Nat.eqb_eq in nn0eq.
          inversion H1. subst. apply T_Diag...
          inversion H1. inversion H1.
      (* Expand *)
      destruct (compute_type ctx e) eqn:eeq. apply IHe in eeq.
        destruct t; inversion H1; subst.
        apply T_Expand...
        inversion H1.
Qed.


(* Contraction of the first two dimensions in a tensor up to bound 'b'. *)
(* Bear in mind that 'VSome' is the only meaningful entry in a tensor,  *)
(* and therefore, whenever an operation encounters a 'VUndef', the      *)
(* result of the whole operation is a 'VUndef':                         *)

Fixpoint sem_contract (i:Tuple) (b:nat) (f:Tuple -> Value) : Value :=
  match b with
    | 0 => VSome
    | S b' => match f (b'::b'::i) with
                | VSome => sem_contract i b' f
                | _ => VUndef
              end
  end.


(* Evaluation of tensor expressions in a static context 'ctx' *)
(* and under the memory 'mu':                                 *)

Fixpoint eval (ctx:Context) (mu:Memory) (e:Expr) (i:Tuple) : Value :=
  match e with
    | Var x => match mu x with
                | None => VUndef
                | Some tensor => proj1_sig tensor i
              end
    | Prod e1 e2 => match compute_type ctx e1, compute_type ctx e2 with
                      | Some t1, Some t2 =>
                          let i1 := List.firstn (length t1) i in
                          let i2 := List.skipn (length t1) i in
                          if ((length i1 =? length t1) &&
                              (length i2 =? length t2))%bool
                          then match eval ctx mu e1 i1,
                                     eval ctx mu e2 i2 with
                                 | VSome, VSome => VSome
                                 | _, _ => VUndef
                               end
                          else VUndef
                      | _, _ => VUndef
                    end 
    | Add e1 e2 => match eval ctx mu e1 i, eval ctx mu e2 i with
                     | VSome, VSome => VSome
                     | _, _ => VUndef
                   end
    | Mul e1 e2 => match compute_type ctx e1 with
                     | Some []%list => match eval ctx mu e1 []%list,
                                             eval ctx mu e2 i with
                                         | VSome, VSome => VSome
                                         | _, _ => VUndef
                                   end
                     | _ => match eval ctx mu e1 i, eval ctx mu e2 i with
                              | VSome, VSome => VSome
                              | _, _ => VUndef
                            end
                   end
    | Transp m e => match tup_swap m i with
                      | Some i' => eval ctx mu e i'
                      | None => VUndef
                      end
    | Contr e => match compute_type ctx e with
                   | Some (d::_) => let x := (fun j => eval ctx mu e j) in
                                    sem_contract i (S d) x
                   | _ => VUndef
                 end
    | Proj m e => eval ctx mu e (m::i)
    | Diag e => match i with 
                  | i0::_ => eval ctx mu e (i0::i)
                  | _ => VUndef
                end
    | Expand m e => match i with 
                    | i0::i' => eval ctx mu e i'
                    | _ => VUndef
                  end
  end.


(* Well-definedness of 'eval', one lemma for each constructor of 'Expr' *)
(* (except for the first contructor 'Var', which needs two lemmas):     *)

Lemma sem_tensor_variable_defined :
  forall (decls:Decls) (ctx:Context) (mu:Memory) (x:Id) (t:Tuple),
  CtxCompatible decls ctx ->
  MemCompatible decls mu ->
  HasType ctx (Var x) t ->
    exists tens, (mu x = Some tens /\ DomainBound (proj1_sig tens) t).
Proof with auto.
  induction decls; intros ctx mu x t CompC CompM HT.
    inversion CompC. subst. inversion HT. inversion H1.
    inversion CompC; inversion CompM; subst. inversion H6; subst.
      destruct (id_eq_dec x x0).
        subst. rewrite mem_extended_lookup.
          exists (ten_tensor_from_tuple t0). intuition...
          inversion HT. rewrite ctx_extended_lookup in H2.
          inversion H2. subst. simpl.
          unfold DomainBound. intuition... destruct (i.<=?.t) eqn:itle...
          apply tup_le_leb in itle... inversion H.
          apply tup_le_leb in H. rewrite H...
        unfold ExtendMemory. destruct (id_eq_dec x0 x)...
          symmetry in e; contradiction. apply (IHdecls ctx0)...
          inversion HT. subst. constructor.
          unfold ExtendContext in H2. destruct (id_eq_dec x0 x).
          contradiction. assumption.
Qed.


Lemma sem_eval_well_defined_Var : 
  forall (x:Id) (decls:Decls) (ctx:Context) (mu:Memory) (t:Tuple),
    CtxCompatible decls ctx ->
    MemCompatible decls mu ->
    HasType ctx (Var x) t ->
      forall (i:Tuple), i.<=.t -> eval ctx mu (Var x) i = VSome.
Proof with auto.
  intros x decls ctx mu t CompC CompM HT i ilet.
  pose proof (sem_tensor_variable_defined decls ctx mu x t CompC CompM HT).
  destruct H as [tens [muxeq DomBnd]].
  simpl. rewrite muxeq.
  assert(proj1_sig tens i = VSome). apply DomBnd...
  rewrite H...
Qed.


Lemma sem_eval_well_defined_Prod : 
  forall (e1 e2:Expr) (decls:Decls) (ctx:Context) (mu:Memory) (t1 t2:Tuple),
    CtxCompatible decls ctx ->
    MemCompatible decls mu ->
    HasType ctx e1 t1 ->
    (forall (i:Tuple), i.<=.t1 -> eval ctx mu e1 i = VSome) ->
    HasType ctx e2 t2 ->
    (forall (i:Tuple), i.<=.t2 -> eval ctx mu e2 i = VSome) ->
      forall (i:Tuple), i.<=.(t1++t2) -> eval ctx mu (Prod e1 e2) i = VSome.
Proof with auto.
  intros e1 e2 decls ctx mu t1 t2 CompC CompM Ht1 Eval1 Ht2 Eval2 i le.
  apply sem_typing_computable in Ht1. apply sem_typing_computable in Ht2.
  simpl. rewrite Ht1. rewrite Ht2.
  pose proof (tup_firstn_preserves_le _ _ _ le).
  pose proof (tup_le_length_eq _ _ H). apply Nat.eqb_eq in H0. rewrite H0.
  pose proof (tup_skipn_preserves_le _ _ _ le).
  pose proof (tup_le_length_eq _ _ H1). apply Nat.eqb_eq in H2. rewrite H2.
  simpl.
  rewrite (Eval1 (firstn (length t1) i) H).
  rewrite (Eval2 (skipn (length t1) i) H1)...
Qed.


Lemma sem_eval_well_defined_Add : 
  forall (e1 e2:Expr) (decls:Decls) (ctx:Context) (mu:Memory) (t:Tuple),
    CtxCompatible decls ctx ->
    MemCompatible decls mu ->
    HasType ctx e1 t ->
    (forall (i:Tuple), i.<=.t -> eval ctx mu e1 i = VSome) ->
    HasType ctx e2 t ->
    (forall (i:Tuple), i.<=.t -> eval ctx mu e2 i = VSome) ->
      forall (i:Tuple), i.<=.t -> eval ctx mu (Add e1 e2) i = VSome.
Proof with auto.
  intros e1 e2 decls ctx mu t CompC CompM Ht1 Eval1 Ht2 Eval2 i le.
  simpl. rewrite (Eval1 i le). rewrite (Eval2 i le)...
Qed.


Lemma sem_eval_well_defined_Mul : 
  forall (e1 e2:Expr) (decls:Decls) (ctx:Context) (mu:Memory) (t:Tuple),
    CtxCompatible decls ctx ->
    MemCompatible decls mu ->
    HasType ctx e1 t ->
    (forall (i:Tuple), i.<=.t -> eval ctx mu e1 i = VSome) ->
    HasType ctx e2 t ->
    (forall (i:Tuple), i.<=.t -> eval ctx mu e2 i = VSome) ->
      forall (i:Tuple), i.<=.t -> eval ctx mu (Mul e1 e2) i = VSome.
Proof with auto.
  intros e1 e2 decls ctx mu t CompC CompM Ht1 Eval1 Ht2 Eval2 i le.
  apply sem_typing_computable in Ht1.
  simpl. rewrite Ht1. destruct t.
    rewrite (Eval1 []%list (tup_le_refl []%list)). rewrite (Eval2 i le)...
    rewrite (Eval1 i le). rewrite (Eval2 i le)...
Qed.


Lemma sem_eval_well_defined_SMul : 
  forall (e1 e2:Expr) (decls:Decls) (ctx:Context) (mu:Memory) (t:Tuple),
    CtxCompatible decls ctx ->
    MemCompatible decls mu ->
    HasType ctx e1 []%list ->
    (forall (i:Tuple), i.<=.[]%list -> eval ctx mu e1 i = VSome) ->
    HasType ctx e2 t ->
    (forall (i:Tuple), i.<=.t -> eval ctx mu e2 i = VSome) ->
      forall (i:Tuple), i.<=.t -> eval ctx mu (Mul e1 e2) i = VSome.
Proof with auto.
  intros e1 e2 decls ctx mu t CompC CompM Ht1 Eval1 Ht2 Eval2 i le.
  apply sem_typing_computable in Ht1.
  simpl. rewrite Ht1.
  rewrite (Eval1 []%list (tup_le_refl []%list)). rewrite (Eval2 i le)...
Qed.


Lemma sem_eval_well_defined_Transp : 
  forall (e:Expr) (decls:Decls) (ctx:Context) (mu:Memory) (t t':Tuple) (m:nat),
    CtxCompatible decls ctx ->
    MemCompatible decls mu ->
    HasType ctx e t ->
    (forall (i:Tuple), i.<=.t -> eval ctx mu e i = VSome) ->
    tup_swap m t = Some t' ->
      forall (i:Tuple), i.<=.t' -> eval ctx mu (Transp m e) i = VSome.
Proof with auto.
  intros e decls ctx mu t t' m CompC CompM Ht Ev Swap i le.
  apply tup_swap_idempotent in Swap.
  simpl. destruct (tup_swap m i) eqn:tsweq.
    pose proof (tup_swap_preserves_le m _ _ _ _ tsweq Swap le).
      rewrite (Ev t0 H)...
    apply tup_le_length_eq in le.
      assert(tup_swap m t' <> None). intuition...
        rewrite Swap in H. inversion H.
      apply (tup_length_eq_swap_defined m _ _ le) in H. contradiction.
Qed.


Lemma sem_eval_well_defined_Contr : 
  forall (e:Expr) (decls:Decls) (ctx:Context) (mu:Memory) (t:Tuple) (d:nat),
    CtxCompatible decls ctx ->
    MemCompatible decls mu ->
    HasType ctx e (d::d::t) ->
    (forall (i:Tuple), i.<=.(d::d::t) -> eval ctx mu e i = VSome) ->
      forall (i:Tuple), i.<=.t -> eval ctx mu (Contr e) i = VSome.
Proof with auto.
  intros e decls ctx mu t d CompC CompM Ht Ev i le.
  apply sem_typing_computable in Ht. simpl. rewrite Ht.
  assert((d::d::i).<=.(d::d::t)). simpl; intuition...
  rewrite (Ev _ H). clear H.
  clear Ht. induction d...
    unfold sem_contract. fold sem_contract.
    assert((d::d::i).<=.((S d)::(S d)::t)). simpl; intuition...
    rewrite (Ev _ H).
    apply IHd. intuition... apply Ev. apply (tup_le_trans _ (d::d::t))...
      simpl; intuition... apply tup_le_refl.
Qed.


Lemma sem_eval_well_defined_Proj :
  forall (e:Expr) (decls:Decls) (ctx:Context) (mu:Memory) (t:Tuple) (d m:nat),
    CtxCompatible decls ctx ->
    MemCompatible decls mu ->
    HasType ctx e (d::t) ->
    (forall (i:Tuple), i.<=.(d::t) -> eval ctx mu e i = VSome) ->
    m <= d ->
      forall (i:Tuple), i.<=.t -> eval ctx mu (Proj m e) i = VSome.
Proof with auto.
  intros e decls ctx mu t d m CompC CompM Ht Ev mdle i le.
  apply sem_typing_computable in Ht. simpl. apply Ev. simpl. intuition.
Qed.


Lemma sem_eval_well_defined_Diag :
  forall (e:Expr) (decls:Decls) (ctx:Context) (mu:Memory) (t:Tuple) (d:nat),
    CtxCompatible decls ctx ->
    MemCompatible decls mu ->
    HasType ctx e (d::d::t) ->
    (forall (i:Tuple), i.<=.(d::d::t) -> eval ctx mu e i = VSome) ->
      forall (i:Tuple), i.<=.(d::t) -> eval ctx mu (Diag e) i = VSome.
Proof with auto.
  intros e decls ctx mu t d CompC CompM Ht Ev i le.
  simpl. destruct i; inversion le.
  apply Ev. simpl. intuition.
Qed.


Lemma sem_eval_well_defined_Expand :
  forall (e:Expr) (decls:Decls) (ctx:Context) (mu:Memory) (t:Tuple) (d:nat),
    CtxCompatible decls ctx ->
    MemCompatible decls mu ->
    HasType ctx e t ->
    (forall (i:Tuple), i.<=.t -> eval ctx mu e i = VSome) ->
      forall (i:Tuple), i.<=.(d::t) -> eval ctx mu (Expand d e) i = VSome.
Proof with auto.
  intros e decls ctx mu t d CompC CompM Ht Ev i le.
  apply sem_typing_computable in Ht. simpl. destruct i; inversion le.
  apply Ev...
Qed.

(* Finally, well-definedness of 'eval': *)

Lemma sem_eval_well_defined' : 
  forall (decls:Decls) (ctx:Context) (mu:Memory) (e:Expr) (t:Tuple),
    CtxCompatible decls ctx ->
    MemCompatible decls mu ->
    HasType ctx e t ->
      forall (i:Tuple), i.<=.t -> eval ctx mu e i = VSome.
Proof with auto.
  intros decls ctx mu. induction e.
    (* Var *)
    apply sem_eval_well_defined_Var.
    (* Prod *)
    intros t CompC CompM Ht i le. inversion Ht. subst.
    apply (sem_eval_well_defined_Prod e1 e2 decls ctx mu t0 t1)...
    apply IHe1... apply IHe2...
    (* Add *)
    intros t CompC CompM Ht i le. inversion Ht. subst.
    apply (sem_eval_well_defined_Add e1 e2 decls ctx mu t)...
    apply IHe1... apply IHe2...
    (* Mul *)
    intros t CompC CompM Ht i le. inversion Ht.
      subst. apply (sem_eval_well_defined_Mul e1 e2 decls ctx mu t)...
        apply IHe1... apply IHe2...
      subst. apply (sem_eval_well_defined_SMul e1 e2 decls ctx mu t)...
        apply IHe1... apply IHe2...
    (* Transp *)
    intros t CompC CompM Ht i le. inversion Ht. subst.
    apply (sem_eval_well_defined_Transp e decls ctx mu t0 t)...
    apply IHe...
    (* Contr *)
    intros t CompC CompM Ht i le. inversion Ht. subst.
    apply (sem_eval_well_defined_Contr e decls ctx mu t d)...
    apply IHe...
    (* Proj *)
    intros t CompC CompM Ht i le. inversion Ht. subst.
    apply (sem_eval_well_defined_Proj e decls ctx mu t d)...
    apply IHe...
    (* Diag *)
    intros t CompC CompM Ht i le. inversion Ht. subst.
    apply (sem_eval_well_defined_Diag e decls ctx mu t0 d)...
    apply IHe...
    (* Expand *)
    intros t CompC CompM Ht i le. inversion Ht. subst.
    apply (sem_eval_well_defined_Expand e decls ctx mu t0 n)...
    apply IHe...
Qed.


(* The following theorem re-states well-definedness        *)
(* of 'eval' for all statements in a well-formed program:  *)

Theorem sem_eval_well_defined :
  forall (decls:Decls) (ctx:Context) (mu:Memory) (stmts:Stmts) (x:Id) (e:Expr),
    CtxCompatible decls ctx ->
    MemCompatible decls mu ->
    OK_Prog (decls, stmts) -> 
    RIn (StmtAssign x e) stmts ->
      (exists t , ctx x = Some t /\ HasType ctx e t /\
        (forall i, i.<=.t -> eval ctx mu e i = VSome)).
Proof with auto.
  intros decls ctx mu stmts x e CompC CompM OK In.
  inversion OK. subst.
  pose proof (ctx_compatible_unique _ _ _ CompC H1). subst.
  pose proof (sem_typable_expr_in_stmt decls ctx0 x e stmts CompC H2 In).
  destruct H as [t [ctxxeq ht]].
  exists t. intuition.
    apply (sem_eval_well_defined' decls ctx0 mu e t)...
Qed.


(* Dynamic semantics, i.e. evaluation of statements, *)
(* sequences of statements, and programs:            *)

Inductive Step_Stmt : Context -> Memory -> Stmt -> Memory -> Prop :=
  | Step_stmt : forall (ctx:Context) (mu:Memory) (x:Id) (e:Expr)
                       (t:Tuple) (tens:Tensor),
                  ctx x = Some t -> 
                  mu x = Some tens ->
                  DomainBound (proj1_sig tens) t ->
                  (forall i : Tuple, i.<=.t -> eval ctx mu e i = VSome) ->
                    Step_Stmt ctx mu (StmtAssign x e)
                                     (ExtendMemory mu x
                                       (ten_tensor_from_tuple t)).


Inductive Step_Seq : Context -> Memory -> Stmts -> Memory -> Prop := 
  | Step_empty : forall (ctx:Context) (mu:Memory),
                   Step_Seq ctx mu [] mu
  | Step_seq : forall (ctx:Context) (stmt:Stmt) (stmts:Stmts)
                      (mu mu' mu'':Memory),
                 Step_Seq ctx mu stmts mu' ->
                 Step_Stmt ctx mu' stmt mu'' ->
                   Step_Seq ctx mu (stmts;;stmt) mu''.


Inductive Eval_Prog : Prog -> Memory -> Prop :=
  | Eval_prog : forall (ctx:Context) (decls:Decls) (stmts:Stmts) 
                       (mu mu':Memory),
                  CtxCompatible decls ctx ->
                  MemCompatible decls mu ->
                  Step_Seq ctx mu stmts mu' ->
                    Eval_Prog (decls, stmts) mu'.


(* The following lemmas show that evaluation of  *)
(* statements preserves the shape of the memory. *)

Lemma sem_step_stmt : forall (ctx:Context) (decls:Decls) (stmt:Stmt),
  CtxCompatible decls ctx ->
  OK_Stmt ctx stmt ->
    Step_Stmt ctx (mem_memory_from_decls decls) stmt
              (mem_memory_from_decls decls).
Proof with auto.
  intros ctx decls stmt CompC OK.
  destruct stmt. inversion OK. subst.
  pose proof (mem_extend_preserves_from_decls decls ctx i t CompC H3).
  rewrite H at 2.
  apply Step_stmt with (tens := ten_tensor_from_tuple t)...
  apply (mem_from_decls_lookup decls ctx)...
  apply ten_from_tuple_bound.
  apply (sem_eval_well_defined' decls)...
    apply mem_from_decls_compatible.
Qed.


Lemma sem_step_seq : forall (ctx:Context) (decls:Decls) (stmts:Stmts),
  CtxCompatible decls ctx ->
  OK_Seq ctx stmts ->
    Step_Seq ctx (mem_memory_from_decls decls) stmts 
             (mem_memory_from_decls decls).
Proof with auto.
  intros ctx decls stmts CompC OK.
  induction OK. constructor.
  apply Step_seq with (mu':=(mem_memory_from_decls decls))...
  apply sem_step_stmt...
Qed.


(* Programs can be fully evaluated and operate on  *)
(* only as much memory as required by the 'decls': *)

Theorem sem_program_evaluation :
  forall (decls : Decls) (stmts : Stmts) (ctx : Context),
    OK_Prog (decls, stmts) ->
    CtxCompatible decls ctx ->
      Eval_Prog (decls, stmts) (mem_memory_from_decls decls).
Proof with auto.
  intros decls stmts ctx OK CompC.
  apply Eval_prog with (ctx:=ctx) (mu:=(mem_memory_from_decls decls))...
  apply mem_from_decls_compatible.
  apply sem_step_seq... inversion OK; subst...
    apply (ctx_compatible_unique _ _ _ CompC) in H1. rewrite H1...
Qed.

