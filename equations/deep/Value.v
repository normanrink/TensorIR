(*****************************************************************************)
(*                                                                           *)
(*  Value.v                                                                  *)
(*                                                                           *)
(*  The data type 'Value' represents entries/elements of a tensor. Since     *)
(*  'Value' is an 'option' type, undefined entries are allowed. Defined      *)
(*  entries are real numbers; a more general development could allow entries *)
(*  from any ring or field.                                                  *)
(*                                                                           *)
(*****************************************************************************)


Require Import Reals.

Require Export Reals.



Definition Value := option R.

Definition plus : Value -> Value -> Value :=
  fun x y =>
  match x, y with
    | Some x', Some y' => Some (x' + y')%R
    | _, _ => None
  end.

Definition mult : Value -> Value -> Value :=
  fun x y =>
  match x, y with
    | Some x', Some y' => Some (x' * y')%R
    | _, _ => None
  end.

Notation "x + y" := (plus x y) (at level 50, left associativity) : val_scope.
Notation "x * y" := (mult x y) (at level 40, left associativity) : val_scope.


Open Scope val_scope.

Lemma val_plus_0_r : forall (x:R), Some x + Some 0%R = Some x.
Proof with auto.
  intro x. simpl. rewrite Rplus_0_r...
Qed.

Lemma val_plus_v0 : forall v, v + Some 0%R = v.
Proof with auto.
  intro v. destruct v... rewrite val_plus_0_r...
Qed.

Lemma val_plus_0_l : forall (x:R), Some 0%R + Some x = Some x.
Proof with auto.
  intro x. simpl. rewrite Rplus_0_l...
Qed.

Lemma val_plus_none_l : forall (v:Value), None + v = None.
Proof with auto.
  intro v. destruct v...
Qed.

Lemma val_mult_0_r : forall (x:R), Some x * Some 0%R = Some 0%R.
Proof with auto.
  intro x. simpl. rewrite Rmult_0_r...
Qed.

Lemma val_mult_0_l : forall (x:R), Some 0%R * Some x = Some 0%R.
Proof with auto.
  intro x. simpl. rewrite Rmult_0_l...
Qed.

Lemma val_mult_none_r : forall (v:Value), v * None = None.
Proof with auto.
  intro v. destruct v...
Qed.

Lemma val_not_none_ex_some : forall (v:Value),
  v <> None <-> exists r, v = Some r.
Proof with auto.
  induction v.
    intuition... exists a... inversion H0.
    intuition... inversion H... inversion H1.
Qed.

Lemma val_plus_some_inv : forall (v w:Value) (r:R),
  v + w = Some r -> exists rv rw, v = Some rv /\ w = Some rw.
Proof with auto.
  intros v w r H; destruct v as [rv |], w as [rw |].
  1: exists rv, rw...
  1-3: inversion H.
Qed.

Lemma val_mult_some_inv : forall (v w:Value) (r:R),
  v * w = Some r -> exists rv rw, v = Some rv /\ w = Some rw.
Proof with auto.
  intros v w r H; destruct v as [rv |], w as [rw |].
  1: exists rv, rw...
  1-3: inversion H.
Qed.

Lemma val_mult_plus_distr_r: forall u v w : Value, 
  (u + v) * w = u * w + v * w.
Proof with auto.
  intros u v w; destruct u as [ru |], v as [rv |], w as [rw |].
  1: simpl; rewrite Rmult_plus_distr_r...
  1-7: simpl...
Qed.

Close Scope val_scope.


Lemma val_plus_some_some : forall (v w:Value) (x y:R),
  v = Some x -> w = Some y -> exists r, plus v w = Some r.
Proof with auto.
  intros v w x y Hv Hw; destruct v as [rv |], w as [rw |].
  1: exists (rv + rw)%R...
  1-3: inversion Hv; inversion Hw.
Qed.


Lemma val_mult_some_some : forall (v w:Value) (x y:R),
  v = Some x -> w = Some y -> exists r, mult v w = Some r.
Proof with auto.
  intros v w x y Hv Hw; destruct v as [rv|], w as [rw |].
  1: exists (rv * rw)%R...
  1-3: inversion Hv; inversion Hw.
Qed.

