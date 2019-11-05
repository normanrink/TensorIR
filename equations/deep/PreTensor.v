(*****************************************************************************)
(*                                                                           *)
(*  PreTensor.v                                                              *)
(*                                                                           *)
(*  A 'PreTensor' is a map from tuples (i.e. data type 'Tuple') to values    *)
(*  (i.e. data type 'Value'). Since 'Value' is an 'option' type, one should  *)
(*  think of a 'PreTensor' as a partial map.                                 *)
(*                                                                           *)
(*  Since a 'PreTensor' is a partial map, it makes sense to ask what is the  *)
(*  domain of a 'PreTensor'. The predicate 'PreDomainP' expresses the fact   *)
(*  that a 'PreTensor' has a very simple domain, namely that the domain      *)
(*  consists precisely of all tuples that are bounded above (under '.<=.')   *)
(*  by a given fixed tuple.                                                  *)
(*                                                                           *)
(*****************************************************************************)


Require Import TensorIR.Tuple.Tuple.
Require Import TensorIR.Equations.Deep.Value.

Require Export TensorIR.Tuple.Tuple.
Require Export TensorIR.Equations.Deep.Value.



Definition PreTensor := Tuple -> Value.

Definition pre_access : PreTensor -> Tuple -> Value :=
  fun x i => (x i).

Notation "x '.[' i ']'" := (pre_access x i) (at level 10, left associativity)
                           : pre_scope.


Open Scope pre_scope.

Definition PreDomainP (l:Tuple) (x:PreTensor) : Prop :=
  forall (i:Tuple), x.[i] <> None <-> i.<=.l .

Definition PreDomainP' (l:Tuple) (x:PreTensor) : Prop :=
  forall (i:Tuple), (exists r, x.[i] = Some r) <-> i.<=.l .

(* Restriction of a 'PreTensor' is currently not needed: *)
(*                                                       *)
(* Definition Restrict (l:Tuple) (x:PreTensor) :=        *)
(*   fun i => if i.<=?.l then x i else None.             *)

Lemma pre_domain_none_some : forall (l:Tuple) (x:PreTensor),
  PreDomainP l x <-> PreDomainP' l x.
Proof with auto.
  intuition.
  + unfold PreDomainP'; intro i; intuition.
    apply val_not_none_ex_some in H0; apply H in H0...
    unfold PreDomainP in H. pose proof (H i) as H1.
    destruct (x.[i]) eqn:xieqn.
    * exists r...
    * apply H1 in H0. contradiction.
  + unfold PreDomainP.
    intuition.
    * apply H. apply val_not_none_ex_some.
      destruct (x.[i]) eqn:zieqn.
      - intuition.
      - contradiction.
    * apply H in H0. destruct H0. rewrite H0 in H1. inversion H1.
Qed.

(* While the definition of 'PreDomainP' is more natural than that of
  "PreDomainP'", it is usually more convenient in proofs to work with
  "PreDomainP'". Hence the following hint:                            *)

Hint Rewrite -> pre_domain_none_some.


Lemma pre_domain_some_length_eq : forall (l i:Tuple) (x:PreTensor),
  PreDomainP l x -> (exists r, x.[i] = Some r) -> length l = length i.
Proof with auto.
  intuition. apply pre_domain_none_some in H. apply H in H0.
  apply tup_le_length_eq in H0...
Qed.

Lemma pre_domain_some_length_eq' : forall (l i:Tuple) (x:PreTensor),
  PreDomainP' l x -> (exists r, x.[i] = Some r) -> length l = length i.
Proof with auto.
  intuition.
  apply pre_domain_none_some in H. apply (pre_domain_some_length_eq l i x)...
Qed.

Close Scope pre_scope.


