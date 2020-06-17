(*****************************************************************************)
(*                                                                           *)
(*  Lemmas.v                                                                 *)
(*                                                                           *)
(*  This file establishes identities between array operations.               *)
(*                                                                           *)
(*  While the identities proven here can be useful for transforming complex  *)
(*  expressions built from array operations, they also serve the purpose of  *)
(*  verifying that the definitions of array operations behave as expected.   *)
(*  This is particularly relevant for the operations that have less trivial  *)
(*  definitions, i.e. 'split', 'append', 'foldl' and 'foldr'.                *)
(*                                                                           *)
(*****************************************************************************)


Require Import FunctionalExtensionality.
Require Import Program.Equality.

Require Import TensorIR.Equations.Shallow.Domain.
Require Import TensorIR.Equations.Shallow.Vectors.
Require Import TensorIR.Arrays.Array.
Require Import TensorIR.Arrays.Operations.

Import VectorNotations.



Lemma map_compose {a b c : Type} {r : nat} {sh : NVect r} : 
  forall (f : a -> b) (g : b -> c) (x : Array sh a),
  (map g) ((map f) x) = map (fun z => g (f z)) x.
Proof.
  intuition.
Qed.


Lemma map_reshape {a b : Type} {r s : nat} {sh : NVect r} {sh' : NVect s} :
  forall (f : a -> b) (rs : DomainT sh' -> DomainT sh) (x : Array sh a),
    map f (reshape rs x) = reshape rs (map f x).
Proof.
  intuition.
Qed.


Lemma split_append {a : Type} {r : nat} {sh : NVect r} {m n : nat} :
  forall (x : Array (m::sh) a) (y : Array (n::sh) a),
    split (append x y) = (x, y).
Proof.
  intuition.
  apply injective_projections;
    apply functional_extensionality; simpl; intuition;
    rewrite sep_join; auto.
Qed.


Lemma append_split {a : Type} {r : nat} {sh : NVect r} {m n : nat} :
  forall (x : Array (m+n::sh) a),
    let (y0,y1) := split x in append y0 y1 = x.
Proof.
  intro x.
  unfold split, append; apply functional_extensionality; intuition.
  destruct x0 as (i0,i').
  pose proof (join_sep i0) as H.
  destruct (sep i0); rewrite <- H; auto.
Qed.


Lemma split_map_append {a b : Type} {r : nat} {sh : NVect r} {m n : nat} :
  forall (f : a -> b) (x : Array (m+n::sh) a),
    let (y0,y1) := split x in
    append (map f y0) (map f y1) = map f x.
Proof with auto.
  intuition.
  pose proof (@append_split b r sh m n (map f x)) as H.
  rewrite <- H.
  apply functional_extensionality...
Qed.


Lemma split_0_empty {a : Type} {r : nat} {sh : NVect r} {n : nat} :
  forall (x : Array (0+n::sh) a),
    fst (split x) = empty sh.
Proof.
  intro x.
  apply functional_extensionality; intro i.
  destruct i. inversion f.
Qed.


Lemma append_head_behead {a : Type} {r : nat} {sh : NVect r} :
  forall (k : nat) (x : Array (S k::sh) a),
    append (prop 0 (head x)) (behead x) = x.
Proof.
  intros; apply functional_extensionality;
    destruct x0 as (i0,i');
    dependent destruction i0; auto.
Qed.


Lemma head_append {a : Type} {r : nat} {sh : NVect r} :
  forall (m n : nat) (x : Array (S m::sh) a) (y : Array (n::sh) a),
    head (append x y) = head x.
Proof.
  intros; apply functional_extensionality; auto.
Qed.


Lemma append_head_append_behead {a : Type} {r : nat} {sh : NVect r} :
  forall (m n : nat) (x : Array (S m::sh) a) (y : Array (n::sh) a),
  append x y = append (prop 0 (head x)) (append (behead x) y).
Proof.
  intros.
  apply functional_extensionality; intro i.
  destruct i as (i0,i').
  dependent destruction i0... simpl. unfold head. reflexivity.
  simpl. destruct (sep i0); auto.
Qed.


Lemma foldl_step {a : Type} {m : nat} {r : nat} {sh : NVect r} :
  forall (f : Array sh a -> Array sh a -> Array sh a),
    (forall u v w, f (f u v) w = f u (f v w)) ->
      forall (i u : Array sh a) (v : Array (m::sh) a),
        foldl f (f u i) v = f u (foldl f i v).
Proof with auto.
  induction m; intros f assoc; auto.
  + intuition.
    unfold foldl at 2. fold (@foldl). rewrite IHm...
    unfold foldl at 1. fold (@foldl). rewrite IHm...
Qed.


Lemma fold_lr {a : Type} {m : nat} {r : nat} {sh : NVect r} :
  forall (f : Array sh a -> Array sh a -> Array sh a),
    (forall u v w, f (f u v) w = f u (f v w)) ->
      forall (init : Array sh a), (forall u, f u init = f init u) ->
        forall (x : Array (m::sh) a), foldl f init x = foldr f init x.
Proof with auto.
  induction m; intros f assoc init comm x; auto.
  + simpl.
    rewrite <- IHm...
    unfold foldl. fold (@foldl).
    rewrite <- comm.
    rewrite foldl_step...
Qed.
