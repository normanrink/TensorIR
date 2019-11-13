(*****************************************************************************)
(*                                                                           *)
(*  Domain.v                                                                 *)
(*                                                                           *)
(*  Tensors will be modelled as total maps from finite domains to the reals  *)
(*  (or, more generally, to a field or ring). This file models the relevant  *)
(*  finite domains as tuples of bounded natural numbers.                     *)
(*                                                                           *)
(*  Bijections between finite domains are also defined. These bijections     *)
(*  will be used to define the transposition operation on tensors. More      *)
(*  generally, bijections can be used to define what is usually called a     *)
(*  'reshape' or a 'view' of a tensor.                                       *)
(*                                                                           *)
(*****************************************************************************)


Require Import Basics.
Require Import Eqdep_dec.
Require Import FunctionalExtensionality.

Require Import TensorIR.Equations.Shallow.Vectors.

Import VectorNotations.



Definition Fin := Fin.t.


(* The type of a finite domain (of a tensor) is
   a tuple of types of bounded natural numbers: *)

Fixpoint DomainT {r : nat} (bounds : NVect r) : Set :=
  match bounds with
    | [] => unit
    | d::bound' => ((Fin d) * (DomainT bound'))%type
  end.


(* Equality of domains is decidable: *)

Lemma dom_eq_dec {n : nat} {b : NVect n} :
  forall (x y : DomainT b), {x = y} + {x <> y}.
Proof with auto.
  induction b; destruct x, y...
  destruct (IHb d d0) as [IHeq | IHneq];
    destruct (Fin.eq_dec f f0) as [FinEq | FinNeq].
  2-4: right; inversion 1...
  left; rewrite IHeq; rewrite FinEq...
Qed.


(* "Unicity of identity proofs" for domains: *)

Lemma dom_UIP_dec {n : nat} {b : NVect n} :
  forall (x : DomainT b) (pf1 pf2 : x = x), pf1 = pf2.
Proof.
  intros x pf; apply (UIP_dec dom_eq_dec).
Qed.

Lemma dom_UIP_refl {n : nat} {b : NVect n} :
  forall (x : DomainT b) (pf : x = x), pf = eq_refl x.
Proof.
  intros x pf; apply dom_UIP_dec.
Qed.


(* Two alternative definitions for splitting of tuples: *)

Fixpoint split' (l : nat) {r : nat} {b : NVect (l + r)} 
                (i : DomainT b) {struct l} : 
                DomainT (fst (splitat l b))* DomainT (snd (splitat l b)).
  refine(match l as l0
                 return (forall (b0 : NVect (l0 + r)),
                         DomainT b0 -> 
                         DomainT (fst (splitat l0 b0))
                         * DomainT (snd (splitat l0 b0)))
         with
           | 0    => fun _ i => (tt,i)
           | S l' => fun b' i => _
         end b i).
Proof.
  destruct (splitat l' (tl b')) as (b0,bs) eqn:Heq.
  rewrite (eta b') in i; simpl in i.
  pose proof (split' l' r (tl b') (snd i)) as H; rewrite Heq in H; simpl in H.
  simpl; rewrite Heq; exact ((fst i, fst H), snd H).
Defined.

Fixpoint split (l : nat) {r : nat} {b0 : NVect l} {b1 : NVect r} {struct b0} :
               DomainT (b0 ++ b1) -> DomainT b0 * DomainT b1 :=
  match b0 as b0'
           return (DomainT (b0' ++ b1) -> DomainT b0' * DomainT b1)
  with
    | [] => fun i => (tt,i)
    | b00::b0'' => fun i => let (i0,i') := i in
                            let (j0,j1) := split _ i' in
                            ((i0,j0),j1)
  end.


(* Concatenation of tuples: *)

Fixpoint dom_append {m n : nat} {b0 : NVect m} {b1 : NVect n} :
  DomainT b0 -> DomainT b1 -> DomainT (b0 ++ b1) :=
    match b0 as b0'
             return (DomainT b0' -> DomainT b1 -> DomainT (b0' ++ b1))
    with
      | [] => fun _ i1 => i1
      | d::b0'' => fun i0 i1 => let (i00,i0') := i0 in
                                let tl := dom_append i0' i1 in
                                (i00,tl)
    end.

Lemma dom_split_append {r0 r1 : nat} {b0 : NVect r0} {b1 : NVect r1} :
  forall (j0 : DomainT b0) (j1 : DomainT b1),
    split r0 (dom_append j0 j1) = (j0,j1).
Proof with auto.
  induction b0; simpl; intros; destruct j0...
  + rewrite (IHb0 d j1)...
Qed.

Lemma dom_append_split {r0 r1 : nat} {b0 : NVect r0} {b1 : NVect r1} :
  forall (j : DomainT (b0 ++ b1)) (j0 : DomainT b0) (j1 : DomainT b1),
    (j0,j1) = split r0 j -> dom_append j0 j1 = j.
Proof with auto.
  induction b0; simpl; intros j j0 j1 Heq.
  + inversion Heq...
  + destruct j, j0, (split n d) eqn:Hs.
      inversion Heq; subst.
      rewrite (IHb0 d d1 d2 (eq_sym Hs))...
Qed.


(* Bijections between domains are useful for defining
   transpositions of tensors. More generally, bijections
   can define tensor operations that are usually referred
   to as 'reshape' or 'view':                             *)

Section Bijections.
  Variable r : nat.

  Record bijection (b0 b1 : NVect r) : Set := Bijection {
    f : DomainT b0 -> DomainT b1;
    g : DomainT b1 -> DomainT b0;

    id_gf : forall (i0 : DomainT b0), g (f i0) = i0;
    id_fg : forall (i1 : DomainT b1), f (g i1) = i1
  }.

  Arguments f {b0 b1}.
  Arguments g {b0 b1}.
  Arguments id_gf {b0 b1}.
  Arguments id_fg {b0 b1}.


  Lemma id_dom_UIP_dec {b : NVect r}
                       {h : DomainT b -> DomainT b} :
    forall (pf1 pf2 : forall (x : DomainT b), h x = x), 
      pf1 = pf2.
  Proof.
    intros pf1 pf2.
    apply functional_extensionality_dep.
    intro x.
    apply (UIP_dec dom_eq_dec).
  Qed.

  Lemma id_gf_UIP_dec {b0 b1 : NVect r}
                      (f : DomainT b0 -> DomainT b1) 
                      (g : DomainT b1 -> DomainT b0):
    forall (pf1 pf2 : forall (x : DomainT b0), g (f x) = x),
      pf1 = pf2.
  Proof.
    apply id_dom_UIP_dec.
  Qed.

  Lemma bij_equal {b0 b1 : NVect r}
                  (bij_1 bij_2 : bijection b0 b1) :
    f bij_1 = f bij_2 -> g bij_1 = g bij_2 ->
      bij_1 = bij_2.
  Proof with auto.
    destruct bij_1, bij_2; simpl; intros Hfeq Hgeq; subst.
    rewrite (id_gf_UIP_dec _ _ id_gf0 id_gf1);
      rewrite (id_gf_UIP_dec _ _ id_fg0 id_fg1)...
  Qed.

  Lemma bij_equal' {b0 b1 : NVect r}
                   (bij_1 bij_2 : bijection b0 b1) :
    (forall x, f bij_1 x = f bij_2 x) ->
      (forall y, g bij_1 y = g bij_2 y) ->
        bij_1 = bij_2.
  Proof with auto.
    intros; apply bij_equal; apply functional_extensionality...
  Qed.


  Definition compose {b0 b1 b2 : NVect r} 
                     (bij_2 : bijection b1 b2)
                     (bij_1 : bijection b0 b1) : bijection b0 b2.
    refine({| f := Basics.compose (f bij_2) (f bij_1);
              g := Basics.compose (g bij_1) (g bij_2);
              id_gf := _;
              id_fg := _  |}).
  Proof with auto.
    + intro i0; unfold compose.
      rewrite (id_gf bij_2); rewrite (id_gf bij_1)...
    + intro i1; unfold compose.
      rewrite (id_fg bij_1); rewrite (id_fg bij_2)...
  Defined.

  Definition bij_inverse {b0 b1 : NVect r}
                         (bij : bijection b0 b1) : bijection b1 b0 :=
    {| f := g bij; 
       g := f bij; 
       id_gf := id_fg bij;
       id_fg := id_gf bij  |}.

  Definition identity {b : NVect r} : bijection b b :=
    {| f := id;
       g := id;
       id_gf := fun _ => eq_refl;
       id_fg := fun _ => eq_refl  |}.

  Lemma inverse_correct_1 {b : NVect r} (bij : bijection b b) :
    compose (bij_inverse bij) bij = identity.
  Proof with auto.
    apply bij_equal'; simpl; intro x; unfold Basics.compose;
      rewrite (id_gf bij)...
  Qed.

  Lemma inverse_correct_2 {b : NVect r} (bij : bijection b b) :
    compose bij (bij_inverse bij) = identity.
  Proof with auto.
    apply bij_equal'; simpl; intro x; unfold Basics.compose;
      rewrite (id_fg bij)...
  Qed.
End Bijections.


Arguments bijection {r}.
Arguments Bijection {r b0 b1}.
Arguments f {r b0 b1}.
Arguments g {r b0 b1}.
Arguments id_gf {r b0 b1}.
Arguments id_fg {r b0 b1}.


(* Transposition of the first two elements in a tuple: *)

Definition f_01 {r : nat} {b0 b1 : nat} {bnds : NVect r} :
  DomainT (b0::b1::bnds) -> DomainT (b1::b0::bnds) :=
  fun i => let (i0,i')  := i in 
           let (i1,i'') := i' in
           (i1,(i0,i'')).

Lemma f_01_self_inverse {r : nat} {b0 b1 : nat} {bnds : NVect r} :
  forall (i : DomainT (b0::b1::bnds)), f_01 (f_01 i) = i.
Proof.
  destruct i as [i0 i'].
  destruct i' as [i1 i''].
  reflexivity.
Qed.

Definition transp_01 {r : nat} (b0 b1 : nat) (bnds : NVect r) :=
  {| f := @f_01 r b0 b1 bnds;
     g := @f_01 r b1 b0 bnds;
     id_gf := f_01_self_inverse;
     id_fg := f_01_self_inverse  |}.

