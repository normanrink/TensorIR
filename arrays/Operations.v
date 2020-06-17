(*****************************************************************************)
(*                                                                           *)
(*  Operations.v                                                             *)
(*                                                                           *)
(*  This file contains definitions of common array operations.               *)
(*                                                                           *)
(*****************************************************************************)


Require Import TensorIR.Equations.Shallow.Domain.
Require Import TensorIR.Equations.Shallow.Vectors.
Require Import TensorIR.Arrays.Array.

Import VectorNotations.



Definition map {a b : Type} {r : nat} {sh : NVect r} :
  (a -> b) -> Array sh a -> Array sh b :=
  fun f x i => f (x i).


Definition zipWith {a b c : Type} {r : nat} {sh : NVect r} :
  (a -> b -> c) -> Array sh a -> Array sh b -> Array sh c :=
  fun f x y i => f (x i) (y i).


Definition zip {a b : Type} {r : nat} {sh : NVect r} :
  Array sh a -> Array sh b -> Array sh (a * b) :=
  fun x y => let p := fun eltx elty => (eltx, elty) in
             zipWith p x y.


(* General reshaping with a function (f : DomainT sh' -> DomainT sh): *)

Definition reshape {a : Type} {r s : nat} {sh : NVect r} {sh' : NVect s} :
  (DomainT sh' -> DomainT sh) -> Array sh a -> Array sh' a :=
  fun f x i => x (f i).


(* Append two arrays along their first dimensions (subsequent dimensions *)
(* must match, i.e. must be of shape 'sh'):                              *)

Definition append {a : Type} {r : nat} {sh : NVect r} {m n : nat} :
                  Array (m::sh) a -> Array (n::sh) a -> 
                  Array ((m+n)::sh) a :=
  fun x y i => let (i0,i') := i in
               match sep i0 with
                 | inl j => x (j,i')
                 | inr j => y (j,i')
               end.


(* Split an array into two arrays, along the first dimension: *)

Definition split {a : Type} {r : nat} {sh : NVect r} {m n : nat} :
                 Array ((m+n)::sh) a ->
                 (Array (m::sh) a) * (Array (n::sh) a) :=
  fun x => (fun (i : DomainT (m::sh)) => let (i0,i') := i in
                                         x (join (inl i0),i'),
            fun (i : DomainT (n::sh)) => let (i0,i') := i in
                                         x (join (inr i0),i')).


(* Extract the first slice of an array (equivalently, project *)
(* an array onto the first index in the first dimension):     *)

Definition head {a : Type} {m : nat} {r : nat} {sh : NVect r} :
  Array ((S m)::sh) a -> Array sh a :=
  fun x i => x (Fin.F1, i).


(* Extract all slices but the first one from an array: *)

Definition behead {a : Type} {m : nat} {r : nat} {sh : NVect r} :
  Array ((S m)::sh) a -> Array (m::sh) a :=
  fun x i => let (i0,i') := i in
             x (Fin.FS i0, i').


(* Extract the last slice of an array: *)

Fixpoint tail {a : Type} {m : nat} {r : nat} {sh : NVect r} :
  Array ((S m)::sh) a -> Array sh a :=
  match m with
    | 0    => fun x i => x (Fin.F1,i)
    | S m' => fun x i => tail (behead x) i
  end.


(* Extract all slices but the last one: *)

Definition curtail {a : Type} {m : nat} {r : nat} {sh : NVect r} :
  Array ((S m)::sh) a -> Array (m::sh) a :=
  fun x i => let (i0,i') := i in
             x (wkS i0, i').


(* Prop up an array by giving it constant *)
(* elements along the first dimension:    *)

Definition prop {a : Type} {r : nat} {sh : NVect r} :
  forall (k : nat), Array sh a -> Array ((S k)::sh) a :=
  fun _ x i => let (i0, i') := i in
               x i'.


Fixpoint foldr {a b : Type} {m : nat} {r : nat} {sh : NVect r} :
  (Array sh a -> Array sh b -> Array sh b) ->
  Array sh b -> Array (m::sh) a -> Array sh b :=
  fun f init => match m with
                  | 0    => fun _ => init
                  | S m' => fun x => f (head x) (foldr f init (behead x))
                end.

Definition foldr' {a b : Type} {m : nat} {r : nat} {sh : NVect r} :
  (a -> b -> b) ->
  Array sh b -> Array (m::sh) a -> Array sh b :=
  fun f => foldr (zipWith f).


Fixpoint foldl {a b : Type} {m : nat} {r : nat} {sh : NVect r} :
  (Array sh b -> Array sh a -> Array sh b) ->
  Array sh b -> Array (m::sh) a -> Array sh b :=
  fun f init => match m with
                  | 0    => fun _ => init
                  | S m' => fun x => foldl f (f init (head x)) (behead x)
                end.


Definition foldl' {a b : Type} {m : nat} {r : nat} {sh : NVect r} :
  (b -> a -> b) ->
  Array sh b -> Array (m::sh) a -> Array sh b :=
  fun f => foldl (zipWith f).
