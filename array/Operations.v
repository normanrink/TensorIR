

Require Import FunctionalExtensionality.
Require Import Program.Equality.

Require Import TensorIR.Equations.Shallow.Domain.
Require Import TensorIR.Equations.Shallow.Vectors.

Import VectorNotations.



Open Scope vector_scope.


Definition Array {r : nat} (sh : NVect r) (a : Type) := DomainT sh -> a.


Definition head {a : Type} {m : nat} {r : nat} {sh : NVect r} :
  Array ((S m)::sh) a -> Array sh a :=
  fun x i => x (Fin.F1, i).


Definition behead {a : Type} {m : nat} {r : nat} {sh : NVect r} :
  Array ((S m)::sh) a -> Array (m::sh) a :=
  fun x i => let (i0,i') := i in
             x (Fin.FS i0, i').


Definition prop {a : Type} {r : nat} {sh : NVect r} :
  forall (k : nat), Array sh a -> Array ((S k)::sh) a :=
  fun _ x i => let (i0, i') := i in
               x i'.


Fixpoint tail {a : Type} {m : nat} {r : nat} {sh : NVect r} :
  Array ((S m)::sh) a -> Array sh a :=
  match m with
    | 0    => fun x i => x (Fin.F1,i)
    | S m' => fun x i => tail (behead x) i
  end.


Fixpoint wkS {m : nat} (i : Fin.t m) : Fin.t (S m) :=
  match i with
    | Fin.F1 => Fin.F1
    | Fin.FS j => Fin.FS (wkS j)
  end.


Definition curtail {a : Type} {m : nat} {r : nat} {sh : NVect r} :
  Array ((S m)::sh) a -> Array (m::sh) a :=
  fun x i => let (i0,i') := i in
             x (wkS i0, i').


Definition map {a b : Type} {r : nat} {sh : NVect r} :
  (a -> b) -> Array sh a -> Array sh b :=
  fun f x i => f (x i).


Lemma map_compose {a b c : Type} {r : nat} {sh : NVect r} : 
  forall (f : a -> b) (g : b -> c) (x : Array sh a),
  (map g) ((map f) x) = map (fun z => g (f z)) x.
Proof.
  intuition.
Qed.


Definition zipWith {a b c : Type} {r : nat} {sh : NVect r} :
  (a -> b -> c) -> Array sh a -> Array sh b -> Array sh c :=
  fun f x y i => f (x i) (y i).


Definition reshape {a : Type} {r s : nat} {sh : NVect r} {sh' : NVect s} :
  (DomainT sh' -> DomainT sh) -> Array sh a -> Array sh' a :=
  fun f x i => x (f i).


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




Definition append {a : Type} {r : nat} {sh : NVect r} :
  forall (m n p : nat), p = m + n ->
    Array (m::sh) a -> Array (n::sh) a -> Array (p::sh) a.
      refine(
        fix f m n p eq x y i :=
          match m as m'
                return (forall n p, p = m' + n ->
                          Array (m'::sh) a -> Array (n::sh) a -> Array (p::sh) a)
                with
          | 0   => fun n0 p0 eq0 x0 y0 i0 => _
          | S k => fun n0 p0 eq0 x0 y0 i0 => _
        end n p eq x y i).
Proof.
  + simpl in eq0.
    rewrite eq0 in i0.
    exact (y0 i0).
  + rewrite eq0 in i0.
    destruct i0 as (i00, i0').
    remember (k + n0) as p1 eqn:?.
    rewrite plus_Sn_m in i00.
    rewrite <- Heqp1 in i00.
    inversion i00; subst.
    - exact (x0 (Fin.F1, i0')).
    - exact (f k n0 (k+n0) eq_refl (behead x0) y0 (H0,i0')).
Defined.


Definition append' {a : Type} {r : nat} {sh : NVect r} {m n : nat} :
  Array (m::sh) a -> Array (n::sh) a -> Array ((m+n)::sh) a.
  refine(
    fun t0 t1 i => _
  ).
Proof.
  induction m; simpl in *.
  + exact (t1 i).
  + destruct i as (i0, i').
    inversion i0; subst.
    - exact (t0 (Fin.F1, i')).
    - exact (IHm (behead t0) (H0, i')).
Defined.


Definition append'' {a : Type} {r : nat} {sh : NVect r} {n : nat} :
                    (forall (m : nat), Array (m::sh) a -> Array (n::sh) a ->
                                       Array ((m+n)::sh) a) :=
  fix f m :=
  match m return (Array (m::sh) a -> Array (n::sh) a -> Array ((m+n)::sh) a) with
    | 0    => fun x y i => y i
    | S m' => fun x y i => let (i0,i') := i in
                           match i0 in Fin.t (S k) 
                                    return (k = m'+n -> Array (S m'::sh) a -> a) with
                             | Fin.F1   => fun _  x1 => x1 (Fin.F1,i')
                             | Fin.FS j => fun eq x1 => let j' := eq_rec _ _ j _ eq in
                                                        f m' (behead x1) y (j',i')
                           end eq_refl x
  end.


Lemma append_correct_1 {a : Type} {r : nat} {sh : NVect r} : 
  forall (k : nat) (x : Array (S k::sh) a),
    append'' _ (prop 0 (head x)) (behead x) = x.
Proof with auto.
  intros; apply functional_extensionality.
    destruct x0 as (i0,i');
    dependent destruction i0...
Qed.


Lemma append_correct_2 {a : Type} {r : nat} {sh : NVect r} : 
  forall (m n : nat) (x : Array (S m::sh) a) (y : Array (n::sh) a),
    head (append'' _ x y) = head x.
Proof with auto.
  induction m; intros; apply functional_extensionality...
Qed.

Definition empty {a : Type} {r : nat} (sh : NVect r) :  Array (0::sh) a :=
  fun i => let (i0,i') := i in
           Fin.case0 _ i0.


Definition split'' {a : Type} {r : nat} {sh : NVect r} {n : nat} :
                   (forall (m : nat), Array ((m+n)::sh) a ->
                                      (Array (m::sh) a) * (Array (n::sh) a)) :=
  fix f m :=
  match m return Array ((m+n)::sh) a -> (Array (m::sh) a) * (Array (n::sh) a) with
    | 0    => fun x => (empty sh, x)
    | S m' => fun x => let (y1,y2) := f m' (behead x) in
                       (append'' _ (prop 0 (head x)) y1, y2)
  end.


Lemma app_expand_1 {a : Type} {r : nat} {sh : NVect r} : 
  forall (m n : nat) (x : Array (S m::sh) a) (y : Array (n::sh) a),
  append'' (S m) x y = append'' 1 (prop 0 (head x)) (append'' m (behead x) y).
Proof with auto.
  intuition.
      apply functional_extensionality; intro i.
  destruct i as (i0,i').
  dependent induction i0...
Qed.


Lemma split_app {a : Type} {r : nat} {sh : NVect r} : 
  forall (m n : nat) (x : Array (m::sh) a) (y : Array (n::sh) a),
    split'' m (append'' m x y) = (x, y).
Proof with auto.
  induction m; intuition;
    apply injective_projections; apply functional_extensionality; intro i; auto.
  + simpl. destruct i. inversion f.
  + unfold fst.
    destruct i. dependent destruction f...
    - unfold append''. fold (@append'' a).
Abort.



Fixpoint sep {m n : nat} : Fin.t (m+n) -> (Fin.t m) + (Fin.t n) :=
  match m return Fin.t (m+n) -> sum (Fin.t m) (Fin.t n) with
    | 0    => fun i => inr i
    | S m' => fun i => match i in Fin.t (S k) 
                                  return (k = m'+n -> sum (Fin.t (S m')) (Fin.t n)) with
                         | Fin.F1    => fun _  => inl Fin.F1
                         | Fin.FS i' => fun eq => let i'' := eq_rec _ _ i' _ eq in
                                                  match sep i'' with
                                                    | inl j => inl (Fin.FS j)
                                                    | inr j => inr j
                                                  end
                       end eq_refl
  end.

Fixpoint join {m n : nat} : (Fin.t m) + (Fin.t n) -> Fin.t (m+n) :=
  match m return sum (Fin.t m) (Fin.t n) -> Fin.t (m+n) with
    | 0    => fun i => match i with
                         | inl i' => match i' with end
                         | inr i' => i'
                       end
    | S m' => fun i => match i with
                         | inl i' => Fin.L n i'
                         | inr i' => Fin.R (S m') i'
                       end
  end.


Lemma sep_join {m n : nat} : forall (j : (Fin.t m) + (Fin.t n)),
  sep (join j) = j.
Proof.
  induction m; intuition.
  + inversion a.
  + dependent destruction a; simpl; auto.
    destruct m.
    - inversion a.
    - specialize IHm with (inl a).
      unfold join in IHm.
      rewrite IHm; auto.
  + simpl.
    specialize IHm with (inr b).
    destruct m; simpl; auto.
    unfold join in IHm; simpl in IHm.
    rewrite IHm; auto.
Qed.

Lemma join_sep {m n : nat} : forall (j : Fin.t (m+n)),
  join (sep j) = j.
Proof.
  induction m; intuition.
  dependent destruction j; simpl; auto.
  specialize IHm with j.
  destruct (sep j) eqn:?.
  + simpl.
    destruct m.
    - inversion t.
    - simpl in IHm. rewrite IHm; auto.
  + destruct m; simpl in *; rewrite IHm; auto.
Qed.


Definition append3 {a : Type} {r : nat} {sh : NVect r} {m n : nat} :
                   Array (m::sh) a -> Array (n::sh) a -> Array ((m+n)::sh) a :=
  fun x y i => let (i0,i') := i in
               match sep i0 with
                 | inl j => x (j,i')
                 | inr j => y (j,i')
               end.

Definition split3 {a : Type} {r : nat} {sh : NVect r} {m n : nat} :
                  Array ((m+n)::sh) a -> (Array (m::sh) a) * (Array (n::sh) a) :=
  fun x => (fun (i : DomainT (m::sh)) => let (i0,i') := i in x (join (inl i0),i'),
            fun (i : DomainT (n::sh)) => let (i0,i') := i in x (join (inr i0),i')).


Lemma split_append {a : Type} {r : nat} {sh : NVect r} {m n : nat} :
  forall (x : Array (m::sh) a) (y : Array (n::sh) a),
    split3 (append3 x y) = (x, y).
Proof.
  intuition.
  apply injective_projections;
    apply functional_extensionality; simpl; intuition;
    rewrite sep_join; auto.
Qed.



Lemma append_split {a : Type} {r : nat} {sh : NVect r} {m n : nat} :
  forall (x : Array (m+n::sh) a),
    let (y0,y1) := split3 x in
    append3 y0 y1 = x.
Proof.
  intuition; unfold split3, append3;
    apply functional_extensionality; intuition.
  destruct x0 as (i0,i').
  pose proof (join_sep i0) as H.
  destruct (sep i0); rewrite <- H; auto.
Qed.



Lemma split_0_empty {a : Type} {r : nat} {sh : NVect r} {n : nat} :
  forall (x : Array (0+n::sh) a),
    fst (split3 x) = empty sh.
Proof.
  intro x.
  apply functional_extensionality; intro i.
  destruct i. inversion f.
Qed.


Lemma append3_correct_1 {a : Type} {r : nat} {sh : NVect r} : 
  forall (k : nat) (x : Array (S k::sh) a),
    append3 (prop 0 (head x)) (behead x) = x.
Proof.
  intros; apply functional_extensionality;
    destruct x0 as (i0,i');
    dependent destruction i0; auto.
Qed.


Lemma append3_correct_2 {a : Type} {r : nat} {sh : NVect r} : 
  forall (m n : nat) (x : Array (S m::sh) a) (y : Array (n::sh) a),
    head (append3 x y) = head x.
Proof.
  intros; apply functional_extensionality; auto.
Qed.


Lemma app3_expand_1 {a : Type} {r : nat} {sh : NVect r} : 
  forall (m n : nat) (x : Array (S m::sh) a) (y : Array (n::sh) a),
  append3 x y = append3 (prop 0 (head x)) (append3 (behead x) y).
Proof.
  intros.
  apply functional_extensionality; intro i.
  destruct i as (i0,i').
  dependent destruction i0... simpl. unfold head. reflexivity.
  simpl. destruct (sep i0); auto.
Qed.



Lemma fold_step {a : Type} {m : nat} {r : nat} {sh : NVect r} :
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
    rewrite fold_step...
Qed.



Lemma fold_step_comm {a : Type} {m : nat} {r : nat} {sh : NVect r} :
  forall (f : Array sh a -> Array sh a -> Array sh a)
         (assoc :  forall u v w, f (f u v) w = f u (f v w))
         (init : Array sh a) 
         (comm : forall u v, f u v = f v u)
         (x : Array sh a) (y : Array (m::sh) a),
  foldl f (f init x) y = f x (foldl f init y).
Proof with auto.
  induction m; intuition; simpl...
  + rewrite <- IHm...
    repeat (rewrite assoc).
    rewrite (comm  x (head y))...
Qed.


Lemma fold_lr_comm {a : Type} {m : nat} {r : nat} {sh : NVect r} :
  forall (f : Array sh a -> Array sh a -> Array sh a)
         (assoc :  forall u v w, f (f u v) w = f u (f v w))
         (init : Array sh a) 
         (comm : forall u v, f u v = f v u)
         (x : Array (m::sh) a),
    foldl f init x = foldr f init x.
Proof with auto.
  induction m; intuition.
  simpl. rewrite <- IHm...
  apply fold_step_comm...
Qed.



(*
  Definition append3 {a : Type} {r : nat} {sh : NVect r} {n : nat} :
                      (forall (m : nat), Array (m::sh) a -> Array (n::sh) a -> Array ((m+n)::sh) a) :=
    fix f m :=
    match m return (Array (m::sh) a -> Array (n::sh) a -> Array ((m+n)::sh) a) with
      | 0    => fun x y i => y i
      | S m' => fun x y i => let (i0,i') := i in
                             match i0 in Fin.t (S k) 
                                      return (k = m'+n -> Array (S m'::sh) a -> a) with
                               | Fin.F1   => fun _  x1 => x1 (Fin.F1,i')
                               | Fin.FS j => fun eq x1 => let j' := eq_rec _ _ j _ eq in
                                                          f m' (behead x1) y (j',i')
                             end eq_refl x
    end.
*)

Fixpoint reduce {a : Type} {m : nat} {r : nat} {sh : NVect r}
                (f : Array sh a -> Array sh a -> Array sh a)
                (init : Array sh a) :
  Array (m::sh) a -> Array sh a :=
  match m with
    | 0    => fun _ => init
    | S m' => fun x => f (head x) (reduce f init (behead x))
  end.


Fixpoint reduce' {a : Type} {m : nat} {r : nat} {sh : NVect r}
                 (f : Array sh a -> Array sh a -> Array sh a)
                 (init : Array sh a) :
  Array (m::sh) a -> Array sh a :=
  match m with
    | 0    => fun x => init
    | S m' => fun x => f (reduce' f init (curtail x)) (tail x)
  end.


Lemma red_assoc {a : Type} {m : nat} {r : nat} {sh : NVect r}
                (f : Array sh a -> Array sh a -> Array sh a)
  (assoc : forall u v w, f (f u v) w = f u (f v w)) :
  forall (x : Array (m::sh) a) (y : Array sh a) (z : Array sh a),
    f (reduce f z x) y = reduce f (f z y) x.
Proof with auto.
  induction m; intros x y z;
  apply functional_extensionality;
    intro x0.
  + simpl...
  + simpl. rewrite assoc. rewrite IHm...
Qed.

Lemma red'_assoc {a : Type} {m : nat} {r : nat} {sh : NVect r}
                (f : Array sh a -> Array sh a -> Array sh a)
  (assoc : forall u v w, f (f u v) w = f u (f v w)) :
  forall (x : Array (m::sh) a) (y : Array sh a) (z : Array sh a),
    f y (reduce' f z x) = reduce' f (f y z) x.
Proof with auto.
  induction m; 
intros x y z;
  apply functional_extensionality;
    intro x0.
  + simpl...
  + simpl. rewrite <- assoc. rewrite IHm...
Qed.


Lemma map_reshape {a b : Type} {r s : nat} {sh : NVect r} {sh' : NVect s} :
  forall (f : a -> b) (rs : DomainT sh' -> DomainT sh) (x : Array sh a),
    map f (reshape rs x) = reshape rs (map f x).
Proof.
  intuition.
Qed.


Lemma split_map_append {a b : Type} {r : nat} {sh : NVect r} {m n : nat} :
  forall (f : a -> b) (x : Array (m+n::sh) a),
    let (y0,y1) := split3 x in
    append3 (map f y0) (map f y1) = map f x.
Proof with auto.
  intuition.
  pose proof (@append_split b r sh m n (map f x)) as H.
  rewrite <- H.
  apply functional_extensionality...
Qed.

