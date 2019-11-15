(*****************************************************************************)
(*                                                                           *)
(*  Expr.v                                                                   *)
(*                                                                           *)
(*  The syntax of tensor expressions is represented by the inductive data    *)
(*  type 'expr'. Only well-typed expressions can be represented with 'expr'  *)
(*  since 'expr' carries an index of type 'Tuple', i.e. the type 'expr'      *)
(*  depends on a value of type 'Tuple'.                                      *)
(*  (Note that 'Tuple' represents the type of a tensor and therefore also    *)
(*  the type of expressions formed from tensors.)                            *)
(*                                                                           *)
(*  Bindings of tensor expressions to variables are represented in the       *)
(*  'expr' type using "parametric higher-order abstract syntax" (PHOAS).     *)
(*  This leads to the introduction of the parameter 'var' of the 'expr'      *)
(*  type. The type 'Expr' is then obtained by universally quantifying over   *)
(*  the parameter 'var'.                                                     *)
(*                                                                           *)
(*  Reference for PHOAS:                                                     *)
(*    Adam Chlipala. 2008. Parametric higher-order abstract syntax for       *)
(*    mechanized semantics. In Proceedings of the 13th ACM SIGPLAN           *)
(*    international conference on Functional programming (ICFP '08).         *)
(*    ACM, New York, NY, USA, 143-156.                                       *)
(*    DOI: https://doi.org/10.1145/1411204.1411226                           *)
(*                                                                           *)
(*****************************************************************************)

Require Import TensorIR.Tuple.Tuple.
Require Import TensorIR.Equations.Deep.Value.



(* Context of tensor types (aka. 'Tuple'): *)

Definition Context := list Tuple.


Open Scope list_scope.

(* Judgement that a tensor type (aka. 'Tuple') is present in a context: *)

Inductive InCtx : Tuple -> Context -> Set :=
  | Here  : forall {t : Tuple} {ctx : Context},
            InCtx t (t::ctx)
  | There : forall {t t' : Tuple} {ctx : Context},
            InCtx t ctx -> InCtx t (t'::ctx).


(* Well-typed tensor expressions:
     (a) Expressions are typed in a typing context 'ctx'. The context 'ctx' 
         is used to determine the types of tensors 'Tens' that come from the
         environment of a tensor expression.
     (b) Binding of tensor expressions to variables is modelled by 'Let'
         expressions using 'parametric higher-order abstract syntax'
         (PHOAS). The variable bound in a 'Let' expression has type 'var t',
         where 't' is a 'Tuple. Hence, 'expr' is parametrized by 'var'.      *)

Inductive expr {var : Tuple -> Set} {ctx : Context} : Tuple -> Set :=
  | Tens   : forall {t : Tuple}, 
             InCtx t ctx -> expr t
  | Add    : forall {t : Tuple}, 
             expr t -> 
             expr t -> 
             expr t
  | Proj   : forall {t:Tuple} {d m:nat},
             m <= d ->
             expr (d::t) ->
             expr t
  | Prod   : forall {t0 t1 : Tuple},
             expr t0 ->
             expr t1 ->
             expr (t0++t1)
  | SMul   : forall {t : Tuple},
             R ->
             expr t ->
             expr t
  | Expa   : forall {t:Tuple} (d:nat),
             expr t ->
             expr (d::t)
  | Diag   : forall {t:Tuple} {d:nat},
             expr (d::d::t) ->
             expr (d::t)
  | Transp : forall {t t':Tuple} {m:nat},
             tup_swap m t = Some t' ->
             expr t ->
             expr t'
  | Red    : forall {t:Tuple} {d:nat},
             expr (d::t) ->
             expr t
  | Var    : forall {t : Tuple},
             var t -> expr t
  | Let    : forall {tx t : Tuple},
             expr tx ->
             (var tx -> expr t) ->
             expr t
  | Conv   : forall {t:Tuple} {m n:nat},
             n <= m ->
             expr (m::n::t) -> 
             expr (m-n::t).

Close Scope list_scope.


(* Tensor expressions 'Expr' are polymorphic in the parameter 'var': *)

Definition Expr (ctx : Context) (t : Tuple) := 
  forall (var : Tuple -> Set), @expr var ctx t.


(* Expansion of 'Let' expressions, i.e. replacement of variables *)
(* with their bound expressions:                                 *)

Fixpoint expandLet' {var : Tuple -> Set} {t : Tuple} {ctx : Context} 
                    (e : @expr (@expr var ctx) ctx t) : @expr var ctx t :=
  match e with
    | Tens i      => Tens i
    | Add e1 e2   => Add (expandLet' e1) (expandLet' e2)
    | Proj le e   => Proj le (expandLet' e)
    | Prod e1 e2  => Prod (expandLet' e1) (expandLet' e2)
    | SMul r e    => SMul r (expandLet' e)
    | Expa d e    => Expa d (expandLet' e)
    | Diag e      => Diag (expandLet' e)
    | Transp eq e => Transp eq (expandLet' e)
    | Red e       => Red (expandLet' e)
    | Var e       => e
    | Let ex f    => let x := (expandLet' ex) in
                     expandLet' (f x)
    | Conv le e   => Conv le (expandLet' e)
  end.

Definition expandLet {t : Tuple} {ctx : Context} :
  Expr ctx t -> Expr ctx t :=
  fun e var => expandLet' (e (@expr var ctx)).


(* Convenient notation for variable binding with 'Let' expressions: *)

Notation "'do' x <- A ; B" := (Let A (fun x => B)) (at level 200,
                                                    x ident,
                                                    A at level 100,
                                                    B at level 200).


(* Examples of variable bindings and their expansions: *)

Example quadruple_expr {var : Tuple -> Set} {ctx : Context} {t : Tuple}
                      (e : @expr var ctx t) :=
  Let (Add e e)
      (fun x => Add (Var x) (Var x)).

Example do_quadruple_expr {var : Tuple -> Set} {ctx : Context} {t : Tuple}
                          (e : @expr var ctx t) :=
  do x <- Add e e; 
  Add (Var x) (Var x).

Eval simpl in (fun e => expandLet' (quadruple_expr e)).
Eval simpl in (fun e => expandLet' (do_quadruple_expr e)).


(* Rename the expressions constructor 'Add' into 'EAdd' to
   avoid a name clash after importing the module 'List':   *)

Definition EAdd {var : Tuple -> Set} {ctx : Context} {t : Tuple} :=
  @Add var ctx t.


Require Import List.

Open Scope list_scope.

(* Introduce relations 'wf' and 'Wf' analogous to Section 17.2.2 of
   "Certified Programming with Dependent Types" by Adam Chlipala, 2013:
     - 'wf' is a binary relation on 'expr' that holds precisely if two
       expressions with different parameters 'var1' and 'var2' have the
       same structure.
     - 'Wf' is a unary relation indicating well-formedness of 'Expr',
       in the sense that 'wf' holds of any two instantiations of 'Expr'
       with arbitrary parameters 'var1', 'var2'.                        *)

Section well_formed_expr. 
  Variables var1 var2 : Tuple -> Set.

  Record varEntry := {
    type   : Tuple;
    first  : var1 type;
    second : var2 type;
  }.

  Inductive wf {ctx : Context} :
    list varEntry -> forall {t : Tuple},
                       @expr var1 ctx t -> @expr var2 ctx t -> Prop :=
    | WfTens   : forall {vars : list varEntry}
                        {t:Tuple} (ic : InCtx t ctx),
                 wf vars (Tens ic) (Tens ic)
    | WfAdd    : forall {vars : list varEntry}
                        {t:Tuple} 
                        {e1  e2  : @expr var1 ctx t} 
                        {e1' e2' : @expr var2 ctx t},
                 wf vars e1 e1' ->
                 wf vars e2 e2' ->
                 wf vars (EAdd e1 e2) (EAdd e1' e2')
    | WfProj   : forall {vars : list varEntry}
                        {t:Tuple} {d m:nat}
                        {le le' : m <= d}
                        {e : @expr var1 ctx (d::t)} {e' : @expr var2 ctx (d::t)},
                 wf vars e e' ->
                 wf vars (Proj le e) (Proj le' e')
    | WfProd   : forall {vars : list varEntry} 
                        {t1 t2:Tuple}
                        {e1 : @expr var1 ctx t1} {e2 : @expr var1 ctx t2}
                        {e1': @expr var2 ctx t1} {e2': @expr var2 ctx t2},
                 wf vars e1 e1' ->
                 wf vars e2 e2' ->
                 wf vars (Prod e1 e2) (Prod e1' e2')
    | WfSMul   : forall {vars : list varEntry}
                        {r:R} {t:Tuple}
                        {e : @expr var1 ctx t} {e' : @expr var2 ctx t},
                 wf vars e e' ->
                 wf vars (SMul r e) (SMul r e')
    | WfExpa   : forall {vars : list varEntry}
                        {t:Tuple} {d:nat}
                        {e : @expr var1 ctx t} {e' : @expr var2 ctx t},
                 wf vars e e' ->
                 wf vars (Expa d e) (Expa d e')
    | WfDiag   : forall {vars : list varEntry}
                        {t:Tuple} {d:nat}
                        {e : @expr var1 ctx (d::d::t)}
                        {e' : @expr var2 ctx (d::d::t)},
                 wf vars e e' ->
                 wf vars (Diag e) (Diag e')
    | WfTransp : forall {vars : list varEntry}
                        {t t':Tuple} {m:nat}
                        {eq eq' : tup_swap m t = Some t'}
                        {e  : @expr var1 ctx t} {e' : @expr var2 ctx t},
                 wf vars e e' ->
                 wf vars (Transp eq e) (Transp eq' e')
    | WfRed    : forall {vars : list varEntry}
                        {t:Tuple} {d:nat}
                        {e  : @expr var1 ctx (d::t)}
                        {e' : @expr var2 ctx (d::t)},
                 wf vars e e' ->
                 wf vars (Red e) (Red e')
    | WfVar    : forall {vars : list varEntry}
                        {t : Tuple}
                        {x1 : var1 t} {x2 : var2 t},
                 In {| type:=t; first:=x1; second:=x2 |} vars ->
                 wf vars (Var x1) (Var x2)
    | WfLet    : forall {vars : list varEntry}
                        {tx t : Tuple}
                        {ex : @expr var1 ctx tx} {ex' : @expr var2 ctx tx}
                        {f   : var1 tx -> @expr var1 ctx t}
                        {f'  : var2 tx -> @expr var2 ctx t},
                 wf vars ex ex' ->
                 (forall (x : var1 tx) (x' : var2 tx), 
                    let vars' := {| type:=tx; first:=x; second:=x' |}::vars in
                    wf vars' (f x) (f' x')) ->
                 wf vars (Let ex f) (Let ex' f')
    | WfConv   : forall {vars : list varEntry}
                        {t:Tuple} {m n:nat}
                        {le le' : n <= m}
                        {e  : @expr var1 ctx (m::n::t)}
                        {e' : @expr var2 ctx (m::n::t)},
                 wf vars e e' ->
                 wf vars (Conv le e) (Conv le' e').

  Hint Constructors wf.
End well_formed_expr.

Arguments varEntry {var1 var2}.
Arguments first {var1 var2}.
Arguments second {var1 var2}.
Arguments type {var1 var2}.
Arguments wf {var1 var2 ctx}.


Definition Wf {ctx : Context} {t : Tuple} (e : Expr ctx t) :=
  forall (var1 var2 : Tuple -> Set), wf [] t (e var1) (e var2).

Close Scope list_scope.

