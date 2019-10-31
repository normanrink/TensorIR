(*****************************************************************************)
(*                                                                           *)
(*  Rlist.v                                                                  *)
(*                                                                           *)
(*  An 'rlist' (for "reverse list") grows by appending to the end.           *)
(*                                                                           *)
(*  It is natural to use an 'rlist' to represent a sequence of statements    *)
(*  or declarations. In particular, proofs by induction on the length of     *)
(*  such a sequence are naturally expressed as structural induction proofs   *)
(*  for an 'rlist'.                                                          *)
(*                                                                           *)
(*****************************************************************************)


Inductive rlist {A:Set} : Set :=
  | rnil : rlist
  | rsnoc : rlist -> A -> rlist.

Notation "[ ]" := rnil (format "[ ]") : rlist_scope.
Notation "xs ;; x" := (rsnoc xs x) (at level 50, left associativity) 
                      : rlist_scope.

Open Scope rlist_scope.

Fixpoint RIn {A:Set} (a:A) (rl:rlist (A:=A)) : Prop :=
  match rl with
    | [] => False
    | rl';;x => x = a \/ RIn a rl'
  end.

Close Scope rlist_scope.
