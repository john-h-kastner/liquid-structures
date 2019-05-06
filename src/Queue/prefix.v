(* I prototyped the prefix inductive predicate in Coq before implementing it in
 * Liquid Haskell. Having this file might be useful when making changes to the
 * Haskell version, especially for anyone more familiar with Coq. *)

Require Import Coq.Lists.List.
Import ListNotations.

Inductive prefix : forall T:Type, list T -> list T -> Prop :=
| Prefix_Emp  : forall T l,
    prefix T [] l
| Prefix_Cons : forall T h k l,
    prefix T (k) (l) ->
    prefix T (h::k) (h::l).

Example test_prefix : prefix _ [] [1].
Proof. apply Prefix_Emp. Qed.

Example test_prefix' : prefix _ [1] [1].
Proof. repeat constructor. Qed.

Example test_prefix'' : prefix _ [1] [1; 2].
Proof. repeat constructor. Qed.

Lemma prefix_refl : forall T l, prefix T l l.
Proof.
  intros.
  induction l.
  - apply Prefix_Emp.
  - apply Prefix_Cons.
    apply IHl.
Qed.

Lemma prefix_app : forall T l0 l1 l2,
  prefix T l0 l1 ->
  prefix T l0 (app l1 l2).
Proof.
  intros.
  induction H.
  - apply Prefix_Emp.
  - apply Prefix_Cons.
    apply IHprefix.
Qed.

Lemma prefix_app_self : forall T l0 l1, prefix T l0 (app l0 l1).
Proof.
  intros.
  apply prefix_app.
  apply prefix_refl.
Qed.

Lemma prefix_rem_last : forall T l0 l1,
  prefix T l0 l1 ->
  prefix T (removelast l0) l1.
Proof.
  intros.
  induction H; try destruct k; constructor; assumption.
Qed.

Example test_prefix''' : prefix _ [1; 2; 3; 4; 5] [1; 2; 3; 4; 5; 6].
Proof.
  (*repeat constructor.*)
  replace ([1; 2; 3; 4; 5]) with (removelast [1; 2; 3; 4; 5; 6]) by reflexivity.
  apply prefix_rem_last.
  apply prefix_refl.
Qed.

Example test_prefix'''' : prefix _ [1; 2; 3; 4; 5] [1; 2; 3; 4; 5; 6].
Proof.
  (*repeat constructor.*)
  (*replace ([1; 2; 3; 4; 5; 6]) with (app [1; 2; 3; 4; 5] [6]) by reflexivity.
  apply prefix_app_self.*)
  apply (prefix_app_self _ [1; 2; 3; 4; 5] [6]).
Qed.

Example test_prefix''''' : forall T h0 l0, exists h1 l1, prefix T (h1::l1) (h0::l0).
Proof.
  intros.
  exists h0, [].
  repeat constructor.
Qed.
