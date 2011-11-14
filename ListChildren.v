Require Import String.
Require List.
Require Import Children.
Require Import Util.

Module ListChildren : MChildren.

(* 一人の子供の型 *)
Definition child := string.
Definition eq_dec : forall x y:child, {x=y}+{x<>y} := string_dec.

(* childの有限集合の型 *)
Definition cset := list string.

Definition empty : cset := nil.

Axiom exists_dec : forall (P: child -> Prop) (f:forall c, {P c}+{~P c}),
  {exists c, P c}+{forall c, ~P c}.

Definition filter (f: child -> bool) cs := List.filter f cs.

Definition In (c: child) (cs:cset) := List.In c cs.

Axiom empty_in : forall c, ~In c empty.

Definition Subset xs ys := forall x, In x xs -> In x ys.

Lemma filter2_subset : forall f g xs,
  (forall x, f x = true -> g x = true) ->
  Subset (filter f xs) (filter g xs).
Proof.
 intros f g xs H; induction xs.
  intros c HH. destruct HH.

  simpl.
  case_eq (f a); intro eq.
   rewrite (H a eq).
   apply subset_conscons. apply IHxs.

   destruct (g a); [apply subset_cons|]; apply IHxs.
Qed.

Definition size (cs: cset) : nat := List.length (div_eq eq_dec cs).

Lemma size_in : forall xs ys,
  Subset xs ys -> size xs <= size ys.
Proof.
 apply div_equiv_aux_length.
Qed.

Lemma filter_length_lt : forall f g xs,
  (exists x, In x xs /\ f x <> true /\ g x = true) ->
  Subset (filter f xs) (filter g xs) ->
  size (filter f xs) < size (filter g xs).
Proof.
 intros.
 apply div_eq_length2.
  apply H0.

  destruct H. destruct H. destruct H1.
  exists x. split.
   intro.
SearchPattern(List.In _ (List.filter _ _) -> _).
 : forall {A:Type} (neqdec : forall x y: A, {x<>y}+{x=y})

Parameter add : child -> cset -> cset.

Axiom add_in : forall c0 c1 cs, In c0 (add c1 cs) -> c0 = c1 \/ In c0 cs.

(* 帰納法の原理 *)
Axiom ind : forall (P : cset -> Type),
  (P empty) ->
  (forall x xs, P xs -> P (add x xs)) ->
  forall cs, P cs.

Definition fold {A:Set} (f: child -> A -> A) (cs : cset) (a:A) : A :=
  ind (fun _ => A) a (fun c cs reccall => f c reccall) cs.

Axiom fold_empty : forall {A:Set} f (a:A),
  fold f empty a = a.

Axiom fold_step : forall {A:Set} f (a:A) c cs,
  (forall x y, f x (f y a) = f y (f x a)) ->
  fold f (add c cs) a = f c (fold f cs a).


(* 少なくとも一人は存在する。 *)
Parameter c0 : child.

(* すべての子供たち *)
Parameter children : cset.

Axiom children_finite : forall c, In c children.

End ListChildren.
