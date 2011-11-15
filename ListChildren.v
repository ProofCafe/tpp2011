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

Definition filter (f: child -> bool) cs := List.filter f cs.

Definition In (c: child) (cs:cset) := List.In c cs.

Lemma empty_in : forall c, ~In c empty.
Proof.
 intros c H; inversion H.
Qed.

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
   intro. edestruct (filter_spec1 _ f); [apply H3|].
   destruct H1. apply H5.

   apply  (filter_spec2); [apply H| apply H2].
Qed.

Definition add (c: child) cs := List.cons c cs.

Lemma add_in : forall c0 c1 cs, In c0 (add c1 cs) -> c0 = c1 \/ In c0 cs.
Proof.
 intros c d cs H. inversion H; [left;rewrite H0; reflexivity | right; apply H0].
Qed.

(* 帰納法の原理 *)
Definition ind : forall (P : cset -> Type),
  (P empty) ->
  (forall x xs, P xs -> P (add x xs)) ->
  forall cs, P cs.
Proof.
 intros P Hemp Hstep. induction cs; [apply Hemp | apply Hstep; apply IHcs].
Defined.

Definition fold {A:Set} (f: child -> A -> A) (cs : cset) (a:A) : A :=
  ind (fun _ => A) a (fun c cs reccall => f c reccall) cs.

Lemma fold_empty : forall {A:Set} f (a:A),
  fold f empty a = a.
Proof.
 reflexivity.
Qed.

Lemma fold_step : forall {A:Set} f (a:A) c cs,
  (forall x y, f x (f y a) = f y (f x a)) ->
  fold f (add c cs) a = f c (fold f cs a).
Proof.
 reflexivity.
Qed.

(* 少なくとも一人は存在する。 *)
Parameter c0 : child.

(* すべての子供たち *)
Parameter children : cset.

Axiom children_finite : forall c, In c children.

Definition exists_dec : forall (P: child -> Prop) (f:forall c, {P c}+{~P c}),
  {exists c, P c}+{forall c, ~P c}.
Proof.
 intros P f.
 cut(forall cs, {exists c, In c cs /\ P c} + {forall c, In c cs -> ~ P c}).
  intros. destruct (H children); [left | right].
   destruct e as [c Hc]. exists c. destruct Hc. apply H1.
   intro c. apply (n c (children_finite c)).

  induction cs.
   right. intros c H. inversion H.

   simpl. destruct (f a).
    left. exists a. split; [left; reflexivity | apply p].

    destruct IHcs; [left | right].
     destruct e as [c Hc]. destruct Hc. exists c.
     split; [right; apply H| apply H0].

     intros c Hc. destruct Hc; [rewrite <- H; apply n | apply (n0 c H)].
Qed.

End ListChildren.
