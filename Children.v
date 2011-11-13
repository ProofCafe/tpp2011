Require Import String.
Require Import MSetList.

Definition t := nat.
Module CSet := MSetList.Make(NatOrderedType.Nat_as_OT).

Parameter children : CSet.t.

Axiom children_finite : forall c, CSet.In c children.

Parameter exists_dec : forall (P: t -> Prop) (f:forall c, {P c}+{~P c}),
  {exists c, P c}+{forall c, ~P c}. (*TODO*)

Definition filter := CSet.filter.

Lemma filter2_subset : forall f g xs,
  (forall x, f x = true -> g x = true) ->
  CSet.Subset (filter f xs) (filter g xs).
Admitted. (*TODO*)

Lemma filter_length_lt : forall f g xs,
  (exists x, f x <> true /\ g x = true) ->
  CSet.Subset (filter f xs) (filter g xs) ->
  CSet.cardinal (filter f xs) < CSet.cardinal (filter g xs).
Admitted. (*TODO*)

Definition fold := CSet.fold.
Definition size := CSet.cardinal.

(*
Axiom min_minimum : forall k c, min k <= m(c, k).
Axiom max_maximum : forall k c, m(c, k) <= max k.
Axiom min_exists : forall k, exists c, m(c, k) = min k.



Parameter num : candy * nat -> nat.
*)