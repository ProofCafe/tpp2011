Require Import String.
Require Import MSetList.

Definition t := nat.
Module Children := MSetList.Make(NatOrderedType.Nat_as_OT).

Parameter children : Children.t.

Axiom children_finite : forall c, Children.In c children.

Parameter exists_dec : forall (P: t -> Prop) (f:forall c, {P c}+{~P c}),
  {exists c, P c}+{forall c, ~P c}.


Check Children.filter.
Check Children.min_elt.

Definition fold := Children.fold.

Parameter max min : nat -> nat.

Axiom min_minimum : forall k c, min k <= m(c, k).
Axiom max_maximum : forall k c, m(c, k) <= max k.
Axiom min_exists : forall k, exists c, m(c, k) = min k.



Parameter num : candy * nat -> nat.
