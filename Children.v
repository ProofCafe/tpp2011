Module Type MChildren.

(* 一人の子供の型 *)
Parameter child : Set.

(* childの有限集合の型 *)
Parameter cset : Set.

Axiom exists_dec : forall (P: child -> Prop) (f:forall c, {P c}+{~P c}),
  {exists c, P c}+{forall c, ~P c}.

Parameter filter : (child -> bool) -> cset -> cset.

Parameter In : child -> cset -> Prop.

Definition Subset xs ys := forall x, In x xs -> In x ys.

Axiom filter2_subset : forall f g xs,
  (forall x, f x = true -> g x = true) ->
  Subset (filter f xs) (filter g xs).

Parameter size : cset -> nat.

Axiom size_in : forall xs ys,
  Subset xs ys -> size xs <= size ys.

Axiom filter_length_lt : forall f g xs,
  (exists x, f x <> true /\ g x = true) ->
  Subset (filter f xs) (filter g xs) ->
  size (filter f xs) < size (filter g xs).

Parameter fold : forall {A:Set}, (child -> A -> A) -> A -> cset -> A.

(* 少なくとも一人は存在する。 *)
Parameter c0 : child.

(* すべての子供たち *)
Parameter children : cset.

Axiom children_finite : forall c, In c children.

End MChildren.