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
  (exists x, In x xs /\ f x <> true /\ g x = true) ->
  Subset (filter f xs) (filter g xs) ->
  size (filter f xs) < size (filter g xs).

Parameter empty : cset.

Axiom empty_in : forall c, ~In c empty.

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

End MChildren.
