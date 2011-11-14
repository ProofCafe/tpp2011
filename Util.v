Require Import List.
Require Import Sumbool.

Definition Subset {A:Type} xs ys := forall (x:A), In x xs -> In x ys.

Lemma subset_conscons : forall {A:Type} (x:A) xs ys,
  Subset xs ys -> Subset (x :: xs) (x :: ys).
Admitted.

Lemma subset_cons : forall {A:Type} (x:A) xs ys,
  Subset xs ys -> Subset xs (x :: ys).
Admitted.

Fixpoint filter_dec {A : Type} {P Q: A -> Prop}
  (f : forall x, {P x} + {Q x}) (l:list A) : list A :=
  match l with 
  | nil => nil
  | x :: l => if (f x) then x::(filter_dec f l) else filter_dec f l
  end.

Lemma filter_dec_In : forall {A: Type} {P Q: A -> Prop} (f : forall x, {P x} + {Q x}) (x:A) (l: list A),
  In x (filter_dec f l) -> In x l /\ P x.
Proof.
intros A P Q f.
 induction l; simpl.
  intro H; elim H.
  
  case (f a); simpl in |- *.
   intros H _H; elim _H; intros.
    split; [ left | rewrite <- H0 in |- * ]; assumption.
    
    elim (IHl H0); intros.
    split; [ right | idtac ]; assumption.
    
   intros _ H; elim (IHl H); intros.
   split; [ right | idtac ]; assumption.
Qed.


Lemma filter_dec_length : forall {A: Type} {P Q: A -> Prop} (f : forall x, {P x} + {Q x}) (xs: list A),
  length (filter_dec f xs) <= length xs.
Proof.
intros A P Q f xs; induction xs; simpl.
 apply Le.le_refl.

 case (f a); intro; simpl.
  apply Le.le_n_S; apply IHxs.

  apply le_S; apply IHxs.
Qed.

Lemma filter_incl : forall {A:Type} {P Q: A -> Prop} (f : forall x, {P x}+{Q x})
  (xs : list A) x,
  In x (filter_dec f xs) -> In x xs.
Admitted.

Lemma filter_dec_In_not1 : forall {A: Type} {P: A -> Prop} (f : forall x, {P x} + {~P x}) (x:A) (xs: list A),
  In x xs -> P x -> In x (filter_dec f xs).
Proof.
intros A P f x xs; induction xs; simpl.
intro H; elim H.
intros.
case (f a).

elim H; intro HH; [rewrite HH; left; reflexivity | right; apply (IHxs HH H0)].
elim H; intro HH; [rewrite HH; intro HH0; elim HH0; apply H0 | intros _; apply (IHxs HH H0)].
Qed.

Lemma filter_dec_In_not2 : forall {A: Type} {P: A -> Prop} (f : forall x, {~P x} + {P x}) (x:A) (xs: list A),
  In x xs -> ~ P x -> In x (filter_dec f xs).
Proof.
intros A P f x xs; induction xs; simpl.
intro H; elim H.
intros.
case (f a).

elim H; intro HH; [rewrite HH; left; reflexivity | right; apply (IHxs HH H0)].
elim H; intro HH; [rewrite HH; intro HH0; elim H0; apply HH0 | intros _; apply (IHxs HH H0)].
Qed.

Lemma filter_In : forall {A:Type} {P Q:A->Prop} xs ys f (a:A),
  (In a xs -> In a ys) -> In a (@filter_dec A P Q f xs) ->
  In a (filter_dec f ys).
Admitted.
Section filterb.
  Variable A : Type.
  Variable f : A -> bool.

  Lemma filter_spec1 : forall xs x,
    In x (filter f xs) -> In x xs /\ f x = true.
  Admitted.

  Lemma filter_spec2 : forall xs x,
    In x xs -> f x = true -> In x (filter f xs).
  Admitted.
End filterb.

Section Equiv.
  Require Import Arith.
  Variable A : Type.
  Variable R : A -> A -> Prop.

  Variable R_refl : forall x, R x x.

  Section EquivAux.
    Variable neqdec : forall (x y: A), {~R x y} + {R x y}.
    Require Import Recdef.
    Function div_equiv_aux (xs : list A) {measure length xs} : list A :=
      match xs with
      | nil => nil
      | x :: xs => x :: div_equiv_aux (filter_dec (neqdec x) xs)
    end.
    intros.
    simpl.
    apply Lt.le_lt_n_Sm.
    apply filter_dec_length.
    Defined.

    Lemma filter_In_length : forall xs a,
      In a xs -> S (length(filter_dec (neqdec a) xs)) <= length xs.
    Admitted.

    Lemma div_In_length : forall xs a b,
      In a xs -> R a b ->
      length (div_equiv_aux xs) = S (length (div_equiv_aux (filter_dec (neqdec b) xs))).
    Admitted.

    Lemma div_In_aux : forall (x:A) (xs: list A),
      In x xs -> exists x':A, R x' x /\ In x' (div_equiv_aux xs).
    Proof.
    intros x xs; functional induction (div_equiv_aux xs).

     intro H; elim H.

     intro H0; elim H0; intro H.
     rewrite H; exists x.
     split; [apply R_refl | left; reflexivity].

     case (neqdec x0 x); intro HH.

      elim (IHl (filter_dec_In_not2 (neqdec x0) _ _ H HH)).
      intros x' _H; inversion _H; exists x'.
      split; [apply H1 | right; apply H2].

     exists x0; split; [apply HH | left; reflexivity].
    Qed.

    Lemma div_In_incl_aux : forall (x:A) (xs: list A),
      In x (div_equiv_aux xs) -> In x xs.
    Proof.
    intros x xs; functional induction (div_equiv_aux xs).
     intro H; elim H.

     simpl; intro _H; elim _H; intro HH; [left; apply HH | right].
 
     elim (filter_dec_In _ _ _ (IHl HH)).
     intros H1 _; apply H1.
    Qed.

    Lemma div_In_incl_aux_inv : forall (x:A) (xs: list A),
      In x xs -> In x (div_equiv_aux xs).
    Admitted.


    Lemma div_length : forall xs,
      length (div_equiv_aux xs) <= length xs.
    Admitted.

    Lemma div_equiv_aux_length : forall xs ys,
      (forall x, In x xs -> In x ys) ->
      length(div_equiv_aux xs) <= length(div_equiv_aux ys).
    Proof.
    intro xs. functional induction (div_equiv_aux xs).   
     intros. apply le_0_n. 

     intros. simpl.
     apply (le_trans _ (S(length(div_equiv_aux (filter_dec (neqdec x) (div_equiv_aux ys)))))).
      (* len (div (filter x xs0)) <= len (div (filter x (div ys))) *)
      apply le_n_S. apply IHl. intros a. apply filter_In.
      intro HH. apply div_In_incl_aux_inv. apply H.
      right. apply HH.

      apply (le_trans _ (S(length (filter_dec (neqdec x) (div_equiv_aux ys))))).
       (* len (div (filter x (div ys))) <= len (filter x (div ys)) *)
       apply le_n_S. apply div_length.

       (* S(len(filter x (div ys))) <= len(div ys) *)
       apply filter_In_length. apply div_In_incl_aux_inv. apply H.
       left. reflexivity.
    Qed.

  End EquivAux.

  Variable eqdec : forall (x y: A), {R x y} + {~R x y}.
  Definition div_equiv xs := div_equiv_aux (fun x y => sumbool_not _ _ (eqdec x y)) xs.

  Lemma div_In : forall (x:A) (xs: list A),
    In x xs -> exists x':A, R x' x /\ In x' (div_equiv xs).
  Proof.
  apply div_In_aux.
  Qed.

  Lemma div_In_incl : forall (x:A) (xs: list A),
    In x (div_equiv xs) -> In x xs.
  Proof.
  apply div_In_incl_aux.
  Qed.
End Equiv.
Implicit Arguments div_equiv [A R].

Definition div_eq {A:Type} (dec : forall x y:A, {x=y}+{x<>y}) xs :=
  div_equiv dec xs.

Lemma div_eq_length2 : forall {A:Type} (neqdec : forall x y: A, {x<>y}+{x=y})
  (xs ys : list A),
  (forall x, In x xs -> In x ys) ->
  (exists a, ~In a xs /\ In a ys) ->
  length(div_equiv_aux _ _ neqdec xs) < length(div_equiv_aux _ _ neqdec ys).
Proof.
 intros A neqdec xs. functional induction (div_equiv_aux _ _ neqdec xs).
  intros. destruct H0. destruct H0.
  erewrite (div_In_length _ _ neqdec _ _ _ H1); [|reflexivity].
  apply lt_0_Sn.

  intros.
  rewrite (div_In_length A _ neqdec ys x x); [|apply H; left; reflexivity |reflexivity].
  simpl. apply lt_n_S. apply IHl.
   (* In a (filter x xs0) -> In a (filter x ys) *)
   intros xx HH.
   apply filter_dec_In_not2.
    (* In xx ys *)
    apply H.  right. eapply filter_incl. apply HH.

    (* x <> xx *)
    intro eq. rewrite eq in HH.
    destruct (filter_dec_In (neqdec xx) _ _ HH). destruct H2. reflexivity.

   (* exists a, ~In a (filter x xs0) /\ In a (filter x ys) *)
   destruct H0 as [a H0]. destruct H0.
   exists a. split.
    (* ~In a (fil x xs0) *)
    intro; destruct H0. right. eapply filter_incl. apply H2.

    (* In a (fil x ys) *)
    eapply filter_dec_In_not2; [apply H1 |].
    intro; destruct H0. left. apply H2.
Qed.
