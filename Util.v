Require Import List.
Require Import Sumbool.

Definition Subset {A:Type} xs ys := forall (x:A), In x xs -> In x ys.

Lemma subset_conscons : forall {A:Type} (x:A) xs ys,
  Subset xs ys -> Subset (x :: xs) (x :: ys).
Proof.
  firstorder.
Qed.

Lemma subset_cons : forall {A:Type} (x:A) xs ys,
  Subset xs ys -> Subset xs (x :: ys).
Proof.
  firstorder.
Qed.

Fixpoint filter_dec {A : Type} {P Q: A -> Prop}
  (f : forall x, {P x} + {Q x}) (l:list A) : list A :=
  match l with 
  | nil => nil
  | x :: l => if (f x) then x::(filter_dec f l) else filter_dec f l
  end.

Lemma filter_dec_In_stronger : forall {A: Type} {P Q: A -> Prop} (f : forall x, {P x} + {Q x}) (x:A) (l: list A),
  In x (filter_dec f l) -> In x l /\ (exists p : P x, f x = left (Q x) p).
Proof.
  intros A P Q f x l H.
  induction l; [ simpl in H; tauto | ].
  simpl in *.
  split;
    [destruct (f a); simpl in H; try tauto
    | case_eq (f a); [intros p H0 | intros q H0]; rewrite H0 in H].
  (* p *)
    simpl in H.
    destruct H;
      [ subst a; exists p; exact H0
      | destruct (IHl H); tauto].
  (* q *)
    destruct (IHl H); tauto.
Qed.

Lemma filter_dec_In : forall {A: Type} {P Q: A -> Prop} (f : forall x, {P x} + {Q x}) (x:A) (l: list A),
  In x (filter_dec f l) -> In x l /\ P x.
Proof.
  intros A P Q f x l H.
  destruct (filter_dec_In_stronger f x l H) as [H0 [p H1]].
  exact (conj H0 p).
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
Proof.
  intros A P Q f xs x H.
  induction xs.
  (* base case *)
  auto. (* simpl in *; exact H. *)
  (* induction step *)
  simpl.
  simpl in H.
  destruct (f a) in H.
  elim H; auto.
  auto.
Qed.  

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

Lemma filter_dec_In_f : forall {A:Type} {P Q:A ->Prop} (f:forall x, {P x}+{Q x}) (x:A) (l:list A) (H:In x l), if (f x) then In x (filter_dec f l) else ~ In x (filter_dec f l).
Proof.
  intros A P Q f x l H.
  case_eq (f x); [intros p Hl | intros q Hr].
  (* In x (filter_dec f l) *)
    induction l; auto.
    simpl in *.
    destruct H.
    (* a = x *)
      rewrite H in *; clear H.
      rewrite Hl; clear Hl.
      simpl.
      left; reflexivity.
    (* In x l *)
      destruct (f a); simpl; auto.
  (* ~ In x (filter_dec f l) *)
    induction l.
    (* base case *)
      simpl in H; tauto.
    (* induction step *)
      intro Habsurd.
      simpl in Habsurd.
      generalize (filter_incl f l x); intro Hincl.
      case_eq (f a); [intros p0 Hp0 | intros q0 Hq0].
      (* p0 *)
        assert (a = x -> False) as ax;
          [intro; subst a; rewrite Hr in Hp0; discriminate | ].
        destruct H; [auto | change (In x l) in H].
        rewrite Hp0 in Habsurd.
        simpl in Habsurd.
        destruct Habsurd; [auto | firstorder].
      (* q0 *)
        rewrite Hq0 in Habsurd.
        exact (IHl (Hincl Habsurd) Habsurd).
Qed.

Lemma filter_dec_In_f_r : forall {A: Type} {P Q: A -> Prop} (f : forall x, {P x} + {Q x}) (x:A) (l: list A),
  In x l /\ (exists p : P x, f x = left (Q x) p)
  -> In x (filter_dec f l).
Proof.
  intros A P Q f x l H.
  induction l.
  (* base case *)
    simpl in H; destruct H; auto.
  (* induction step *)
    simpl in *.
    generalize (filter_dec_In_f f x l); intro Hf.
    destruct H as [H Hp].
    destruct H.
    (* a = x *)
      destruct Hp as [p Hp].
      subst a.
      destruct (f x);
        [simpl; auto | discriminate].
    (* In x l *)
      assert (In x (filter_dec f l)) as IHl';
        [exact (IHl (conj H Hp)) | clear IHl].
      destruct (f a); simpl; auto.
Qed.

Lemma filter_dec_In_r_weaker : forall {A: Type} {P Q: A -> Prop} (f : forall x, {P x} + {Q x}) (x:A), ~ (P x /\ Q x) -> forall (l: list A),
  In x l /\ P x -> In x (filter_dec f l).
Proof.
  intros A P Q f x npq.
  induction l.
  (* base case *)
    simpl; tauto.
  (* induction step *)
    intro H; destruct H as [H H0].
    simpl in H.
    destruct H.
    (* a = x *)
      simpl.
      destruct (f a); rewrite H in *; simpl; tauto.
    (* In x l *)
      generalize (IHl (conj H H0)); clear IHl; intro IHl.
      simpl; destruct (f a); simpl; auto.
Qed.

Lemma filter_In : forall {A:Type} {P Q:A->Prop} xs ys f (a:A),
  (In a xs -> In a ys) -> In a (@filter_dec A P Q f xs) ->
  In a (filter_dec f ys).
Proof.
  intros A P Q xs ys f a Hxsys Haxs.
  generalize (filter_dec_In_f f a xs); intro Hf.
  generalize (filter_dec_In_stronger f a xs Haxs); intro H.
  destruct H as [H [p Hp]].
  rewrite Hp in Hf.
  generalize (Hxsys H); clear Hxsys; intro Hxsys.
  generalize (Hf H); clear Hf; intro Hf.
  refine (filter_dec_In_f_r f a ys (conj Hxsys _)).
  exists p; exact Hp.
Qed.

Lemma filter_equiv : forall {A:Type} (P Q P' Q':A->Prop)
  (f:forall x:A,{P x}+{P' x}) (g:forall x:A, {Q x}+{Q' x}) xs,
  (forall x, P x <-> Q x) -> filter_dec f xs = filter_dec g xs.
Admitted.

Section Falsity_of_filter_equiv.
  Definition A := nat.
  Definition P := fun x : A => True.
  Definition f := fun x : A => left (P x) I.
  Definition g := fun x : A => right (P x) I.
  Definition xs := (0 :: nil) : list A.
  Definition discriminator :=
    fun xs : list A => if xs then False else True.
  Theorem falsity : False.
  Proof.
    refine (eq_ind (filter_dec f xs) discriminator I (filter_dec g xs) (filter_equiv P P P P f g xs _)).
    tauto.
  Qed.
End Falsity_of_filter_equiv.

Lemma filter_filter : forall {A:Type} (P Q P' Q':A->Prop)
  (f:forall x:A,{P x}+{P' x}) (g:forall x:A, {Q x}+{Q' x}) xs,
  filter_dec f (filter_dec g xs) = filter_dec g (filter_dec f xs).
Proof.
  intros A P Q P' Q' f g xs.
  induction xs; simpl; [auto | ].
  case_eq (g a);
    [ intros pg Hpg; case_eq (f a); [intros pf Hpf | intros qf Hqf]
    | intros qg Hqg; case_eq (f a); [intros pf Hpf | intros qf Hqf] ].

  simpl.
  rewrite Hpg,Hpf,IHxs.
  reflexivity.

  simpl.
  rewrite Hqf,IHxs.
  reflexivity.

  simpl.
  rewrite Hqg,IHxs.
  reflexivity.

  simpl.
  rewrite IHxs.
  reflexivity.
Qed.

Section filterb.
  Variable A : Type.
  Variable f : A -> bool.

  Lemma filter_filter_dec : forall xs x,
    In x (filter f xs) ->
    In x (filter_dec (fun a => sumbool_of_bool (f a)) xs).
      intros xs x H.
      induction xs; [simpl in H; tauto | ].
      simpl in *.
      destruct (f a); simpl in *; [destruct H; tauto | tauto].
  Qed.

  Lemma filter_dec_filter : forall xs x,
    In x (filter_dec (fun a => sumbool_of_bool (f a)) xs) ->
    In x (filter f xs).
      intros xs x H.
      induction xs; [simpl in H; tauto | ].
      simpl in *.
      destruct (f a); simpl in *; [destruct H; tauto | tauto].
  Qed.

  Lemma filter_spec1 : forall xs x,
    In x (filter f xs) -> In x xs /\ f x = true.
  Proof.
    intros xs x H.
    apply (filter_dec_In (fun a => sumbool_of_bool (f a)) x xs).
    apply filter_filter_dec.
    assumption.
  Qed.

  Lemma filter_spec2 : forall xs x,
    In x xs -> f x = true -> In x (filter f xs).
  Proof.
    intros xs x H H0.
    apply (filter_dec_filter).
    apply (filter_dec_In_f_r (fun a => sumbool_of_bool (f a)) x xs).
    split; [assumption | ].
    exists H0.
    rewrite H0.
    simpl.
    reflexivity.
  Qed.
End filterb.

Section Equiv.
  Require Import Arith.
  Variable A : Type.
  Variable R : A -> A -> Prop.

  Variable R_refl : forall x, R x x.
  Variable R_comm : forall x y, R x y -> R y x.
  Variable R_trans : forall x y z, R x y -> R y z -> R x z.

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

    Lemma div_equiv_aux_cons : forall xs x,
      div_equiv_aux (x::xs) = x :: div_equiv_aux(filter_dec (neqdec x) xs).
    Proof.
     intros. rewrite div_equiv_aux_equation. reflexivity.
    Qed.

    Lemma filter_In_length : forall xs a,
      In a xs -> S (length(filter_dec (neqdec a) xs)) <= length xs.
    Proof.
     induction xs.
      intros a H; inversion H.
      
      simpl. intros y H. apply le_n_S. destruct H.
       rewrite H. destruct (neqdec y y); [destruct n; apply R_refl |].
       apply filter_dec_length.

       destruct (neqdec y a); [| apply le_Sn_le]; apply IHxs; apply H.
    Qed.

    Lemma div_In_length : forall xs a b,
      In a xs -> R a b ->
      length (div_equiv_aux xs) = S (length (div_equiv_aux (filter_dec (neqdec b) xs))).
    Proof.
     intro xs. functional induction (div_equiv_aux xs).
      intros. inversion H.

      simpl. intros. destruct (neqdec x a).
       (* ~ R x a *)
       destruct (neqdec b x);
         [| destruct n; apply R_comm; apply (R_trans _ _ _ H0 r)].
       rewrite div_equiv_aux_cons. simpl.
       destruct H; [destruct n; rewrite H; apply R_refl |].
       rewrite (IHl a b); [| | apply H0].
        rewrite filter_filter. reflexivity.

        apply filter_dec_In_not2; [apply H | apply n].

       (*   R x a *)
       destruct (neqdec b x);
         [destruct n; apply R_comm; apply (R_trans _ _ _ r H0) | ].
       erewrite filter_equiv; [reflexivity |].
       intro e; split.
        intros HH Rbe. destruct HH. apply R_comm in r0.
        apply (R_trans _ _ _ r0 Rbe).

        intros HH Rxe. destruct HH. apply (R_trans _ _ _ r0 Rxe).
    Qed.

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
      In x xs -> exists y, R x y /\ In y (div_equiv_aux xs).
    Proof.
     intros x xs. revert x. functional induction (div_equiv_aux xs).
      intros x H. inversion H.
      intros. simpl in H. destruct H.
       exists x. rewrite H. split; [apply R_refl | left; reflexivity].

       destruct (neqdec x x0).
        destruct (IHl x0).
         apply filter_dec_In_not2; [apply H | apply n].

         exists x1. destruct H0. split; [apply H0 | right; apply H1].

        exists x. split; [apply (R_comm _ _ r) | left; reflexivity].
    Qed.


    Lemma div_length : forall xs,
      length (div_equiv_aux xs) <= length xs.
    Proof.
     intro xs. functional induction (div_equiv_aux xs).
      apply le_refl.
      
      simpl. apply le_n_S. eapply le_trans; [apply IHl |].
      apply filter_dec_length.
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

Section DivEq.
  Variable A : Type.
  Variable dec : forall x y: A, {x=y} + {x<>y}.
  Definition neqdec x y := sumbool_not _ _ (dec x y).
  Lemma eq_refl : forall (x:A), x=x. reflexivity. Qed.
  Lemma eq_comm : forall (x y:A), x=y -> y=x. auto. Qed.
  Lemma eq_trans : forall (x y z:A), x=y -> y=z -> x=z. apply eq_trans. Qed.
    
  Definition div_eq xs := div_equiv dec xs.

  Lemma div_eq_cons : forall xs x,
    div_eq (x :: xs) = x :: div_eq (filter_dec (neqdec x) xs).
  Proof.
   intros. apply div_equiv_aux_cons.
  Qed.

  Lemma div_eq_aux_length : forall xs ys,
    (forall x, In x xs -> In x ys) ->
    length(div_eq xs) <= length(div_eq ys).
  Proof.
    intro xs. functional induction (div_equiv_aux A _ neqdec xs).   
     intros. apply le_0_n. 

     intros. simpl.
     apply (le_trans _ (S(length(div_equiv_aux _ _ neqdec (filter_dec (neqdec x) (div_equiv_aux A _ neqdec ys)))))).

      (* len (div (filter x xs0)) <= len (div (filter x (div ys))) *)
      rewrite div_eq_cons.
      apply le_n_S. apply IHl. intros a. apply filter_In.
      intro HH. destruct (div_In_incl_aux_inv A eq eq_refl eq_comm neqdec a ys);
        [apply H; right; apply HH|].
      destruct H0 as [HH1 HH2]. rewrite HH1. apply HH2.

      apply (le_trans _ (S(length (filter_dec (neqdec x) (div_equiv_aux _ _ neqdec ys))))).
       (* len (div (filter x (div ys))) <= len (filter x (div ys)) *)
       apply le_n_S. apply div_length.

       (* S(len(filter x (div ys))) <= len(div ys) *)
       apply filter_In_length; [apply eq_refl|].
       destruct (div_In_incl_aux_inv _ _ eq_refl eq_comm neqdec x ys);
          [apply H; left; reflexivity |].
       destruct H0 as [HH1 HH2]. rewrite HH1. apply HH2.
     Qed.

Lemma div_eq_length2 : forall (xs ys : list A),
  (forall x, In x xs -> In x ys) ->
  (exists a, ~In a xs /\ In a ys) ->
  length(div_equiv_aux _ _ neqdec xs) < length(div_equiv_aux _ _ neqdec ys).
Proof.
 intros xs. functional induction (div_equiv_aux _ _ neqdec xs).
  intros. destruct H0. destruct H0.
  erewrite (div_In_length A _ eq_refl eq_comm eq_trans neqdec _ _ _ H1); [|reflexivity].
  apply lt_0_Sn.

  intros.
  rewrite (div_In_length A _ eq_refl eq_comm eq_trans neqdec ys x x); [|apply H; left; reflexivity |reflexivity].
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
End DivEq.