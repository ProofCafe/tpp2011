Require Import Arith.
Require Import Even.
Require Import Div2.

Parameter child : Set.
Parameter right : child -> child.

(* number of candies *)
Definition candy : Set := nat.

(* initial candies for children *)
Parameter m0 : child -> candy.
Axiom m0_even : forall c, even (m0 c).

Parameter exists_dec : forall (P: child -> Prop) (f:forall c, {P c}+{~P c}),
  {exists c, P c}+{forall c, ~P c}.

Definition m_aux : child -> nat -> {n | even n}.
 refine (fix iter c k : {n|even n} :=
   match k with
   | O => exist _ (m0 c) _
   | S k =>
     let (n, Hn) := iter c k in
     let (m, Hm) := iter (right c) k in
     let (half_mine, Ha)  := even_2n n Hn in
     let (half_right, Hb) := even_2n m Hm in
     if (even_odd_dec (half_mine + half_right)) then
       exist _ (half_mine + half_right) _
     else
       exist _ (S (half_mine + half_right)) _
   end).
 apply m0_even.

 apply _H.

 apply even_S. apply _H.
Defined.

Definition m (c_k: child*nat) : candy :=
  let (c,k) := c_k in proj1_sig (m_aux c k).

Lemma m_even : forall c k, even(m(c, k)).
Proof.
 intros c k; simpl. destruct (m_aux c k). apply e.
Qed.

Parameter max min : nat -> nat.
Parameter num : candy * nat -> nat.

Axiom min_minimum : forall k c, min k <= m(c, k).
Axiom max_maximum : forall k c, m(c, k) <= max k.
Axiom min_exists : forall k, exists c, m(c, k) = min k.
Axiom max_exists : forall k, exists c, m(c, k) = max k.

Lemma min_max : forall k, min k <= max k.
Proof.
 intro k. destruct (min_exists k). rewrite <- H. apply max_maximum.
Qed.

(* 1 *)
Lemma l1 : forall k, max (S k) <= max k.
  intro k.
  cut (exists c, max (S k) <= m (c,k)). (* subgoal A introduced *)
  intro H.
  assert (forall c, m (c,k) <= max k); try apply max_maximum.
  destruct H.
  specialize H0 with x.
  Require Import Omega.
  omega. (* main goal reached *)
  Show.  
  assert (exists c, m(c,k) = max k); try apply max_exists.
  assert (forall c k, m (c,(S k)) <= max k).
  intros.
  simpl.
  case_eq (m_aux c k0).
  intros.
  case_eq (m_aux (right c) k0).
  intros.
  destruct (even_odd_dec (div2 x + div2 x0)).

  simpl.
  assert (x <= max k0).
    assert (x = m (c,k0)).
      simpl.
      rewrite H0.
      simpl.
      reflexivity.
    rewrite H2.
    apply max_maximum.
  assert (x0 <= max k0).
    assert (x0 = m (right c,k0)).
      simpl.
      rewrite H1.
      simpl.
      reflexivity.
    rewrite H3.
    apply max_maximum.
  assert (max k0 = div2 (max k0) + div2 (max k0)).
    assert (forall m, even m ->  m = div2 m + div2 m).
      apply even_double.
    assert (even (max k0)).
      generalize (max_exists k0).
      intros.
      destruct H5.
      rewrite <- H5.
      apply m_even.
    rewrite <- (H4 (max k0) H5).
    reflexivity.
  Check even_2n.
  generalize (even_2n x e).
  generalize (even_2n x0 e0).
  intros.
  destruct H5.
  destruct H6.
  rewrite e2,e3 in *.
  assert (forall n, 2 * n = double n).
    unfold double; intros; omega.
  rewrite <- (H5 x2), <- (H5 x1) in *.
  rewrite (div2_double x2),(div2_double x1).
  omega.

  simpl.
  assert (x <= max k0).
    assert (x = m (c,k0)).
      simpl.
      rewrite H0.
      simpl.
      reflexivity.
    rewrite H2.
    apply max_maximum.
  assert (x0 <= max k0).
    assert (x0 = m (right c,k0)).
      simpl.
      rewrite H1.
      simpl.
      reflexivity.
    rewrite H3.
    apply max_maximum.
  assert (max k0 = div2 (max k0) + div2 (max k0)).
    assert (forall m, even m ->  m = div2 m + div2 m).
      apply even_double.
    assert (even (max k0)).
      generalize (max_exists k0).
      intros.
      destruct H5.
      rewrite <- H5.
      apply m_even.
    rewrite <- (H4 (max k0) H5).
    reflexivity.
  Check even_2n.
  generalize (even_2n x e).
  generalize (even_2n x0 e0).
  intros.
  destruct H5.
  destruct H6.
  rewrite e1,e2 in *.
  assert (forall n, 2 * n = double n).
    unfold double; intros; omega.
  rewrite <- (H5 x2), <- (H5 x1) in *.
  rewrite (div2_double x2),(div2_double x1).
  apply lt_le_S.
  assert (x2 + x1 <= max k0 /\ x2 + x1 <> max k0 -> x2 + x1 < max k0).
    omega.
  apply H6.
  split.
  omega.
  rewrite (div2_double x2), (div2_double x1) in o.
  assert (even (max k0)).
    generalize (max_exists k0).
    intros.
    destruct H7.
    rewrite <- H7.
    apply m_even.
  intro.
  rewrite H8 in *.
  apply (not_even_and_odd (max k0) H7 o).

  generalize (max_exists (S k)).
  intro.
  destruct H.
  exists x.
  destruct H1.
  rewrite <- H1.
  rewrite H.
  apply H0.
Qed.

Lemma max_i : forall i k, max (i + k) <= max k.
Proof.
 induction i; simpl; intros; [apply le_refl | eapply le_trans; [apply l1| apply IHi]].
Qed.

(* 2 *)
Lemma l2_aux : forall k x, 
  (forall c, x <= m(c, k)) -> x <= min k.
Proof.
 intros.
 destruct (min_exists k) as [c HH].
 rewrite <- HH; apply H. 
Qed.
 
Require Import Omega.

Lemma l2 : forall k, min (k) <= min (S k).
Proof.
 intro k. apply l2_aux. intro c.
 simpl.
  generalize (min_minimum k c).
  generalize (min_minimum k (right c)). simpl.
 destruct (m_aux c k) as [nc Ec]. destruct (m_aux (right c) k) as [nr Er].
(* case_eq (m_aux c k). case_eq (m_aux (right c) k). intros nr Hr eq1 nc Hc eq2.*)
 destruct (even_2n _ Er) as [rhalf req].
 destruct (even_2n _ Ec) as [chalf ceq].
 simpl; intros.
 rewrite req; rewrite ceq.
 cut (forall n, double n = 2 * n); [intro eq | intros; unfold double; omega].
 rewrite (eq chalf). rewrite (eq rhalf).
 rewrite div2_double. rewrite div2_double.
 unfold double in req. unfold double in ceq.
 destruct (even_odd_dec (chalf + rhalf)); simpl.
  (* 偶数 *)
  omega.
  
  (* 奇数 *)
  omega.
Qed.

(* 3 *)
Lemma l3 : forall c k,
  min k < m(c, k) -> min k < m(c, S k).
Admitted.

Lemma div2_plus : forall a b,
  even a ->
  even b ->
  div2 a + div2 b = div2 (a + b).
Proof.
Admitted.


Lemma double_multi : forall n,
  double n = 2 * n.
Proof.
intros.
unfold double.
omega.
Qed.

Lemma double_lt: forall x y,
  double x < double y ->
  x < y.
Proof.
intros.
unfold double in H.
omega.
Qed.

(* 4 *)
Lemma l4 : forall k c,
  m(c, k) < m(right c, k) -> m(c, k) < m(c, S k).
Proof with auto.
unfold m, proj1_sig.
simpl.
intros.
destruct (m_aux c k).
destruct (m_aux (right c) k).
destruct (even_odd_dec (div2 x + div2 x0)).
 (* case: even (div2 x + div2 x0) *)
 apply even_2n in e.
 apply even_2n in e0.
 destruct e as [ p P ].
 destruct e0 as [ q Q ].
 rewrite P, Q in *.
 clear P Q.
 rewrite (double_multi p), (double_multi q).
 rewrite (div2_double p), (div2_double q).
 apply double_lt in H.
 omega.

 (* case: odd (div2 x + div2 x0) *)
 apply even_2n in e.
 apply even_2n in e0.
 destruct e as [ p P ].
 destruct e0 as [ q Q ].
 rewrite P, Q in *.
 clear P Q.
 rewrite (double_multi p), (double_multi q).
 rewrite (div2_double p), (div2_double q).
 apply double_lt in H.
 omega.
Qed.

(* 5 *)
Fixpoint fpow n {A:Type} (f: A -> A) x :=
  match n with
  | O => x
  | S m => f (fpow m f x)
  end.

Axiom rightpow : forall c d: child, exists n, d = fpow n right c.

Lemma exist_gap_aux : forall k n c,
  m(c, k) = min k -> min k < m(fpow n right c, k) ->
  exists c', m(c', k) = min k /\ m(c', k) < m(right(c'), k).
Proof.
 induction n; intros.
  (* case: O *)
  rewrite <- H in H0. destruct (lt_irrefl _ H0).

  (* case: S n *)
  destruct(le_lt_eq_dec (min k) (m(fpow n right c, k))); [apply min_minimum| |].
   (* min k < m (fpow n right c, k) のとき *)
   destruct (IHn c H l).
   exists x; apply H1.

   (* min k = m (fpow n right c, k) のとき *)
   exists (fpow n right c).
   split; [rewrite e; reflexivity | rewrite <- e; apply H0].
Qed.

Lemma exist_gap : forall k, (exists c, min k < m(c, k)) ->
  exists c', m(c', k) = min k /\ m(c', k) < m(right(c'), k).
Proof.
 intros.
 destruct (min_exists k) as [c Hc].
 destruct H as [d Hd].
 destruct (rightpow c d) as [n HH].
 apply (exist_gap_aux k n c Hc).
 rewrite HH in Hd; apply Hd.
Qed.

Lemma l5_aux : forall c k,
  m(c, k) = min k -> min k < m(c, S k) -> num(min k, S k) < num (min k, k).
(* use (3) and finite set's filter lemma*)
Admitted.
 
Lemma l5 : forall k,
  (exists c, min k < m(c, k)) -> num(min k, S k) < num(min k, k).
Proof.
 intros.
 destruct (exist_gap _ H) as [c HH].
 destruct HH.
 apply (l5_aux _ _ H0).
 rewrite <- H0. apply l4. apply H1.
Qed.

(* Main Theorem *)

Definition same k := forall c, m(c, k) = min k.

Lemma min_max_same : forall k, min k = max k -> same k.
Proof.
 intros k H c. erewrite le_antisym;
   [reflexivity  | apply min_minimum | rewrite H; apply max_maximum].
Qed.

Lemma min_incr_aux : forall d k,
  num (min k, k) < d -> exists i, same (i+k) \/ min k < min (i+k).
Proof.
 induction d; intros.
  (* case: O *)
  inversion H.

  (* case: S d *)
  destruct (exists_dec _ (fun c => lt_dec (min k) (m(c,k)))).
   (* min k < m(c, k) のとき *)
   destruct (le_lt_eq_dec _ _ (l2 k)).
    (* min k < min (1+k) のとき *)
    exists 1; right; apply l.

    (* min k = min (1+k) のとき *)
    destruct (IHd (S k)) as [i HH].
     rewrite <- e0.
     eapply lt_le_trans; [apply (l5 _ e) | apply (lt_n_Sm_le _ _ H)].

     exists (S i). rewrite plus_Snm_nSm. rewrite e0.
     destruct HH; [left | right]; apply H0.

   (* min k >= m(c, k) のとき *)
   exists 0. left. simpl. unfold same. intros.
   destruct (le_lt_eq_dec _ _ (min_minimum k c)); auto.
   destruct (n c); apply l.
Qed.

Lemma min_incr : forall k,
  exists i, same (i+k) \/ min k < min (i+k).
Proof.
 intro k. apply (min_incr_aux (S (num(min k, k)))).
 apply lt_n_Sn.
Qed.

Lemma aux : forall d k,
  max k <= d + min k -> exists i, same (i+k).
Proof.
 induction d; intros.
  (* case O *)
  exists 0. simpl in H. apply (min_max_same _ (le_antisym _ _ (min_max _) H)).

  (* case S d *)
  destruct (min_incr k) as [j]. destruct H0.
   exists j. apply H0.

   destruct (IHd (j + k)) as [i Hi].
    apply lt_n_Sm_le.
    apply (le_lt_trans _ (S d + min k)).
     apply (le_trans _ (max k)); [apply max_i | apply H].

     simpl; apply lt_n_S. apply plus_lt_compat_l. apply H0.

   exists (i+j). rewrite <- plus_assoc. apply Hi.
Qed.

Theorem main :
  exists k, forall c1 c2, m(c1, k) = m(c2, k).
Proof.
 destruct (aux (max 0 - min 0) 0) as [k H].
  rewrite plus_comm.
  rewrite le_plus_minus_r; [apply le_refl | apply min_max].

  exists k. intros c1 c2. rewrite plus_0_r in H. rewrite (H c1). rewrite (H c2).
  reflexivity.
Qed.
