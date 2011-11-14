Require Import Arith.
Require Import Even.
Require Import Div2.
Require Import Omega.
Require Import Children.

Module Make(C : MChildren).

Definition child := C.child.
Parameter right : child -> child.

(* number of candies *)
Definition candy : Set := nat.

(* initial candies for children *)
Parameter m0 : child -> candy.
Axiom m0_even : forall c, even (m0 c).

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

Definition nat_max := MinMax.max.

Definition max_m k c x := nat_max (m(c,k)) x.

Lemma nat_max_ascomm : forall x y z,
  nat_max x (nat_max y z) = nat_max y (nat_max x z).
Proof.
   intros x y z. rewrite (Max.max_assoc y).
   rewrite (Max.max_comm _ x). rewrite <- (Max.max_assoc x).
   reflexivity.
Qed.

Definition max k :=
  C.fold (max_m k) C.children (m(C.c0,k)).

Lemma max_maximum : forall k c, m(c, k) <= max k.
Proof.
 cut(forall k c x0 cs,
   C.In c cs -> m(c, k) <= C.fold (max_m k) cs x0);
     [intros aux k c; apply aux; apply C.children_finite | ].
 intros k c x0.
 apply (C.ind (fun cs => C.In c cs ->
   m (c, k) <= C.fold (max_m k) cs x0));intros.
  rewrite C.fold_empty.
  destruct (C.empty_in c). apply H.

  rewrite C.fold_step; [| intros; apply nat_max_ascomm].
  simpl in H0. destruct (C.add_in _ _ _ H0).
    rewrite H1. apply Max.le_max_l.

    apply (le_trans _ _ _ (H H1)). apply Max.le_max_r.
Qed.

(* !! trying to define min *)
  
Definition nat_min := MinMax.min.

Definition min_m k c x := nat_min (m(c,k)) x.

Lemma nat_min_ascomm : forall x y z,
  nat_min x (nat_min y z) = nat_min y (nat_min x z).
Proof.
   intros x y z. rewrite (Min.min_assoc y).
   rewrite (Min.min_comm _ x). rewrite <- (Min.min_assoc x).
   reflexivity.
Qed.

Definition min k :=
  C.fold (min_m k) C.children (m(C.c0,k)).

Lemma min_minimum : forall k c, min k <= m(c, k).
Proof.
 cut(forall k c x0 cs,
   C.In c cs -> C.fold (min_m k) cs x0 <= m(c, k));
     [intros aux k c; apply aux; apply C.children_finite | ].
 intros k c x0.
 apply (C.ind (fun cs => C.In c cs ->
   C.fold (min_m k) cs x0 <= m (c, k)));intros.
  rewrite C.fold_empty.
  destruct (C.empty_in c). apply H.

  rewrite C.fold_step; [| intros; apply nat_min_ascomm].
  simpl in H0. destruct (C.add_in _ _ _ H0).
    rewrite H1. apply Min.le_min_l.

    refine (le_trans _ _ _ _ (H H1)).
    apply Min.le_min_r.
Qed.

Lemma max_exists : forall k, exists c, m(c, k) = max k.
Proof.
 intro k.
 cut (forall cs, exists c, m(c,k) = C.fold (max_m k) cs (m(C.c0,k))); [intro aux; apply aux|].
 (* aux *)
 apply C.ind.
  (* case: empty *)
  rewrite C.fold_empty. exists C.c0. reflexivity.

  (* case: step *)
  intros c cs IH. rewrite C.fold_step; [| intros; apply nat_max_ascomm].
  unfold max_m at 1. destruct (le_dec (m(c,k)) (C.fold (max_m k) cs (m (C.c0, k)))).
   unfold nat_max. destruct IH. exists x.
   rewrite Max.max_r; [apply H | apply l].

   unfold nat_max. exists c.
   rewrite Max.max_l; [reflexivity | ].
   apply lt_le_weak. apply not_le. apply n.
Qed.

Lemma min_exists : forall k, exists c, m(c, k) = min k.
Proof.
 intro k.
 cut (forall cs, exists c, m(c,k) = C.fold (min_m k) cs (m(C.c0,k))); [intro aux; apply aux|].
 (* aux *)
 apply C.ind.
  (* case: empty *)
  rewrite C.fold_empty. exists C.c0. reflexivity.

  (* case: step *)
  intros c cs IH. rewrite C.fold_step; [| intros; apply nat_min_ascomm].
  unfold min_m at 1. destruct (le_dec (C.fold (min_m k) cs (m (C.c0, k))) (m(c,k))). 
   unfold nat_min. destruct IH. exists x.
   rewrite Min.min_r; [apply H | apply l].

   unfold nat_min. exists c.
   rewrite Min.min_l; [reflexivity | ].
   apply lt_le_weak. apply not_le. apply n.
Qed.  

Lemma min_max : forall k, min k <= max k.
Proof.
 intro k. destruct (min_exists k). rewrite <- H. apply max_maximum.
Qed.

Definition num (x_k : candy * nat) : nat :=
  let (x, k) := x_k in
  C.size (C.filter (fun c => beq_nat(m(c,k)) x) C.children).

Lemma max_even : forall k, even (max k).
Proof.
  intro k.
  generalize (max_exists k).
  intro H.
  destruct H as [c H'].
  rewrite <- H'.
  apply m_even.
Qed.

Lemma double_is_double : forall n, 2 * n = double n.
    unfold double; intros; omega.
Qed.

Lemma m_c_S_k_is_LE_max_k :
  forall c k, m (c,(S k)) <= max k.
Proof.
  intros c k.
  simpl.
  (* tools *)
  case_eq (m_aux c k).
  intros x e HH.
  assert (x <= max k) as H_for_omega.
    assert (x = m (c,k)) as HH0.
      simpl.
      rewrite HH.
      simpl.
      reflexivity.
    rewrite HH0.
    apply max_maximum.
  clear HH.
  case_eq (m_aux (right c) k).
  intros x0 e0 HH.
  assert (x0 <= max k) as H_for_omega0.
    assert (x0 = m (right c,k)) as HH1.
      simpl.
      rewrite HH.
      simpl.
      reflexivity.
    rewrite HH1.
    apply max_maximum.
  clear HH.
  generalize (even_2n x e).
  generalize (even_2n x0 e0).
  intros HH HH0.
  destruct HH as [x1 e1].
  destruct HH0 as [x2 e2].
  (* even or odd *)
  destruct (even_odd_dec (div2 x + div2 x0)) as [ee|oo].
  (* even *)
  simpl.
  rewrite e1,e2 in *.
  rewrite <- (double_is_double x1), <- (double_is_double x2) in *.
  rewrite (div2_double x1),(div2_double x2).
  omega.
  (* odd *)
  simpl.
  rewrite e1,e2 in *.
  rewrite <- (double_is_double x1), <- (double_is_double x2) in *.
  rewrite (div2_double x1),(div2_double x2).
  assert (x2 + x1 <= max k /\ x2 + x1 <> max k -> S(x2 + x1) <= max k) as HHH1;
    [omega | apply HHH1; clear HHH1].
  split; [omega | ].
  intro HHH2.
  rewrite (div2_double x2), (div2_double x1) in oo.
  rewrite HHH2 in *.
  apply (not_even_and_odd (max k) (max_even k) oo).
Qed.

Lemma max_S_k_is_LE_m_c_k_for_some_c :
  forall k, exists c, max (S k) <= m (c,k).
Proof.
  intro k.
  destruct (max_exists k) as [x H].
  destruct (max_exists (S k)) as [x0 H0].
  exists x.
  rewrite <- H0.
  rewrite H.
  apply m_c_S_k_is_LE_max_k.
Qed.

(* 1 *)
Lemma l1 : forall k, max (S k) <= max k.
  intro k.
  destruct (max_S_k_is_LE_m_c_k_for_some_c k) as [x H].
  generalize (max_maximum k x).
  omega. 
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
  (* EVEN *)
  omega.
  
  (* ODD *)
  omega.
Qed.

(* 3 *)
Lemma l3_subgoal1 : forall c k,
  min k < m(c, k) -> min k <= m(right(c), k).
Proof.
 intros.
 apply min_minimum.
Qed.

Lemma min_even : forall k, even(min k).
Proof.
 intro k. destruct (min_exists k) as [c Hc].
 rewrite <- Hc. apply m_even.
Qed.
 
Lemma lt_div2_even : forall x y, even x -> even y -> x < y -> div2 x < div2 y.
Proof.
 intros x y Ex Ey H.
 cut (forall x y, double x < double y -> x < y);
     [intro HH; apply HH | unfold double; intros; omega].
 rewrite <- (even_double _ Ex). rewrite <- (even_double _ Ey). apply H.
Qed. 

Lemma l3 : forall c k,
  min k < m(c, k) -> min k < m(c, S k).
Proof.
 intros c k.
 simpl.
 case_eq (m_aux c k).
 intros.
 case_eq (m_aux (right c) k).
 intros.


  simpl.
  apply (le_lt_trans _ (div2 (min k) + div2 x0)).
   cut (min k = div2(min k) + div2(min k)); intros.
    rewrite H2 at 1.
    apply (plus_le_compat_l (div2 (min k)) (div2 x0) (div2 (min k))).
    assert(double (div2 (min k)) <= double (div2 x0)).
    rewrite<- (even_double (min k)).
    rewrite<- (even_double x0).
    generalize (min_minimum k).
    intros.
     assert (x0 = m (right c, k)).
     change (x0 = proj1_sig (m_aux (right c) k)).
     rewrite  H1.
     simpl.
     auto.
     rewrite H4.
     apply min_minimum.
    assumption.
    rewrite H2.
    fold (double (div2 (min k))).
    apply double_even.
    rewrite H2 at 1.
    auto.

    assert (x0 = m (right c, k)).
    change (x0 = proj1_sig (m_aux (right c) k)).
    rewrite H1.
    simpl.
    auto.
    rewrite H4.
    assert (forall x y, (even(x) /\ even(y) /\ (x<=y)) -> (div2(x) <= div2(y))).
    intros.
    destruct H5.
    destruct H6.
    apply even_2n in H5.
    apply even_2n in H6.
    destruct H5.
    destruct H6.
    rewrite e1, e2.
    assert(forall n, double n = 2 * n).
     intros.
     unfold double.
     omega.
    
     rewrite (H5 x2),(H5 x3).
     rewrite div2_double.
     rewrite div2_double.
       rewrite e1 in H7.
       rewrite e2 in H7.
       unfold double in H7.
       omega.

      apply H5.
      split.
      rewrite H2.
      fold (double (div2 (min k))).
      apply double_even.
      rewrite H2 at 1.
      fold (double (div2 (min k))).
      auto.
      split.
      apply m_even.
      apply min_minimum.

 (* min k = div2 (min k) + div2 (min k) *)
 destruct (min_exists k) as[c1 Hc].
 rewrite  (even_double (min k)) at 1; [reflexivity |].
 rewrite <- Hc. apply m_even.

 (* div2 (min k) + div2 x0 < m(c, S k) *)
 destruct (even_odd_dec (div2 x + div2 x0)); [| apply lt_S];
    apply plus_lt_compat_r;
    apply (lt_div2_even _ _ (min_even k) e); apply H0.
Qed.

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

Lemma m_lt_eq : forall k c,
  m(c, S k) = min k -> m(c, k) = min k.
Proof.
 intros.
 generalize (min_minimum k c); intros.
 destruct (le_lt_eq_dec _ _ H0); auto.
 apply l3 in l.
 rewrite <- H in l.
 apply lt_irrefl in l.
 contradiction.
Qed.
 
Lemma l5_aux : forall c k,
  m(c, k) = min k -> min k < m(c, S k) -> num(min k, S k) < num (min k, k).
Proof.
 intros.
 unfold num.
 apply C.filter_length_lt.
  exists c. split; [apply C.children_finite|]. split.
   intro. destruct (beq_nat_true_iff (m(c,S k)) (min k)) as[HH _].
   destruct (lt_irrefl (min k)). rewrite <- (HH H1) at 2. apply H0.

   apply beq_nat_true_iff. apply H.

  apply C.filter2_subset. intros c0 H1.
  apply beq_nat_true_iff. apply m_lt_eq. apply beq_nat_true_iff.
  apply H1.
Qed.
 
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
  destruct (C.exists_dec _ (fun c => lt_dec (min k) (m(c,k)))).
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

End Make.
