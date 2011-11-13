Lemma monotone_double_double_r : forall m n, double m <= double n -> m <= n .
  unfold double.
  intros.
  induction m; induction n; intros; simpl; try omega; try eauto.
Qed.

Lemma monotone_Sdouble_double_r : forall m n, S (double m) <= double n -> m <= n .
  unfold double.
  intros.
  induction m; induction n; intros; simpl; try omega; try eauto.
Qed.

Lemma monotone_double_Sdouble_r : forall m n, double m <= S (double n) -> m <= n .
  unfold double.
  intros.
  induction m; induction n; intros; simpl; try omega; try eauto.
Qed.

Lemma monotone_Sdouble_Sdouble_r : forall m n, S (double m) <= S (double n) -> m <= n .
  unfold double.
  intros.
  induction m; induction n; intros; simpl; try omega; try eauto.
Qed.

Lemma monotone_div2 : forall m n, m <= n -> div2 m <= div2 n.
Proof.
  intros.
  generalize (even_odd_dec m).
  generalize (even_odd_dec n).
  intros.
  destruct H0.
  generalize (even_double n e); intro.
  destruct H1.
  generalize (even_double m e0); intro.
  rewrite H0,H1 in H.
  apply monotone_double_double_r.
  apply H.

  generalize (odd_double m o); intro.
  rewrite H0,H1 in H.
  apply monotone_Sdouble_double_r.
  apply H.

  generalize (odd_double n o); intro.
  destruct H1.
  generalize (even_double m e); intro.
  rewrite H0,H1 in H.
  apply monotone_double_Sdouble_r.
  apply H.

  generalize (odd_double m o0); intro.
  rewrite H0,H1 in H.
  apply monotone_Sdouble_Sdouble_r.
  apply H.
Qed.  
