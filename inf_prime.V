(* Preliminaries *)

(* Ltac custom tactics *)

Ltac fassume := exfalso; assumption.

Ltac unfoldfold e := unfold e; fold e.

Ltac unfoldfoldin e h := unfold e in h; fold e in h.

(* Nat Def & Succ & Pred *)



Lemma succ_inj : forall (x y : nat), x = y -> S x = S y.
  intros x y H. rewrite H. reflexivity.
  Defined.

Fixpoint pred (n : nat) :=
  match n with
  | O => O
  | S n' => n'
  end.

Lemma succ_inj2 : forall (x y : nat), S x = S y -> x = y.
  intros n m H. assert (H2 : n = pred (S n)). reflexivity.
  rewrite H2. rewrite H. reflexivity.
  Defined.

Lemma succ_ex : forall (x : nat), x = S x -> False.
  induction x; intros H. discriminate H. apply (succ_inj2 x (S x)) in H.
  apply IHx. assumption.
  Defined.

Lemma succ_ex2 : forall (n : nat), S n = n -> False.
  intros n H. apply (succ_ex n). rewrite H. reflexivity.
  Defined.

(* Option *)

Inductive option (A:Type) : Type :=
  | Some : A -> option A
  | None : option A.

Arguments Some {A} a.
Arguments None {A}.

Definition predO (no : option nat) :=
  match no with
  | Some n => n
  | None => O
  end.

Lemma predSome : forall (n : nat), predO (Some n) = n.
  reflexivity.
  Defined.

Lemma some_eq : forall (x y : nat), Some x = Some y -> x = y.
  intros x y H.
  rewrite <- (predSome x). rewrite <- (predSome y). rewrite H. reflexivity.
  Defined.

Lemma some_eq2 : forall (x y : nat), x = y -> Some x = Some y.
  intros x y H. rewrite H. reflexivity.
  Defined. 

(* Plus *)

Fixpoint plus (n m : nat) :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Lemma plus_Sx_y : forall (x y : nat), plus (S x) y = S (plus x y).
  reflexivity.
  Defined.

Lemma plus_O_y : forall (y : nat), plus O y = y.
  reflexivity.
  Defined.

Lemma plus_x_Sy : forall (x y : nat), plus x (S y) = S (plus x y).
  induction x; intro y; try reflexivity. rewrite ?plus_Sx_y. rewrite IHx. reflexivity.
  Defined.

Lemma plus_x_O : forall (x : nat), plus x O = x.
  induction x. reflexivity. rewrite plus_Sx_y. rewrite IHx. reflexivity.
  Defined.

Theorem plus_comm : forall (x y : nat), plus x y = plus y x.
  induction x; intros y; try reflexivity. rewrite plus_O_y. rewrite plus_x_O. reflexivity.
  rewrite plus_Sx_y. rewrite plus_x_Sy. rewrite IHx. reflexivity.
  Defined.

Theorem plus_assoc : forall (x y z : nat), plus x (plus y z) = plus (plus x y) z.
  induction x. intros y z. rewrite plus_O_y. rewrite plus_O_y. reflexivity.
  intros y z. rewrite plus_Sx_y. rewrite plus_Sx_y. rewrite plus_Sx_y.
  rewrite IHx. reflexivity.
  Defined.

Lemma plus_22o1 : forall (a b c d : nat), plus (plus a b) (plus c d) = plus (plus a c) (plus b d).
  intros a b c d. rewrite <- (plus_assoc a b (plus c d)). rewrite <- (plus_assoc a c (plus b d)).
  rewrite (plus_assoc b c d). rewrite (plus_assoc c b d). rewrite (plus_comm b c). reflexivity.
  Defined.

Lemma plus_extract1 : forall (z x y  : nat), plus x z = plus y z -> x = y.
  induction z; intros x y H. rewrite ?plus_x_O in H. assumption. rewrite ?plus_x_Sy in H. apply (succ_inj2 (plus x z) (plus y z)) in H.
  apply IHz. assumption.
  Defined.

Lemma plus_extract2 : forall (z x y : nat), plus z x = plus z y -> x = y.
  intros z x y H. rewrite (plus_comm z x) in H. rewrite (plus_comm z y) in H.
  apply plus_extract1 in H. assumption.
  Defined.

Lemma plus_xyz_xzy : forall (x y z : nat), plus (plus x y) z = plus (plus x z) y.
  intros x y z. rewrite <- plus_assoc. rewrite (plus_comm y z). rewrite <- plus_assoc.
  reflexivity.
  Defined.

(* Times *)

Fixpoint times (n m : nat) :=
  match n with
  | O => O
  | S n' => plus (times n' m) m
  end.

Lemma times_Sx_y : forall (x y : nat), times (S x) y = plus (times x y) y.
  reflexivity.
  Defined.

Lemma times_SO_y : forall (y : nat), times (S O) y = y.
  reflexivity.
  Defined.

Lemma times_x_O : forall (x : nat), times x O = O.
  induction x; try reflexivity. rewrite times_Sx_y. rewrite plus_x_O. assumption.
  Defined.

Lemma times_O_y : forall (x : nat), times O x = O.
 induction x; try reflexivity. Defined.

Lemma times_x_SO : forall (x : nat), times x (S O) = x.
  induction x. reflexivity.
  rewrite times_Sx_y. rewrite plus_x_Sy. apply succ_inj.
  rewrite IHx. rewrite plus_x_O. reflexivity.
  Defined.

Lemma times_x_Sy : forall (x y : nat), times x (S y) = plus (times x y) x.
  induction x. reflexivity.
  intros y. rewrite ?times_Sx_y. rewrite IHx.
  rewrite ?plus_x_Sy. rewrite plus_xyz_xzy. reflexivity.
  Defined.

Lemma times_comm : forall (x y : nat), times x y = times y x.
  induction x; intros y. rewrite times_O_y. rewrite times_x_O. reflexivity.
  rewrite times_Sx_y. rewrite times_x_Sy. rewrite IHx. reflexivity.
  Defined.

Lemma times_dist1 : forall (x y z : nat), times x (plus y z) = plus (times x y) (times x z).
  induction x; intros y z. rewrite ?times_O_y. rewrite plus_O_y. reflexivity.
  rewrite times_Sx_y. rewrite IHx. rewrite ?times_Sx_y. rewrite plus_22o1. reflexivity.
  Defined.

Lemma times_dist2 : forall (x y z : nat), times (plus x y) z = plus (times x z) (times y z).
  intros x y z. rewrite times_comm. rewrite times_dist1. rewrite (times_comm z x). rewrite (times_comm z y).
  reflexivity.
  Defined.

Lemma times_assoc : forall (x y z : nat), times (times x y) z = times x (times y z).
  induction x; intros y z. rewrite ?times_O_y. reflexivity.
  rewrite ?times_Sx_y. rewrite times_dist2. rewrite IHx. reflexivity.
  Defined.

Lemma times_SS_neq_SO : forall (x y : nat), not (times x (S (S y)) = S O).
  unfold not. induction x; intros y H. rewrite times_O_y in H. discriminate H.
  rewrite times_Sx_y in H. rewrite ?plus_x_Sy in H. discriminate.
  Defined.

Lemma times_xyO_or : forall (x y : nat), times x y = O -> x = O \/ y = O. 
  intros x y H. destruct x. left. reflexivity. destruct y. right. reflexivity. rewrite times_Sx_y in H.
  rewrite plus_x_Sy in H. discriminate.
  Qed.

(* Eq / Eqb *)

Fixpoint eqb n m : bool :=
  match n, m with
    | O, O => true
    | O, S _ => false
    | S _, O => false
    | S n', S m' => eqb n' m'
  end.

Lemma eqb_Sn_Sm : forall (n m : nat), eqb (S n) (S m) = eqb n m.
  intros n m. unfold eqb; fold eqb. reflexivity.
  Defined.

Lemma eqb_comm : forall (n m : nat), eqb n m = eqb m n.
  induction n; destruct m; try reflexivity. rewrite ?eqb_Sn_Sm. rewrite IHn. reflexivity.
  Defined.

Lemma eqb_equal : forall (n m : nat), eqb n m = true -> n = m.
  induction n. destruct m. reflexivity.
  intros H. discriminate.
  intros m H. destruct m. discriminate.
  unfoldfoldin eqb H. apply IHn in H. apply succ_inj. assumption.
  Defined.

Lemma eqb_not_equal : forall (n m : nat), eqb n m = false -> n <> m.
  induction n. intros m H0 H1.
  rewrite <- H1 in H0. discriminate.
  destruct m. intros H0 H1. discriminate.
  intros H0 H1. unfoldfoldin eqb H0. apply IHn in H0. unfold not in H0. apply H0. apply succ_inj2. assumption.
  Defined.

Lemma eq_or_not : forall (n m : nat), n = m \/ not (n = m).
  intros n m. destruct (eqb n m) eqn: eqpat. apply eqb_equal in eqpat. left. assumption.
                                             apply eqb_not_equal in eqpat. right. assumption.
  Defined.

Lemma eqb_n_n : forall (n : nat), eqb n n = true.
  induction n. reflexivity. unfoldfold eqb. assumption.
  Defined.

Lemma eqb_equal2 : forall (n m : nat), n = m -> eqb n m = true.
  intros n m H. rewrite H. 
  rewrite eqb_n_n. reflexivity.
  Defined.

Lemma neq_S : forall (n m : nat), n <> m -> (S n) <> (S m).
  intros n m H. unfold not. unfold not in H. intros H1. apply H.
  apply succ_inj2. assumption.
  Defined.

Lemma neq_pred : forall (n m : nat), (S n) <> (S m) -> n <> m.
  intros n m H. unfold not. unfold not in H. intros H1. apply H.
  apply succ_inj. assumption.
  Defined.

Lemma neq_impl_eqb_false : forall (n m : nat), n <> m -> eqb n m = false.
  intros n m H. destruct (eqb n m) eqn: eqbpat. apply eqb_equal in eqbpat. absurd (n = m); assumption.
  reflexivity.
  Defined.

Lemma eq_neq_false : forall (n m : nat), n <> m -> n = m -> False.
  intros n m H. unfold not; intros H1. unfold not in H. apply H. assumption.
  Defined.

(* Tuples *)

Lemma tup_eq : forall (n m o p : nat), (n,m) = (o,p) -> n = o /\ m = p.
  intros n m o p H. inversion H.
  split; reflexivity.
  Defined.

Lemma neq_tup1 : forall (n m o p : nat), n <> o -> (n,m) <> (o,p).
  intros n m o p H1 H2.
  unfold not in H1. apply tup_eq in H2. destruct H2. apply H1. apply H.
  Defined.

Lemma neq_tup2 : forall (n m o p : nat), m <> p -> (n,m) <> (o,p).
  intros n m o p H1 H2.
  unfold not in H1. apply H1. apply tup_eq in H2. destruct H2. apply H0. Defined.

(* Le / Lt / Leb *)

Fixpoint leb n m : bool :=
  match n, m with
    | O, _ => true
    | _, O => false
    | S n', S m' => leb n' m'
  end.

Fixpoint le n m : Prop :=
  match n, m with
  | O,_ => True
  | _,O => False
  | S n', S m' => le n' m'
  end.

Definition ltb n m := leb (S n) m.

Definition lt n m := le (S n) m.

Lemma le_Sx_O : forall (x : nat), le (S x) O -> False.
  intros x H. unfold le in H. assumption.
  Defined.

Lemma le_O_y : forall (y : nat), le O y.
  intros y; reflexivity.
  Defined.

Lemma le_Sx_Sy : forall (x y : nat), le (S x) (S y) -> le x y.
  intros x y H.
  unfoldfoldin le H. assumption.
  Defined.

Lemma le_Sx_Sy2 : forall (x y : nat), le x y -> le (S x) (S y).
  intros x y H. unfoldfoldin le H. assumption.
  Defined.

Lemma le_succ1 : forall (x y : nat), le (S x) y -> le x y.
  induction x. intros y H. reflexivity.
  intros y. intros H. destruct y. apply le_Sx_O in H. fassume.
  apply le_Sx_Sy in H. apply IHx in H. apply le_Sx_Sy2. assumption.
  Defined.

Lemma lt_succ1 : forall (x y : nat), lt (S x) y -> lt x y.
  intros x y H. unfold lt in H. unfold lt. apply le_succ1. assumption.
  Defined.

Lemma le_succ2 : forall (x y : nat), le x y -> le x (S y).
  induction x. intros y H. apply le_O_y.
  intros y H. destruct y. apply le_Sx_O in H. fassume. apply IHx in H. apply le_Sx_Sy2. assumption.
  Defined.

Lemma le_x_x : forall (x : nat), le x x.
  induction x. reflexivity. apply le_Sx_Sy2. assumption.
  Defined.

Lemma trichotomy : forall (x y : nat), lt x y \/ lt y x \/ x = y.
  induction x.
  destruct y; 
  [right; right; reflexivity | 
   left; unfold lt; apply le_Sx_Sy2; apply le_O_y].
  destruct y. right; left; unfold lt; apply le_Sx_Sy2; apply le_O_y.
  destruct (IHx y). left; apply le_Sx_Sy2; assumption.
  destruct H; 
  right. left; apply le_Sx_Sy2; assumption.
         right; rewrite H; reflexivity.
  Defined.

Lemma dichotomy : forall (x y : nat), le x y \/ le y x.
  induction x; destruct y. right; reflexivity.
  left. apply le_O_y. right. apply le_O_y.
  destruct (IHx y). left. apply le_Sx_Sy2. assumption.
  right. apply le_Sx_Sy2. assumption.
  Defined.

Lemma dichotomy_le_lt : forall (x y : nat), le x y \/ lt y x.
  induction x; destruct y. left. reflexivity. left. apply le_O_y. right. unfold lt. apply le_Sx_Sy2. apply le_O_y.
  destruct (IHx y). left. apply le_Sx_Sy2. assumption. right. unfold lt in H. unfold lt. apply le_Sx_Sy2. assumption.
  Defined.

Lemma le_lt_anticomm : forall (x y : nat), le x y -> lt y x -> False.
  induction x; destruct y; intros H0 H1. unfold lt in H1. simpl in H1. assumption.
  unfold lt in H1. simpl in H1. assumption. simpl in H0. assumption. apply (IHx y). apply le_Sx_Sy. apply H0.
  unfold lt. unfold lt in H1. apply le_Sx_Sy in H1. apply H1.
  Defined.

Lemma le_impplus : forall (x y z :  nat), le (plus z x) y -> le x y.
  intros x y z. generalize dependent x. generalize dependent y. induction z; intros y x.
  rewrite plus_O_y. intros H. assumption.
  intros H. rewrite plus_Sx_y in H. apply le_succ1 in H.
  apply IHz in H. assumption.
  Defined.

Lemma le_impplus2 : forall (x y z : nat), le (plus x z) y -> le x y.
  intros x y z H. rewrite plus_comm in H. apply (le_impplus) in H.
  assumption.
  Defined.

Lemma le_lt_conv : forall (x y : nat), le (S x) y -> lt x y.
  intros x y H. unfold lt. assumption.
  Defined.

Lemma le_trans : forall (x y z : nat), le x y -> le y z -> le x z.
  induction x. intros y z H1 H2. reflexivity.
  intros y z H1 H2. destruct y. simpl in H1. fassume.
  destruct z. simpl in H2. fassume.
  apply le_Sx_Sy2. apply le_Sx_Sy in H1. apply le_Sx_Sy in H2. 
  apply (IHx y z). assumption. assumption.
  Defined.

Lemma le_Sx_x : forall (x : nat), le (S x) x -> False.
  induction x. intros H.
  simpl in H. assumption.
  intros H. apply le_Sx_Sy in H.
  apply IHx. apply H.
  Defined.

Lemma le_plus_reduce1 : forall (x y z : nat), le y z -> le (plus x y) (plus x z).
  induction x; intros y z H. rewrite ?plus_O_y. assumption.
  rewrite ?plus_Sx_y. apply le_Sx_Sy2.
  apply IHx. assumption.
  Defined.

Lemma le_sumex : forall (q r s : nat), le q r -> le q (plus r s).
  intros q r s.
  generalize dependent q. generalize dependent r. induction s.
  intros q r. intros H1. rewrite plus_x_O. assumption.
  intros r q. intros H1. apply IHs in H1. rewrite plus_x_Sy. apply le_succ2. assumption.
  Defined.

Lemma le_sumex2 : forall (q r s : nat), le (plus q r) s -> le q s.
  intros q r s. revert q s. induction r. intros q s. rewrite plus_x_O. intros H. assumption.
  intros q s H. rewrite plus_x_Sy in H. apply le_succ1 in H. apply IHr in H. assumption.
  Defined.

Lemma le_plustrans1 : forall (q r s u : nat), le q r -> le (plus r s) u -> le (plus q s) u.
  intros q r s u H1 H2. rewrite (plus_comm r s) in H2. rewrite plus_comm.
  assert (le (plus s q) (plus s r)).
  apply le_plus_reduce1. assumption. apply (le_trans (plus s q) (plus s r) u).
  assumption. assumption.
  Defined.

Lemma le_plustrans2 : forall (q r s u : nat), le q r -> le u (plus q s) -> le u (plus r s).
  intros q r s u H1 H2. rewrite plus_comm in H2. rewrite plus_comm.
  assert (le (plus s q) (plus s r)). apply le_plus_reduce1.
  assumption. apply (le_trans u (plus s q) (plus s r)). assumption.
  assumption.
  Defined. 

Lemma sum_le : forall (q r x y : nat), le q r -> le x y -> le (plus q x) (plus r y).
  intros q r x y H1 H2.
  apply (le_plustrans1 q r x (plus r y)).
  assumption.
  rewrite (plus_comm r x). rewrite (plus_comm r y).
  apply (le_plustrans2 x y r (plus x r)). assumption. apply le_x_x.
  Defined.

Lemma le_pluscancel : forall (q x y : nat), le (plus x q) (plus y q) -> le x y.
  induction q; intros x y H.
  rewrite ?plus_x_O in H. assumption.
  rewrite ?plus_x_Sy in H. apply le_Sx_Sy in H. apply IHq. assumption.
  Defined.

Lemma lt_pluscancel : forall (q x y : nat), lt (plus x q) (plus y q) -> lt x y.
  intros q x y H. unfold lt in H. rewrite <- plus_Sx_y in H.
  apply le_pluscancel in H. unfold lt. assumption.
  Defined.

Lemma lt_plusdisc : forall (x y : nat), lt (plus x y) x -> False.
  intros x y. generalize dependent x. induction y.
  intros x H. rewrite plus_x_O in H. unfold lt in H. apply le_Sx_x in H. assumption.
  intros x H. apply (IHy x). rewrite plus_x_Sy in H.
  apply lt_succ1 in H. assumption.
  Defined.

Lemma le_pluscancel2 : forall (q x y : nat), le x y -> le (plus x q) (plus y q).
  induction q; intros x y H.
  rewrite ?plus_x_O. assumption.
  rewrite ?plus_x_Sy. apply le_Sx_Sy2.
  apply IHq. assumption.
  Defined.

Lemma lt_pluscancel2 : forall (q x y : nat), lt x y -> lt (plus x q) (plus y q).
  intros q x y H. unfold lt in H. apply (le_pluscancel2 q (S x) y ) in H.
  rewrite plus_Sx_y in H. unfold lt. assumption.
  Defined.

Lemma le_prod_Sreduct : forall (q x y : nat), le (times (S q) (S x)) (times (S q) (S y)) -> le (times (S q) x) (times (S q) y).
  intros q x y H. rewrite (times_x_Sy (S q) x) in H. rewrite (times_x_Sy (S q) y) in H.
  apply le_pluscancel in H. assumption.
  Defined.

Lemma prod_le : forall (x y q : nat), le (times (S q) x) (times (S q) y) -> le x y.
  induction x; intros y q H. apply le_O_y. destruct y.
  rewrite times_x_O in H. rewrite times_Sx_y in H. rewrite plus_x_Sy in H. apply le_Sx_O in H. fassume.
  apply le_Sx_Sy2. apply (IHx y q). apply le_prod_Sreduct in H. assumption.
  Defined.

Lemma prod_le2 : forall (q x y : nat), le x y -> le (times (S q) x) (times (S q) y).
  intros q x. revert q. induction x; intros q y H. rewrite times_x_O. reflexivity.
  destruct y. simpl in H. fassume.
  rewrite times_x_Sy. rewrite times_x_Sy. apply (le_pluscancel2 (S q) (times (S q) x) (times (S q) y)).
  apply IHx. apply le_Sx_Sy. assumption.
  Defined.

Lemma le_x_O : forall (x : nat), le x O -> x = O.
  destruct x. reflexivity. simpl. intros H. fassume.
  Defined.

Lemma le_x_Sx : forall (x : nat), le x (S x).
  induction x. reflexivity. apply le_Sx_Sy2. assumption.
  Defined.

Lemma neq_lt : forall (x y : nat), x <> y -> lt x y \/ lt y x.
  intros x y H. unfold not in H. remember (trichotomy x y).
  destruct o. left; assumption.
  destruct o. right; assumption. exfalso. apply H. assumption.
  Defined.

Lemma le_neq : forall (x y : nat), le x (S y) -> x <> (S y) -> le x y.
  intros x y H1 H2. remember (trichotomy x (S y)).
  destruct o. unfold lt in l; apply le_Sx_Sy2; assumption.
  destruct o. exfalso. apply (le_lt_anticomm x (S y)); assumption; assumption. absurd (x = S y); assumption; assumption.
  Defined.

Lemma le_x_Syx : forall (x y : nat), le x (times (S y) x).
  intros x y. rewrite times_Sx_y. rewrite plus_comm. apply le_sumex. apply le_x_x.
  Defined.

Lemma le_SSx_SSySx : forall (x y : nat), le (S (S x)) (times (S (S y)) (S x)).
  intros x y. rewrite times_Sx_y. rewrite times_Sx_y. rewrite <- plus_assoc. rewrite plus_Sx_y. rewrite <- plus_x_Sy.
  rewrite plus_assoc. rewrite (plus_comm (plus (times y (S x)) x) (S (S x))).
  apply le_sumex. apply le_x_x.
  Defined.

Lemma le_imp_leb : forall (x y : nat), le x y -> leb x y = true.
  induction x; destruct y; try reflexivity. 
  intros H. apply le_Sx_O in H. fassume.
  intros H. unfold leb; fold leb. apply IHx. apply le_Sx_Sy. assumption.
  Defined.

Lemma leb_imp_le : forall (x y : nat), leb x y = true -> le x y.
  induction x; destruct y; intros H; try reflexivity. simpl leb in H.
  discriminate. simpl in H. apply IHx in H. apply le_Sx_Sy2. assumption.
  Defined.

Lemma leb_false_lt : forall (x y : nat), leb x y = false -> lt y x.
  induction x; destruct y; intros H; try reflexivity.
  unfold lt. simpl in H. discriminate H. simpl in H. discriminate H.
  simpl in H. apply IHx in H. unfold lt in H. unfold lt. apply le_Sx_Sy2. assumption.
  Defined.

Lemma le_not_leb_false : forall (x y : nat), (le x y -> False) -> leb x y = false.
  intros x y H. remember (leb x y). destruct b. exfalso. apply H. assert (leb x y = true).  rewrite Heqb. reflexivity.
  apply leb_imp_le. assumption. reflexivity.
  Defined.

Lemma ltb_antisym : forall (x y : nat), ltb x y = true -> ltb y x = false.
  intros x y H.  apply leb_imp_le in H. assert (le (S x) y -> lt x y). intros H1. unfold lt. assumption. apply H0 in H. apply le_not_leb_false. intros H1.
  apply le_succ1 in H1. apply (le_lt_anticomm y x). assumption. assumption.
  Defined.

Lemma le_x_Sy_reduct : forall (x y : nat), le x (S y) -> x = (S y) \/ le x y.
  intros x y. generalize dependent x. induction y; intros x H. destruct x. right. apply le_x_x.
  destruct x. left. reflexivity. apply le_Sx_Sy in H. apply le_Sx_O in H. fassume.
  destruct x. right. apply le_O_y. apply le_Sx_Sy in H. apply IHy in H. destruct H. left. apply succ_inj. assumption.
  right. apply le_Sx_Sy2. assumption.
  Defined.

Lemma le_x_Sy_reduct2 : forall (x y : nat), x = (S y) \/ le x y -> le x (S y).
  induction x. intros y H. destruct H. discriminate. apply le_O_y. intros y H.
  destruct H. rewrite H. apply le_x_x. apply le_succ2. assumption.
  Defined.

Lemma le_SO_y_le_prod : forall (x y : nat), le (S O) y -> le x (times x y).
  intros x. generalize dependent x. induction y. intros H. apply le_Sx_O in H. fassume.
  intros H. rewrite times_x_Sy. 
  rewrite plus_comm. apply le_sumex. apply le_x_x.
  Defined.

(* Sub *)

Fixpoint sub n m :=
  match n, m with
  | S k, S l => sub k l
  | _, _ => n
  end.

Lemma sub_n_n : forall (n : nat), sub n n = O.
  induction n. reflexivity. simpl. assumption.
  Defined.

Lemma sub_O : forall (x : nat), sub x O = x.
  intros x. destruct x; reflexivity.
  Defined.

Lemma sub_O_y : forall (y : nat), sub O y = O.
  reflexivity.
  Defined.

Lemma sub_Sx_Sy : forall (x y : nat), sub (S x) (S y) = sub x y.
  intros x y. reflexivity.
  Defined.

Lemma le_sub : forall (x y : nat), le x y -> plus x (sub y x) = y.
  induction x; destruct y; intros H; try reflexivity.
  apply le_Sx_O in H. fassume.
  simpl. simpl in H. rewrite (succ_inj (plus x (sub y x)) y). reflexivity. apply IHx. assumption.
  Defined.

Lemma le_sub2 : forall (x y : nat), le x y -> sub x y = O.
  induction x; destruct y; intros H; try reflexivity. simpl in H. fassume.
  apply le_Sx_Sy in H. rewrite sub_Sx_Sy. apply IHx. assumption.
  Defined.

Lemma lt_sub2 : forall (x y : nat), lt x y -> sub x y = O.
  intros x y. unfold lt. intros H. apply le_succ1 in H. apply le_sub2. assumption.
  Defined.

Lemma le_plus : forall (x y : nat), le x y -> exists (z : nat), plus x z = y.
  intros x y H. exists (sub y x). apply le_sub. assumption.
  Defined.

Lemma sub_Sx_y : forall (x y : nat), le y x -> sub (S x) y = S (sub x y).
  induction x; intros y H. destruct y; [reflexivity | apply le_Sx_O in H; fassume ].
  destruct y. rewrite ?sub_O; reflexivity. 
              rewrite ?sub_Sx_Sy; rewrite (IHx y). reflexivity. apply le_Sx_Sy. assumption.
  Defined.

Lemma sub_x_Sy : forall (x y : nat), le (S y) x -> S (sub x (S y)) = sub x y.
  induction x; intros y H. apply le_Sx_O in H; fassume.
  rewrite sub_Sx_Sy. rewrite sub_Sx_y. reflexivity.
  apply le_Sx_Sy. assumption.
  Defined. 

Lemma plus2_sub : forall (x y z : nat), le z y -> sub (plus x y) z = plus x (sub y z).
  induction x. intros y z H. rewrite ?plus_O_y; reflexivity.
  intros y z H. 
  assert (sub (plus x y) z = plus x (sub y z)). apply IHx in H. assumption.
  rewrite plus_Sx_y. assert (le z (plus x y)). rewrite plus_comm. apply le_sumex. assumption.
  rewrite sub_Sx_y. rewrite H0. rewrite plus_Sx_y. reflexivity. assumption.
  Defined.

Lemma plus_sub : forall (x y z : nat), le y x -> plus (sub x y) z = sub (plus x z) y.
  induction x; intros y z H. destruct y. rewrite ?sub_O. reflexivity.
  apply le_Sx_O in H. fassume.
  destruct y. rewrite ?sub_O. reflexivity.
  rewrite plus_Sx_y. rewrite ?sub_Sx_Sy.
  apply IHx. apply le_Sx_Sy. assumption.
  Defined.

Lemma sub_plus2 : forall (x y z : nat), le (plus y z) x -> sub x (plus y z) = sub (sub x y) z.
  induction x; destruct y; destruct z; try reflexivity; intros H.
  rewrite plus_x_O in H. rewrite plus_x_O. rewrite sub_O. reflexivity.
  rewrite plus_Sx_y. rewrite plus_x_Sy. rewrite sub_Sx_Sy. rewrite sub_Sx_Sy. rewrite <- plus_x_Sy.
  apply (IHx y (S z)). rewrite plus_Sx_y in H. apply le_Sx_Sy in H. assumption.
  Defined.

Lemma sub_sub_x_yz : forall (x y z : nat), le (plus y z) x -> sub (sub x y) z = sub (sub x z) y.
  induction x; destruct y; destruct z; intros H; try reflexivity.
  rewrite ?sub_O. reflexivity. rewrite ?sub_O. reflexivity.
  rewrite plus_Sx_y in H. apply le_Sx_Sy in H.
  rewrite sub_Sx_Sy. rewrite sub_Sx_y.
  all: cycle 1. rewrite plus_comm in H. apply (le_sumex2 (S z) y x) in H. assumption.
  rewrite sub_Sx_Sy. rewrite (IHx y (S z)). reflexivity. assumption.
  Defined.

Lemma plus_dist_sub : forall (x y z w : nat), le z x -> le w y -> sub (plus x y) (plus z w) = plus (sub x z) (sub y w).
  intros x y z w H1 H2.
  rewrite (plus_sub x z (sub y w)). rewrite <- (plus2_sub x y w). rewrite <- (sub_plus2 (plus x y) w z). rewrite (plus_comm z w). reflexivity.
  rewrite (plus_comm w z); apply sum_le. assumption. assumption. assumption. assumption.
  Defined.
 
Lemma prod_dist_sub_le1 : forall (x y z : nat), le y x -> sub (times x z) (times y z) = times (sub x y) z.
  intros x y z. revert x y. induction z. intros x y H. rewrite !times_x_O. reflexivity.
  intros x y H. rewrite ?times_x_Sy. rewrite plus_dist_sub. rewrite IHz. reflexivity.
  assumption.
  all: cycle 1. assumption.
  destruct z. rewrite !times_x_O. reflexivity. rewrite (times_comm y (S z)). rewrite (times_comm x (S z)). 
  apply (prod_le2 z y x). assumption.
  Defined.

Lemma prod_dist_sub_le2 : forall (x y z : nat), le x y -> sub (times x z) (times y z) = times (sub x y) z.
  intros x y z H. assert (sub x y = O). apply le_sub2. assumption. rewrite H0. rewrite times_O_y.
  assert (le (times x z) (times y z)).
  rewrite (times_comm x z). rewrite (times_comm y z).
  destruct z. rewrite !times_O_y. reflexivity.
  apply (prod_le2 z x y). assumption.
  assert (sub (times x z) (times y z) = O).
  apply le_sub2. assumption. assumption.
  Defined.

Lemma prod_dist_sub : forall (x y z : nat), sub (times x z) (times y z) = times (sub x y) z.
  intros x y z. assert (le x y \/ le y x). apply dichotomy.
  destruct H. apply prod_dist_sub_le2. assumption.
  apply prod_dist_sub_le1. assumption.
  Defined.

Lemma le_suby_y : forall (y x : nat), le (sub y x) y.
  induction y; destruct x; try reflexivity. rewrite sub_O. apply le_x_x.
  simpl. apply le_succ2. apply IHy.
  Defined.

Lemma le_Sx_subx_false : forall (x y : nat), le (S x) (sub x y) -> False.
  intros x y H. generalize dependent x. induction y; intros x H. rewrite sub_O in H.
  apply le_Sx_x in H. assumption.
  destruct x. rewrite sub_O_y in H. apply le_Sx_x in H. assumption.
  rewrite sub_Sx_Sy in H. apply le_succ1 in H. apply (IHy x) in H.
  assumption.
  Defined.

Lemma sub_O_imp_eq : forall (x y : nat), le y x -> sub x y = O -> x = y.
  induction x. intros y H1 H2.
  destruct y. reflexivity. apply le_Sx_O in H1. fassume.
  intros y H1 H2. destruct y. simpl in H2. discriminate H2. simpl. apply le_Sx_Sy in H1. apply succ_inj.  apply IHx.
  assumption. rewrite sub_Sx_Sy in H2. assumption.
  Defined.

Lemma sub_plus_xy_y : forall (x y : nat), sub (plus x y) y = x.
  intros x y. rewrite plus2_sub. rewrite sub_n_n. rewrite plus_x_O. reflexivity. apply le_x_x.
  Defined.

Lemma plus_elim_sub : forall (x y z : nat), plus x y = z -> x = sub z y.
  intros x y z H. rewrite <- H. rewrite sub_plus_xy_y. reflexivity.
  Defined.

Lemma sub_Sx_x : forall (x : nat), sub (S x) x = S O.
  induction x. reflexivity.
  rewrite sub_Sx_Sy. assumption.
  Defined.

(* Divmod *)

Fixpoint divmod x y q u :=
  match x with
    | O => (q,u)
    | S x' => match u with
                | O => divmod x' y (S q) y
                | S u' => divmod x' y q u'
              end
  end.

Lemma divmod_t0 : forall (y q u : nat), divmod O y q u = (q,u).
  reflexivity.
  Defined.

Lemma divmod_t1 : forall (x y q : nat), divmod (S x) y q O = divmod x y (S q) y.
  reflexivity.
  Defined.

Lemma divmod_t2 : forall (x y q u : nat), divmod (S x) y q (S u) = divmod x y q u.
  reflexivity.
  Defined.

Definition dminc (q r mp : nat) :=
  match r with
  | O => (S q, mp)
  | S r' => (q, r')
  end.

Definition dmdec (q r mp : nat) :=
  if eqb r mp
  then 
    match q with
    | O => (O,O)
    | S q' => (q',O)
    end
  else
    (q, S r).

Definition tinc (d : nat * nat) (mp : nat) :=
  dminc (fst d) (snd d) mp.

Lemma dminc_neq : forall (q r mp : nat), dminc q r mp <> (q,r).
  intros q r mp. unfold dminc. destruct r. intros H. apply tup_eq in H. destruct H. apply succ_ex2 in H. 
  assumption. intros H. apply tup_eq in H. destruct H. apply succ_ex in H0. assumption.
  Defined.

Lemma divmod_x_plus_u : forall (x y q u : nat), divmod (plus x u) y q u = divmod x y q O.
  intros x y q u. generalize dependent x. generalize dependent y. generalize dependent q.
  induction u. intros q y x. rewrite plus_x_O. reflexivity.
  intros q y x. rewrite plus_x_Sy. rewrite divmod_t2. rewrite IHu. reflexivity.
  Defined.

Lemma divmod_u_plus_x : forall (x y q u : nat), divmod x y q (plus u x) = divmod O y q u.
  induction x. intros y q u. rewrite plus_x_O. reflexivity.
  intros y q u. rewrite plus_x_Sy. rewrite divmod_t2. rewrite IHx.
  reflexivity. Defined.

Lemma divmod_x_plus_y_u0 : forall (x y q : nat), divmod (plus x (S y)) y q O = divmod x y (S q) O.
  intros x y q. generalize dependent x. generalize dependent y.
  induction q. intros y x. induction y. rewrite plus_x_Sy. rewrite plus_x_O. rewrite divmod_t1. reflexivity.
  rewrite plus_x_Sy. rewrite divmod_t1. rewrite (divmod_x_plus_u x (S y) (S O) (S y)). reflexivity.
  intros y x. rewrite plus_x_Sy. rewrite divmod_t1. rewrite (divmod_x_plus_u x y (S (S q)) y). reflexivity.
  Defined.

Lemma divmod_xpn_y_q_upn : forall (x y q u n : nat), divmod (plus x n) y q (plus u n) = divmod x y q u.
  intros x y q u n. generalize dependent x. generalize dependent y. generalize dependent q. generalize dependent u.
  induction n; intros u q y x. rewrite ?plus_x_O. reflexivity.
  rewrite ?plus_x_Sy. rewrite divmod_t2. rewrite IHn. reflexivity.
  Defined.

Lemma divmod_leftO : forall (x y q u : nat), le x u -> divmod x y q u = divmod O y q (sub u x).
  intros x y q u H. apply le_sub in H.
  assert (divmod x y q u = divmod x y q (plus x (sub u x))).
  rewrite -> H. reflexivity. rewrite H0. assert (divmod x y q (plus x (sub u x)) = divmod (plus O x) y q (plus x (sub u x))).
  simpl. reflexivity. rewrite H1. rewrite (plus_comm x (sub u x)). 
  rewrite divmod_xpn_y_q_upn. reflexivity.
  Defined.

Lemma divmod_rightO : forall (x y q u : nat), le u x -> divmod x y q u = divmod (sub x u) y q O.
  intros x y q u H. apply le_sub in H.
  assert (divmod x y q u = divmod (plus u (sub x u)) y q u). rewrite -> H. reflexivity.
  rewrite H0. 
  assert (divmod (plus u (sub x u)) y q u = divmod (plus u (sub x u)) y q (plus O u)).
  simpl. reflexivity. rewrite H1. 
  rewrite (plus_comm u (sub x u)). rewrite divmod_xpn_y_q_upn. reflexivity.
  Defined.

Lemma divmod_x_plus_y_y : forall (x y q : nat), divmod (plus x (S y)) y q y = divmod x y (S q) y.
  intros x y q. rewrite ?plus_x_Sy. rewrite <- plus_Sx_y.
  rewrite divmod_x_plus_u. rewrite divmod_t1. reflexivity.
  Defined.

Lemma divmod_x_O_q_O : forall (x q : nat), divmod x O q O = (plus x q,O).
  induction x; intros q. rewrite divmod_t0. rewrite plus_O_y. reflexivity. 
  rewrite divmod_t1. rewrite IHx. rewrite plus_x_Sy. rewrite plus_Sx_y. reflexivity.
  Defined.

Lemma snd_divmod_S (x y q u : nat) :
  snd (divmod x y q u) = snd (divmod x y (S q) u).
Proof.
revert y q u. induction x as [|x IH]; intros y q [|u]; simpl; try reflexivity. rewrite <- (IH y (S q) y). reflexivity.
rewrite IH. reflexivity.
Defined.

Lemma divmod_spec : forall (x y q u : nat) , le u y ->
  let (q',u') := divmod x y q u in
  plus x (plus (times (S y) q) (sub y u)) = plus (times (S y) q') (sub y u') /\ le u' y.
Proof.
  intro x; induction x as [|x IHx].
  - simpl; intuition.
  - intros y q u H.
    destruct u as [|u]; simpl divmod.
    + generalize (IHx y (S q) y (le_x_x y)).
      destruct divmod as (q',u').
      intros (EQ,LE); split; trivial.
      rewrite sub_O. rewrite <- EQ. rewrite sub_n_n. rewrite plus_x_O.
      rewrite times_x_Sy. rewrite plus_x_Sy. rewrite plus_x_Sy.
      rewrite plus_Sx_y. reflexivity.
    + assert (H' : le u y).
      { apply le_trans with (S u); trivial.
        apply le_succ2. apply le_x_x. }
      generalize (IHx y q u H').
      destruct divmod as (q',u').
      intros (EQ,LE); split; trivial.
      rewrite <- EQ. rewrite plus_Sx_y. rewrite <- plus_x_Sy. rewrite <- plus_x_Sy. rewrite sub_x_Sy.
      reflexivity. assumption.
Defined.

Lemma divm_times_Sx_Sy_y_q_y : forall (x y q : nat), divmod (times (S x) (S y)) y q y = (plus (S x) q, y).
  induction x; intros y q. rewrite times_comm. rewrite times_x_SO. assert (plus O (S y) = S y). rewrite plus_O_y. reflexivity. 
  rewrite <- H. rewrite (divmod_x_plus_y_y O y q). rewrite divmod_t0. reflexivity.
  rewrite times_Sx_y. rewrite (divmod_x_plus_y_y (times (S x) (S y)) y q). rewrite IHx. rewrite plus_x_Sy. 
  rewrite <- (plus_Sx_y). reflexivity.
  Defined.

Lemma divm_times_x_Sy_y_q_y : forall (x y q : nat), divmod (times x (S y)) y q y = (plus x q, y).
  induction x; intros y q. rewrite times_comm. rewrite times_x_O. 
  rewrite plus_O_y. rewrite divmod_t0. reflexivity.
  rewrite times_Sx_y. rewrite divmod_x_plus_y_y. rewrite IHx. rewrite plus_x_Sy. rewrite plus_Sx_y. reflexivity.
  Defined. 

Lemma le_uy_le_dm : forall (x y q u : nat), le u y -> le (snd (divmod x y q u)) y.
  induction x.
  intros y q u. rewrite divmod_t0. unfold snd. intros h. assumption.
  destruct y; intros q u H; destruct u. rewrite divmod_x_O_q_O. simpl. reflexivity.
  simpl in H. fassume. rewrite divmod_t1.
  apply (IHx (S y) (S q) (S y)). apply le_x_x.
  rewrite divmod_t2. apply (IHx (S y) q u).
  apply le_succ1. assumption.
  Defined.

(* Div / Mod / addl sim functions *)

Definition div x y :=
  match y with
    | O => y
    | S y' => fst (divmod x y' O y')
  end.

Definition mod x y :=
  match y with
    | O => x
    | S y' => sub y' (snd (divmod x y' O y'))
  end.

Fixpoint gcd a b :=
  match a with
   | O => b
   | S a' => gcd (mod b (S a')) (S a')
  end.

Lemma mod_O_y : forall (y : nat), mod O y = O.
  induction y. reflexivity. simpl. rewrite sub_n_n. reflexivity.
  Defined.

Lemma mod_x_O : forall (x : nat), mod x O = x.
  intros x. unfold mod. simpl. reflexivity.
  Defined.

Lemma mod_x_SO : forall (x : nat), mod x (S O) = O.
  intros x. unfold mod. rewrite divmod_x_O_q_O. rewrite plus_x_O. unfold snd. reflexivity.
  Defined.

Lemma div_O_y : forall (y : nat), div O y = O.
  induction y. reflexivity.
  reflexivity.
  Defined.

Lemma div_x_O : forall (x : nat), div x O = O.
  intros x. unfold div. reflexivity.
  Defined.

Lemma div_x_SO : forall (x : nat), div x (S O) = x.
  induction x. reflexivity. unfold div. rewrite divmod_t1. rewrite divmod_x_O_q_O. unfold fst. rewrite plus_x_Sy. rewrite plus_x_O.
  reflexivity.
  Defined.

Lemma mod_x_Sy_le_y : forall (x y : nat), le (mod x (S y)) y.
  intros x y. unfold mod. 
  apply le_suby_y.
  Defined.

Lemma prod_mod_Sn_Sm : forall (n m : nat), mod (times (S n) (S m)) (S m) = O.
  intros n m. unfold mod. rewrite divm_times_Sx_Sy_y_q_y. simpl. apply sub_n_n.
  Defined.

Lemma prod_mod_n_m : forall (n m : nat), mod (times n m) m = O.
  destruct n; destruct m.
  reflexivity. simpl. rewrite sub_n_n. reflexivity.
  unfold mod. rewrite times_x_O. reflexivity.
  rewrite prod_mod_Sn_Sm. reflexivity.
  Defined.

Lemma exist_prod_imp_mod : forall (n m : nat), (exists (x : nat), times x m = n) -> mod n m = O.
  intros n m H. destruct H. rewrite <- H. rewrite prod_mod_n_m.
  reflexivity.
  Defined.

Lemma plus_nm_mod_m : forall (n m : nat), mod (plus n m) m = mod n m.
  intros n m. destruct m. simpl. rewrite plus_x_O. reflexivity.
  unfold mod. rewrite (divmod_x_plus_y_y n m O).
  rewrite <- snd_divmod_S.
  reflexivity.
  Defined.

Lemma nkm_mod_m : forall (k n m : nat), mod (plus n (times k m)) m = mod n m.
  induction k; intros n m. simpl. rewrite plus_x_O. reflexivity.
  rewrite times_Sx_y. rewrite -> (plus_assoc n (times k m) m).
  rewrite plus_nm_mod_m. rewrite IHk. reflexivity.
  Defined.

Lemma div_times_Sn_m : forall (n m : nat), div (times (S n) m) (S n) = m.
  intros n m. unfold div. rewrite times_comm. rewrite (divm_times_x_Sy_y_q_y m n O).
  simpl. rewrite plus_x_O. reflexivity.
  Defined.

Lemma div_mod_recon : forall (n r : nat), plus (times (S (S r)) (div (S (S n)) (S (S r)))) (mod (S (S n)) (S (S r))) = (S (S n)).
  intros n r.
  unfold div. unfold mod.
  assert (exists (q : nat * nat), q = divmod (S (S n)) (S r) O (S r)).
  exists (divmod (S (S n)) (S r) O (S r)). reflexivity. destruct H.
  destruct x.
  assert (fst (divmod (S (S n)) (S r) O (S r)) = n0). rewrite <- H. reflexivity.
  assert (snd (divmod (S (S n)) (S r) O (S r)) = n1). rewrite <- H. reflexivity.
  rewrite H0. rewrite H1.
  assert (le (S r) (S r)). apply le_x_x. apply (divmod_spec (S (S n)) (S r) O (S r)) in H2.
  rewrite times_x_O in H2. rewrite plus_O_y in H2.
  rewrite <- H in H2. destruct H2. rewrite sub_n_n in H2. rewrite plus_x_O in H2. rewrite H2. reflexivity.
  Defined.

Lemma div_mod_imp : forall (n r : nat), plus (times (S (S r)) (div n (S (S r)))) (mod n (S (S r))) = n.
  destruct n. intros r. simpl. rewrite times_x_O. rewrite ?plus_x_O. rewrite plus_O_y. rewrite sub_n_n.
  reflexivity. destruct n. intros r.
  unfold div. rewrite divmod_t2. rewrite divmod_t0. unfold fst. rewrite times_x_O. rewrite plus_O_y.
  unfold mod. rewrite divmod_t2. rewrite divmod_t0. unfold snd. assert (forall (w : nat), sub (S w) w = S O).
  induction w. simpl. reflexivity. rewrite sub_Sx_Sy. apply IHw. apply H.
  intro r. rewrite div_mod_recon. reflexivity.
  Defined.

Lemma lt_nm_impl_divab_O : forall (n u : nat), lt (S (S n)) (S (S u)) -> div (S (S n)) (S (S u)) = O.
  intros n u H. assert (plus (times (S (S u)) (div (S (S n)) (S (S u)))) (mod (S (S n)) (S (S u))) = S (S n)).
  apply div_mod_imp.
  remember (div (S (S n)) (S (S u))). destruct n0.
  reflexivity. rewrite times_x_Sy in H0. rewrite (plus_comm (times (S (S u)) n0) (S (S u))) in H0. rewrite <- plus_assoc in H0.
  rewrite <- H0 in H. apply lt_plusdisc in H. fassume.
  Defined.

Lemma lt_mod : forall (n u : nat), lt n (S (S u)) -> mod n (S (S u)) = n.
  intros n u H. destruct n. simpl. rewrite sub_n_n. reflexivity.
  destruct n. unfold mod. rewrite divmod_t2. rewrite divmod_t0. unfold snd. rewrite sub_Sx_x. reflexivity.
  assert (plus (times (S (S u)) (div (S (S n)) (S (S u)))) (mod (S (S n)) (S (S u))) =  (S (S n))).
  apply div_mod_imp. apply lt_nm_impl_divab_O in H. rewrite H in H0. rewrite times_x_O in H0.
  rewrite plus_O_y in H0. assumption.
  Defined.
  
Lemma mod_SSSx_SSx : forall (x : nat), mod (S (S (S x))) (S (S x)) = S O.
  intros x. remember (S (S x)).
  assert (S n = plus (S O) n).
  rewrite plus_Sx_y. rewrite plus_O_y. reflexivity. rewrite H. unfold mod.
  rewrite Heqn. rewrite (divmod_x_plus_y_y (S O) (S x) O). rewrite divmod_t2. rewrite divmod_t0.
  unfold snd. rewrite sub_Sx_x. reflexivity.
  Defined.

Lemma mod_x_x : forall (x : nat), mod x x = O.
  intros x. induction x. reflexivity.
  destruct x. reflexivity. unfold mod. rewrite divmod_rightO. rewrite sub_Sx_x. rewrite divmod_t1. rewrite divmod_t0.
  unfold snd. rewrite sub_n_n. reflexivity. apply le_succ2. apply le_x_x.
  Defined.

(* Divides / Divideb / Dividex *)

Definition divideb (n m : nat) :=
  eqb (mod n m) O.

Definition divides (n m : nat) :=
  mod n m = O.

Definition dividex (n m : nat) :=
  exists (x : nat), times m x = n.

Lemma divides_imp_divideb : forall (n m : nat), divides n m -> divideb n m = true.
  intros n m H. unfold divides in H. unfold divideb. rewrite H. reflexivity.
  Defined.

Lemma divideb_imp_divides : forall (n m : nat), divideb n m = true -> divides n m.
  intros n m H. unfold divideb in H. unfold divides.
  apply eqb_equal in H. assumption.
  Defined.

Lemma divideb_false_imp_not_divides : forall (n m : nat), divideb n m = false -> not (divides n m).
 intros n m H. unfold divideb in H. apply eqb_not_equal in H. unfold not. intros H1. unfold divides in H1.
 unfold not in H. apply H. assumption.
 Defined.

Lemma not_divides_imp_divideb_false : forall (n m : nat), not (divides n m) -> divideb n m = false.
  intros n m H. unfold not in H. remember (divideb n m). destruct b. assert (divideb n m = true). rewrite Heqb. reflexivity.
  apply divideb_imp_divides in H0. exfalso. apply H. assumption.
  reflexivity.
  Defined.


Lemma dividex_imp_divides : forall (n m : nat), dividex n m -> divides n m.
  intros n m H. unfold dividex in H. unfold divides.
  apply exist_prod_imp_mod.  
 destruct H. exists x.
  rewrite times_comm. assumption.
  Defined.

Lemma divides_imp_dividex : forall (n m : nat), divides n m -> dividex n m.
  intros n m H. unfold divides in H. unfold dividex. exists (div n m).
  destruct m. unfold div. unfold mod in H. rewrite H. reflexivity.
  unfold div. unfold mod in H.
  assert (le (snd (divmod n m O m)) m). apply (le_uy_le_dm n m O m). apply le_x_x.
  assert (m = snd (divmod n m O m)). apply sub_O_imp_eq in H. assumption. assumption.
  assert (S m = S (snd (divmod n m O m))). rewrite <- H1. reflexivity. rewrite H2.
  rewrite times_Sx_y. 
  assert (H3 := divmod_spec n m O m). assert (le m m). apply le_x_x. apply H3 in H4.
  destruct (divmod n m O m). destruct H4. unfold snd. unfold fst.
  rewrite times_x_O in H4. rewrite plus_O_y in H4. rewrite sub_n_n in H4. rewrite plus_x_O in H4.
  unfold snd in H1. rewrite <- H1. rewrite <- H1 in H4. rewrite sub_n_n in H4. rewrite plus_x_O in H4.
  rewrite H4. rewrite times_Sx_y.
  reflexivity.
  Defined.

Theorem succ_notdiv : forall (n m : nat), divides n (S (S m)) -> not (divides (S n) (S (S m))).
  intros n m H. unfold not. intros H1.
  apply divides_imp_dividex in H. apply divides_imp_dividex in H1.
  unfold dividex in H. unfold dividex in H1. destruct H. destruct H1.
  assert (sub (times (S (S m)) x0) (times (S (S m)) x) = sub (S n) n). rewrite H. rewrite H0.
  reflexivity.
  rewrite sub_Sx_y in H1. rewrite sub_n_n in H1.
  rewrite (times_comm (S (S m)) x0) in H1. rewrite (times_comm (S (S m)) x) in H1.
  rewrite prod_dist_sub in H1.
  assert (not (times (sub x0 x) (S (S m)) = S O)).
  apply times_SS_neq_SO.
  unfold not in H2. apply H2. assumption. apply le_x_x.
  Defined.

Lemma ndivides_SSSx_SSx : forall (x : nat), not (divides (S (S (S x))) (S (S x))).
  unfold divides. intros x. rewrite mod_SSSx_SSx. unfold not. discriminate.
  Defined.

Lemma ndivideb_SSx_SSy : forall (x y : nat), lt (S (S x)) (S (S y)) -> divideb (S (S x)) (S (S y)) = false.
  intros x y H. unfold divideb. rewrite lt_mod. simpl. reflexivity. assumption.
  Defined.

Lemma divideb_trans : forall (x y z : nat), divideb x y = true -> divideb y z = true -> divideb x z = true.
  intros x y z H1 H2. 

  apply divideb_imp_divides in H1. apply divides_imp_dividex in H1. unfold dividex in H1.
  destruct H1. apply divideb_imp_divides in H2. apply divides_imp_dividex in H2. unfold dividex in H2. destruct H2.
  apply divides_imp_divideb. apply dividex_imp_divides. unfold dividex. exists (times x1 x0). rewrite <- times_assoc.
  rewrite H0. rewrite H. reflexivity.
  Defined.

(* Factorial *)

Fixpoint fact (n : nat) :=
  match n with
  | O => S O
  | S n' => times n (fact n')
  end.

Lemma Sn_fact : forall (n : nat), times (S n) (fact n) = fact (S n).
  simpl. intros n. reflexivity.
  Defined.

(* Product List *)

Inductive plist : Set :=
  | T : plist
  | XS : nat -> plist -> plist.

Fixpoint prod_list (pl : plist) :=
  match pl with
  | T => S O
  | XS n pl' => times n (prod_list pl')
  end. 

Fixpoint pl_nat (n : nat) :=
  match n with
  | O => T
  | S n' => XS n (pl_nat n')
  end.

Lemma prod_plnat : forall (n : nat), prod_list (pl_nat n) = fact n.
  induction n. reflexivity.
  unfold pl_nat. fold pl_nat. unfold fact. fold fact.
  unfold prod_list; fold prod_list. rewrite IHn. reflexivity.
  Defined.

Lemma prod_list_n : forall (pl : plist) (n : nat), prod_list (XS n pl) = times n (prod_list pl).
  intros pl n. simpl. reflexivity.
  Defined.

Fixpoint contains (pl : plist) (target : nat) :=
  match pl with
  | T => False
  | XS n pl' => n = target \/ contains pl' target
  end.

Lemma contains_divides : forall (pl : plist) (n : nat), contains pl (S n) -> divides (prod_list pl) (S n).
  induction pl. intros n H. simpl in H. fassume.
  intros n0 H. unfold contains in H. fold contains in H.
  assert (n = (S n0) \/ n <> (S n0)).
  apply eq_or_not. destruct H0. rewrite H0. unfold prod_list; fold prod_list.
  apply (dividex_imp_divides). unfold dividex.
  exists (prod_list pl). reflexivity.
  unfold prod_list; fold prod_list. destruct H. exfalso. apply H0. assumption.
  apply IHpl in H. apply divides_imp_dividex in H.
  unfold dividex in H. destruct H. rewrite <- H.
  apply dividex_imp_divides. unfold dividex. 
  rewrite <- times_assoc. rewrite (times_comm n (S n0)). rewrite times_assoc.
  exists (times n x). reflexivity.
  Defined.

Lemma contains_plnat : forall (n m : nat), le (S m) n -> contains (pl_nat n) (S m).
  intros n m H. induction n. simpl in H. fassume.
  unfold contains; fold contains.
  simpl. assert ((S n) = (S m) \/ not ((S n) = (S m))). apply eq_or_not.
  destruct H0. left. assumption.
  apply le_neq in H. right. apply IHn. apply H. unfold not in H0. unfold not. intros H1. apply H0.
  rewrite H1. reflexivity.
  Defined.

Lemma prod_plnat_div : forall (n m : nat), le (S m) n -> dividex (prod_list (pl_nat n)) (S m).
  intros n m H. assert (contains (pl_nat n) (S m)). apply contains_plnat. assumption.
  apply contains_divides in H0. apply divides_imp_dividex in H0. assumption.
  Defined.

Lemma fact_div : forall (n m : nat), le (S m) n -> dividex (fact n) (S m).
  induction n. intros m H. simpl in H. fassume.
  intros m H. rewrite <- prod_plnat. rewrite <- prod_plnat in IHn. apply prod_plnat_div. assumption.
  Defined.

Lemma factp1_ndiv : forall (n m : nat), le (S (S m)) n -> not (divides (S (fact n)) (S (S m))).
  intros n m H. apply succ_notdiv. apply dividex_imp_divides. apply fact_div. assumption.
  Defined.

Fixpoint lpred (l : plist) :=
  match l with
  | T => T
  | XS u l' => l'
  end.

(* Min Prop *)

Lemma min_prop : forall (pb : nat -> bool) (n : nat), (forall (u : nat), le u n -> pb u = false) 
                  \/ (exists (min : nat), pb min = true /\ (forall (u : nat), lt u min -> pb u = false)).
  intros pb. induction n. remember (pb O). destruct b. right.
  exists O. split. rewrite Heqb. reflexivity.
  intros u H. unfold lt in H. apply le_Sx_O in H. fassume.
  left. intros u H. destruct u. rewrite Heqb. reflexivity.
  apply le_Sx_O in H; fassume.
  destruct IHn. remember (pb (S n)). destruct b.
  right. exists (S n). split.
  rewrite Heqb. reflexivity.
  intros u H2. unfold lt in H2. apply le_Sx_Sy in H2. apply (H u) in H2. assumption.
  left. intros u H2. apply le_x_Sy_reduct in H2. destruct H2. rewrite <- H0 in Heqb. rewrite Heqb. reflexivity.
  apply H in H0. assumption.
  right. destruct H. exists x. assumption.
  Defined.

Definition divideb_prop (n : nat) (d : nat) := divideb n (S (S d)).

(* Primality *)

Definition composite (n : nat) :=
  exists (m : nat), n <> (S (S m)) /\ divideb n (S (S m)) = true.

Definition unit (n : nat) :=
  n = O \/ n = S O.

Definition prime (n : nat) :=
  not (composite n) /\ not (unit n).

Lemma prime_reqs : forall (x : nat), ((exists (m : nat), (S (S x)) <> (S (S m)) /\ divideb (S (S x)) (S (S m)) = true) -> False) -> prime (S (S x)).
  intros x H.
  unfold prime. split.
  unfold not. intros H1. unfold composite in H1. apply H.
  assumption.
  unfold unit. unfold not. intros H1. destruct H1; discriminate.
  Defined.

(* Supporting Lemmas *)

Theorem always_divide_min_prop : 
  forall (n : nat), exists (md : nat), 
  divideb_prop (S (S n)) md = true /\ (forall (u : nat), lt u md -> divideb_prop (S (S n)) u = false).
  
  assert (forall (n : nat), (forall (u : nat), le u n -> divideb_prop (S (S n)) u = false)
                  \/ (exists (min : nat), divideb_prop (S (S n)) min = true /\ (forall (u : nat), lt u min -> divideb_prop (S (S n)) u = false))).
  intros n.
  apply (min_prop (divideb_prop (S (S n)))). intros n.
  destruct (H n).
  assert (divideb_prop (S (S n)) n = true).
  unfold divideb_prop. unfold divideb. rewrite mod_x_x. reflexivity.
  assert (divideb_prop (S (S n)) n = false).
  apply H0. apply le_x_x. rewrite H1 in H2. discriminate. assumption.
  Defined.

Lemma divideb_min_contra : forall (n x x0 : nat), lt (S (S x0)) (S (S x)) -> (forall u : nat, lt u x -> divideb_prop (S (S n)) u = false) -> divideb (S (S n)) (S (S x)) = true -> divideb (S (S x)) (S (S x0)) = true -> False.
  intros n x x0 H1 H2 H3 H4.
  assert (divideb (S (S n)) (S (S x0)) = true). apply (divideb_trans (S (S n)) (S (S x)) (S (S x0))). assumption. assumption.
  assert (divideb (S (S n)) (S (S x0)) = false). unfold divideb_prop in H1. apply H2. apply le_Sx_Sy. apply le_Sx_Sy. assumption.
  rewrite H in H0. discriminate.
  Defined.

Theorem exists_prime_div : forall (n : nat), exists (d : nat), divideb (S (S n)) (S (S d)) = true /\ prime (S (S d)).
  intros n. 
  (* bring in always_divide_min_prop as premise *)
  assert (exists (md : nat), divideb_prop (S (S n)) md = true /\ (forall (u : nat), lt u md -> divideb_prop (S (S n)) u = false)). apply always_divide_min_prop. 
  destruct H. destruct H.
  unfold divideb_prop in H; exists x. 
  split. assumption.  
  
  (* switch proof to requirements to be prime. *)
  apply (prime_reqs x). intros H1; destruct H1; destruct H1.
  
  (* prove for the three cases of trichotomy *)
  assert (lt (S (S x)) (S (S x0)) \/ lt (S (S x0)) (S (S x)) \/ (S (S x)) = (S (S x0))). apply trichotomy.
  destruct H3. apply ndivideb_SSx_SSy in H3; rewrite H2 in H3; discriminate.
  destruct H3; [apply (divideb_min_contra n x x0); repeat (assumption) | apply (eq_neq_false (S (S x)) (S (S x0))); repeat (assumption)].
  Defined.

Lemma prime_SSO : prime (S (S O)).
  unfold prime. unfold composite. unfold unit. split.
  unfold not. intros H1. destruct H1. destruct H.
  apply H. destruct x. reflexivity.
  assert (divideb (S (S O)) (S (S (S x))) = false). apply ndivideb_SSx_SSy. unfold lt. 
  apply le_Sx_Sy2. apply le_Sx_Sy2. apply le_Sx_Sy2. apply le_O_y. rewrite H0 in H1. discriminate.
  unfold not. intros H1. destruct H1. discriminate. discriminate.
  Defined.

(* Minor Lemmas for Final Proof *)

Lemma n_le_factn : forall (n : nat),  le n (fact n).
  induction n. reflexivity. unfold fact. fold fact. destruct n.
  reflexivity. assert (le (S O) (fact (S n))). assert (le (S O) (S n)). apply le_Sx_Sy2. apply le_O_y.
  apply (le_trans (S O) (S n) (fact (S n))). assumption. assumption.
  apply le_SO_y_le_prod. assumption.
  Defined.

Lemma le_divideb_false : forall (n u : nat), le (S (S u)) n -> divideb (S (fact n)) (S (S u)) = false.
  intros n u.
  assert (forall (u : nat), le (S (S u)) n -> not (divides (S (fact n)) (S (S u)))). apply factp1_ndiv. 
  assert (le (S (S u)) n -> ~ divides (S (fact n)) (S (S u))). intros H2. apply H in H2. assumption. 
  intros H1. apply H0 in H1. apply not_divides_imp_divideb_false. assumption.
  Defined.

Lemma fact_n_n0 : forall (n : nat), fact n <> O.
  induction n. unfold not. unfold fact. discriminate. unfold not. rewrite <- Sn_fact.
  intros H. unfold not in IHn. apply IHn. apply (times_xyO_or (S n) (fact n)) in H.
  destruct H. discriminate. assumption.
  Defined.

(* Inf Primes *)

Theorem infprimes : forall (n : nat), exists (m : nat), le n m /\ prime m.
  intros n. assert (forall (u : nat), le (S (S u)) n -> divideb (S (fact n)) (S (S u)) = false). intros u. apply (le_divideb_false n u).
  destruct n. exists (S (S O)); split; [ apply le_O_y | apply prime_SSO ]. 
  destruct n. exists (S (S O)); split; [ apply le_Sx_Sy2; apply le_O_y | apply prime_SSO].
  remember (S (fact (S (S n)))).
  destruct n0. discriminate. destruct n0. 
  assert (fact (S (S n)) <> O). apply fact_n_n0. exfalso; apply H0; apply succ_inj2 in Heqn0; rewrite Heqn0; reflexivity.
  assert (exists (d : nat), divideb (S (S n0)) (S (S d)) = true /\ prime (S (S d))). apply exists_prime_div. 
  destruct H0; destruct H0. rewrite Heqn0 in H0; exists (S (S x)).
  assert (le (S (S n)) (S (S x)) \/ le (S (S x)) (S (S n))). apply dichotomy. 
  destruct H2. 
    -- split; assumption.  
    -- apply (H x) in H2; rewrite Heqn0 in H2; rewrite H0 in H2; discriminate.
  Defined. 

