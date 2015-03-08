Require Export init.

(** Des hints et tactiques utiles pour les shifting/substitutions *)

Hint Extern 1 => 
match goal with
| |- context [le_dec ?a ?b] => destruct (le_dec a b); try omega
| |- context [eq_nat_dec ?a ?b] => destruct (eq_nat_dec a b); try omega
| H : context [le_dec ?a ?b] |- _ => destruct (le_dec a b); try omega
end.

Ltac destruct_match :=
  match goal with
  | H:context[match ?a with _ => _ end] |- _ => destruct a eqn:?; simpl in *
  | |- context[match ?a with _ => _ end] => destruct a eqn:?; simpl in *
  end.

(** ** Propriétés utiles de [tshift] *)

(** Décaler de 0 n'a pas d'effet *)

Lemma tshift_ident : forall T p , tshift T 0 p = T.
Proof.
  induction T; simpl; intros; [ destruct_match | f_equal .. ]; eauto.
Qed.

(** La composition commute faiblement en général *)

Lemma tshift_commut T :
  forall a c d (p : nat) , tshift (tshift T a p) c (d+p) = tshift (tshift T c (d-a+p)) a (p).
Proof.
induction T; intros a c d p; simpl in *.
- f_equal; eauto 7.
- f_equal; eauto.
- rewrite plus_n_Sm. 
  rewrite IHT with (p := (S p)). 
  do 3 f_equal. 
  omega.
Qed.

Lemma tshift_merge T : forall X K N Y, 
  tshift T (Y + X + K) N = tshift (tshift T (Y+X) N) K (N + Y).
Proof.
induction T; intros; simpl.
- repeat destruct_match; try omega; try (f_equal; omega).
- now rewrite <- IHT1, <- IHT2.
- now setoid_rewrite <- IHT.
Qed.

(** Version simplifiée de [tshift_commut] avec [a := 1], [d := S x] et [p := 0]. *)

Lemma tshift_commut_simpl T c d : tshift (tshift T 1 0) c (S d) = tshift (tshift T c d) 1 0.
Proof.
  replace (S d) with (S d + 0) at 1 by omega.
  replace d with (S d - 1 + 0) at 2 by omega.
  now apply tshift_commut.
Qed.

(** Simplification de la composition quand le plancher est nul. *)

Lemma tshift_plus1 T p : tshift T (S p) 0 = tshift (tshift T p 0) 1 0.
Proof.
  pose proof (tshift_merge T p 1 0 0). simpl in *. 
  now replace (p+1) with (S p) in * by omega. 
Qed.
  
(** ** Relation entre [tshift] et [tsubst]. *)

Lemma tsubst_tshift_swapDown: 
  forall T U m n, 
  tshift (tsubst T U n) 1 (n+m)  = tsubst (tshift T 1 (S (n+m))) (tshift U 1 (n+m)) n.
Proof.
induction T; intros; simpl.
- repeat destruct_match; try omega; try (f_equal; omega).
- now rewrite <- IHT1, IHT2.
- rewrite <- tshift_commut_simpl.
  specialize (IHT (tshift U 1 0) m (S n0)).
  simpl in IHT.
  congruence. 
Qed.

Lemma tsubst_tshift_swapUp : forall T X R K N U, 
  tsubst (tshift T K X) (tshift U (X+R+K) 0) (X+K+N) = tshift (tsubst T (tshift U (X+R) 0) (X+N)) K X.
Proof.
induction T; intros; simpl.
- repeat destruct_match; try omega; try (f_equal; omega).
  apply tshift_merge.
- now rewrite <- IHT1, IHT2.
- specialize (IHT (S X) R K N U).
  repeat rewrite <- tshift_plus1.
  simpl in IHT. 
  congruence.
Qed.

Lemma tsubst_tshift_swapIn : forall T K X U, 
  tsubst (tshift T (S K) X) U (X+K) = tshift T K X.
Proof.
induction T; intros; simpl.
- repeat destruct_match; try omega; try (f_equal; omega).
- now rewrite IHT1, IHT2.
- f_equal.
  specialize (IHT K (S X) (tshift U 1 0)).
  simpl in IHT. 
  assumption.
Qed.

Lemma tsubst_tshift_ident T : forall U k, T = tsubst (tshift T 1 k) U k.
Proof.
  intros. symmetry.
  pose proof (tsubst_tshift_swapIn T 0 k U).
  now rewrite tshift_ident, plus_0_r in H.
Qed.

Lemma tsubst_commut_general T : forall k U V X,
tsubst (tsubst T (tshift U k 0) k) (tshift V k 0) (k+X) 
= tsubst (tsubst T (tshift V (S k) 0) (S k + X)) (tshift (tsubst U V X) k 0) k.
Proof.
induction T; intros; simpl.
- repeat destruct_match; try omega; try (f_equal; omega).
  + symmetry.
    apply tsubst_tshift_swapIn.
  + subst.
    pose proof (tsubst_tshift_swapUp U 0 0 x X V).
    rewrite tshift_ident in H.
    assumption.
- replace  (S (k+X)) with (S k + X) by omega. 
  now rewrite <- IHT1, <- IHT2.
- f_equal.
  replace  (S (S (k+X))) with (S (S k) + X) by omega. 
  setoid_rewrite <- tshift_plus1 at 3 4.
  replace (S (k+1)) with (S k + 1) by omega.
  rewrite <- IHT.
  rewrite <- tshift_plus1, <- tshift_plus1. trivial.
Qed.


Lemma tsubst_commut T U V X : 
  tsubst (tsubst T U 0) V X = (tsubst (tsubst T (tshift V 1 0) (S X)) (tsubst U V X) 0).
Proof.
  pose proof (tsubst_commut_general T 0 U V X).
  repeat rewrite tshift_ident in H.
  now repeat rewrite plus_O_n in H.
Qed.

