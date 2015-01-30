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

(** Version simplifiée de [tshift_commut] avec [a := 1], [d := S x] et [p := 0]. *)

Lemma tshift_commut_simpl T c d : tshift (tshift T 1 0) c (S d) = tshift (tshift T c d) 1 0.
Proof.
replace (S d) with (S d + 0) at 1 by omega.
replace d with (S d - 1 + 0) at 2 by omega.
now apply tshift_commut.
Qed.
(** Simplification de la composition en général. *)

Lemma tshift_plusm T p : forall m, tshift T (S p) m = tshift (tshift T 1 m) p (m+1).
Proof.
induction T; intros; simpl in *; auto.
- now rewrite IHT1, IHT2.
- now rewrite IHT.
Qed.

(** Simplification de la composition quand le plancher est nul. *)

Lemma tshift_plus1 T p :  tshift T (S p) 0 = tshift (tshift T p 0) 1 0.
Proof.
transitivity (tshift (tshift T 1 0) p 1).
- now rewrite tshift_plusm.
- apply (tshift_commut T 1 p 1 0).
Qed.

(** ** Relation entre [tshift] et d'autres fonctions *)

(** *** Relation utile entre [tshift] et [tsubst]. *)

Lemma tsubst_tshift_swapN: 
  forall T U X n, n <= X -> (tshift (tsubst T U n) 1 X) = tsubst (tshift T 1 (S X)) (tshift U 1 X) n.
Proof.
induction T; intros; simpl in *.
- repeat destruct_match; try omega; try (f_equal; omega); auto.
- rewrite IHT1, IHT2; auto.
- rewrite IHT with (X:=S X); try omega.
  now rewrite tshift_commut_simpl.
Qed.