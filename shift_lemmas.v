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
  | |- context[match ?a with _ => _ end] => destruct a; simpl in *; try destruct_match
  | H:context[match ?a with _ => _ end] |- _ => destruct a; simpl in *; try destruct_match
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

(** Elle commute fortement quand le plancher est nul. *)

Lemma tshift_commut_simpl T a c d : tshift (tshift T a 0) c d = tshift (tshift T c (d-a)) a 0.
Proof.
replace d with (d+0) at 1 by omega.
replace (d - a) with (d - a + 0) by omega.
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

(** Injectivité de [tshift], lemme puis cas où [p = k]. *)

Lemma tshift_injectl T U p k n : tshift T (S p) n = tshift U (S k) n -> tshift T p n = tshift U k n.
Proof.
  revert U n.
  induction T; intros [ | | ] ? H ; inv H ; simpl; f_equal; eauto.
Qed.

Lemma tshift_inject  T U m n : tshift T m n = tshift U m n -> T = U.
Proof.
induction m; intros.
- now repeat rewrite tshift_ident in *.
- apply tshift_injectl in H. auto.
Qed.

(** ** Relation entre [tshift] et d'autres fonctions *)

(** *** Relation utile entre [tshift] et [tsubst]. *)

Lemma tsubst_tshift_swapN: 
  forall T U X n, n <= X -> (tshift (tsubst T U n) 1 X) = tsubst (tshift T 1 (S X)) (tshift U 1 X) n.
Proof.
induction T; intros; simpl in *.
- destruct_match; try omega; try (f_equal; omega); auto.
- rewrite IHT1, IHT2; auto.
- rewrite IHT with (X:=S X); try omega.
  do 2 f_equal.
  replace X with (S X - 1) at 2 by omega. 
  apply tshift_commut_simpl.
Qed.


(** *** Relation entre |tshift] et [get_typ_aux] *)

(** Le décalage dans le [tshift] initial reflète celui donné à [get_typ_aux]. *)

Lemma get_typ_aux_shift : 
  forall e Y T n, get_typ_aux e Y n = Some T -> get_typ_aux e Y (S n) = Some (tshift T 1 0).
Proof.
  induction e as [ | [|] ]; intros; simpl in *; eauto.
  destruct Y.
  - inv H. 
    f_equal. 
    apply tshift_plus1. 
  - now rewrite IHe with (T:=T0).
Qed.

(** Dans l'autre sens, avoir un [tshift] initial non nul implique que le type a
    été shifté au moins une fois *)

Lemma get_typ_aux_unshift e x T m :
  get_typ_aux e x 1 = Some (tshift T m 0) ->
  exists T', (tshift T m 0) = tshift T' 1 0 /\ get_typ_aux e x 0 = Some T'.
Proof.
  admit.
Qed.
