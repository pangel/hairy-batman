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

(** Propriétés utiles de [tshift] : décaler de 0 n'a pas d'effet, la composition 
    commute faiblement, ou fortement quand le plancher est 0, et elle est injective. *)

Lemma tshift_ident : forall T p , tshift T 0 p = T.
Proof.
  induction T; simpl; intros; [ destruct_match | f_equal .. ]; eauto.
Qed.

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

(** TODO a simpler version of commut to be used elsewhere *)

Lemma tshift_plusm T p : forall m, tshift T (S p) m = tshift (tshift T 1 m) p (m+1).
Proof.
induction T; intros; simpl in *; auto.
- now rewrite IHT1, IHT2.
- now rewrite IHT.
Qed.

Lemma tshift_plus1 T p :  tshift T (S p) 0 = tshift (tshift T p 0) 1 0.
Proof.
transitivity (tshift (tshift T 1 0) p 1).
- now rewrite tshift_plusm.
- apply (tshift_commut T 1 p 1 0).
Qed.
(*
Lemma tshift_inject T U : forall m,  tshift T 1 m = tshift U 1 m -> T = U.
revert T U.
induction T.
- destruct U; try discriminate ; try f_equal.
  simpl in *.
  intros.
  injection H as H1. f_equal. 
  auto.
- destruct U; try discriminate.
  intros. simpl in *.
  injection H as H1 H2.
  f_equal.
  + rewrite (IHT1 U1 m) ; auto.
  + rewrite (IHT2 U2 m) ; auto.
- destruct U; try discriminate.
  simpl in *.
  intros.
  injection H as H1 H2.
  f_equal.
  + apply H2.
  + rewrite (IHT U (S m)) ;auto.
Qed.
*)

(** Version générale nombre de shifts *)
(*
Lemma tshift_remN:
  forall T U m n,
  tshift T m n = tshift U m n -> T = U.
Proof.
induction T.
- destruct U; try discriminate ; try f_equal.
  simpl in *.
  intros.
  injection H as H1. f_equal. 
  auto.
- destruct U; try discriminate.
  intros. simpl in *.
  injection H as H1 H2.
  f_equal.
  + rewrite (IHT1 U1 m n) ; auto.
  + rewrite (IHT2 U2 m n) ; auto.
- destruct U; try discriminate.
  simpl in *.
  intros.
  injection H as H1 H2.
  f_equal.
  + apply H2.
  + rewrite (IHT U m (S n1)) ;auto.
Qed.

Lemma tshift_rem1 T U p k : tshift T (S p) 0 = tshift U (S k) 0 -> tshift T p 0 = tshift U k 0.
Proof.
intros.
refine (@tshift_inject _ _  0 _).
replace (tshift (tshift T p 0) 1 0) with (tshift T (S p) 0).
- replace (tshift (tshift U k 0) 1 0) with (tshift U (S k) 0).
  + apply H.
  + apply tshift_plus1.
- apply tshift_plus1.
Qed.
*)
Lemma tshift_injectl T U p k n : tshift T (S p) n = tshift U (S k) n -> tshift T p n = tshift U k n.
revert U n.
induction T.
- destruct U; try discriminate ; try f_equal.
  simpl in *.
  intros.
  injection H as H1. f_equal. 
  auto.
- destruct U; try discriminate.
  intros. simpl in *.
  injection H as H1 H2.
  f_equal.
  + rewrite (IHT1 U1 n) ; auto.
  + rewrite (IHT2 U2 n) ; auto.
- destruct U; try discriminate.
  simpl in *.
  intros.
  injection H as H1 H2.
  f_equal.
  + apply H2.
  + rewrite (IHT U (S n1)) ;auto.
Qed.

Lemma tshift_inject  T U m n : tshift T m n = tshift U m n -> T = U.
induction m; intros.
- now repeat rewrite tshift_ident in *.
- apply tshift_injectl in H. auto.
Qed.

Lemma tshift_swap1 T n : tshift (tshift T 1 n) 1 0 = tshift (tshift T 1 0) 1 (S n).
Proof.
symmetry.
replace (S n) with (n + 1 + 0) by omega.
replace (n) with (n + 1 -1 + 0) at 2 by omega.
apply (tshift_commut T 1 1 (n+1) 0).
Qed.

Lemma tshift_swapN T X p : tshift (tshift T 1 (X-p)) p 0 = tshift (tshift T p 0) 1 X.
admit.
Qed.

Lemma tshift_shape : forall e T' n, get_typ_aux e n 0 = Some T' -> exists k T'', T' = tshift T'' k 0.
admit.
Qed.

(** Relation entre [tsubst] et [tshift]. *)

Lemma tsubst_tshift_swapN: 
  forall T U X n, n <= X -> (tshift (tsubst T U n) 1 X) = tsubst (tshift T 1 (S X)) (tshift U 1 X) n.
Proof.
induction T; intros; simpl in *.
- destruct_match; try omega; try (f_equal; omega); auto.
- rewrite IHT1, IHT2; auto.
- rewrite IHT with (X:=S X); try omega.
  do 2 f_equal.
  now rewrite <- tshift_swap1.
Qed.


(** Relation entre [get_typ_aux] et [tshift] : augmenter le [tshift] initial
    renvoie un type tshifté d'un de plus *)

(** Version avec [tshift] initial quelconque *)

Lemma get_typ_plusone : 
  forall e Y T n, get_typ_aux e Y n = Some T -> get_typ_aux e Y (S n) = Some (tshift T 1 0).
Proof.
  induction e.
  - intros.
    simpl in *.
    discriminate.
  - destruct a.
    + simpl in *.
      destruct Y.
      * { intros.
          injection H as H1.
          f_equal.
          replace T0 with (tshift T n 0).
          apply tshift_plus1.
        }
      * { intros.
          eauto.
         }
    + simpl in *.
      intros.
      rewrite IHe with (T :=T) ; auto.
Qed.

(** Version avec [tshift] renvoyé quelconque *)

Lemma get_typ_aux_shift1 e x Tu n : 
  get_typ_aux e x 0 = Some (tshift Tu n 0) -> get_typ_aux e x 1 = Some (tshift Tu (1+n) 0).
admit.
Qed.


Lemma get_typ_aux_unshift1 e x T m: 
  get_typ_aux e x (S m) = Some (tshift T m 0) ->
  exists T', get_typ_aux e x m = Some (tshift T' m 0) /\ T = (tshift T' 1 0).
Proof.
admit.
Qed.


(* TODO merge above 2 defns. *)

(** Dans l'autre sens, avoir un [tshift] initial non nul implique que le type a
    été shifté au moins une fois *)

Lemma get_typ_aux_1 e Y T : 
  get_typ_aux e Y 1 = Some T -> exists T', T = tshift T' 1 0 /\ get_typ_aux e Y 0 = Some T'.
admit.
Qed.