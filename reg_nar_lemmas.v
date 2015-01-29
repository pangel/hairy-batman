Require Export shift_lemmas.

(** * Lemmes utiles pour prouver [regularity] et [narrowing] *)

(** Les variables avec les noms suivants prennent le type correspondant par défaut : *)

Implicit Types 
(x y z X Y Z : nat)
(T U V : typ)
(n k p q : kind)
(t s u v : term)
(e f : env).

(** ** Insertion d'un [kind] dans un environnement *)

(** [insert_kind X e e'] est vrai quand [e'] est [e] avec une variable de type 
   insérée en [X]ième position. *)

Inductive insert_kind : nat -> env -> env -> Prop :=
| inil e p : insert_kind 0 e ((etvar p)::e)
| iskip n T e e' : insert_kind n e e' -> insert_kind n ((evar T)::e) ((evar (tshift T 1 n))::e')
| icons n p e e' : insert_kind n e e' -> insert_kind (S n) ((etvar p)::e) ((etvar p)::e').
Hint Constructors insert_kind.

(** *** Relation entre [insert_kind] et [get_kind] *) 

(** L'insertion en position [X] maintient le résultat de [get_kind _ Y] à [shift_var Y 1 X] près. *)

Lemma get_kind_insert_shift e e' X Y :
  insert_kind X e e' -> get_kind e Y = get_kind e' (shift_var Y 1 X).
Proof.
  intros D. revert Y.
  induction D as [e p'| | ]; simpl; intros Y; eauto.
  destruct Y; eauto.
  simpl in *.
  specialize (IHD Y).
  eauto.
Qed.

Lemma insert_kind_wf_typ n e e' T : insert_kind n e e' -> wf_typ e T -> wf_typ e' (tshift T 1 n).
Proof.
  revert n e e'.
  induction T;
  intros n' e e' A B;
  simpl in *.
  - contradict B.
    erewrite get_kind_insert_shift; eauto.
  - destruct B as [B C]. 
    split; eauto.
  - refine (IHT (1+n') (etvar n::e) _ _ _).
    + apply (icons _ A).
    + assumption.
Qed.

(** *** Relation entre [insert_kind] et [wf_env] *)

(** La well-formedness est fermée par insertion/suppression. *)

Lemma insert_kind_wf_env X e e' : 
  insert_kind X e e' -> wf_env e -> wf_env e'.
Proof.
  induction 1; simpl; auto.
  intros [D E].
  split; auto.
  now apply insert_kind_wf_typ with (n:=n) (e:=e).
Qed.


Lemma insert_kind_wf_env_conv X e e' :
  insert_kind X e e' -> wf_env e' -> wf_env e.
admit.
Qed.

(** *** Relation entre [insert_kind] et [kinding] *)

(** Les variables de type "après" [X] doivent avoir leur pointeur décalé. *)

Lemma insert_kind_kinding X e e' T p: 
  insert_kind X e e' -> kinding e T p -> kinding e' (tshift T 1 X) p.
Proof.
  revert p X e e'.
  induction T; intros p X e e' D E.
  - inversion E. subst.
    refine (kvar _ H1 _).
    + erewrite <- get_kind_insert_shift; eauto.
    + eapply insert_kind_wf_env; eauto. 
  - inversion E. subst.
    simpl.
    refine (karrow _ _); eauto.
  - apply (icons n) in D.
    inversion E. subst.
    refine (kall _).
    eapply IHT; eauto.
Qed.

(** *** Relation entre [insert_kind] et [get_typ] *)

(** Les variables de terme qui pointent "après" la variable insérée sont décalées de 1 *)

Lemma get_type_insert_some e e' X :
  insert_kind X e e' -> forall Y p T, 
  get_typ_aux e Y 0 = Some (tshift T p 0) -> 
  get_typ_aux e' Y 0 = Some (tshift (tshift T 1 (X-p)) p 0).
Proof.
induction 1; simpl get_typ_aux; intros Y p' T0 A. 
- replace (0-p') with 0 by omega.
  replace 0 with (0+0) at 4 by omega.
  rewrite (tshift_commut T0 1 p' 0 0).
  replace (0-1+0) with 0 by omega.
  now apply get_typ_aux_shift.
- destruct Y; eauto.
  rewrite tshift_ident in *.
  inv A.
  f_equal.
  replace (n-p') with (n-p'+0) by omega.
  rewrite <- tshift_commut . do 2 f_equal. auto.
- assert (exists T', (tshift T0 p' 0) = tshift T' 1 0 /\ get_typ_aux e Y 0 = Some (tshift T' (p'-1) 0)). admit.
  destruct H0 as [T' [B C]]. subst.
  specialize (IHinsert_kind _ _ _ C).
  apply get_typ_aux_shift in IHinsert_kind.
  rewrite IHinsert_kind.
  f_equal.
  rewrite <- tshift_plus1.
  destruct p'.
  + simpl. 
    rewrite tshift_ident.
    replace (S n) with (n+1) by omega. 
    simpl in *.
  admit.
+ admit.
Qed.  
Arguments get_typ / _ _.

(** *** Préservation du [typing] par [insert_kind] *)

Lemma insert_kind_typing X e e' t T : 
  insert_kind X e e' -> typing e t T -> typing e' (tshift_in_term t 1 X) (tshift T 1 X).
Proof.
  intros.
  revert H. revert X e'.
  induction H0; intros.
  - simpl in *.
    setoid_rewrite <- tshift_ident with (p:=0) in H.
    pose proof (get_type_insert_some H1 H).
    rewrite <- tshift_commut_simpl in H2.
    rewrite tshift_ident in H2.
    apply (insert_kind_wf_env H1) in H0.
    eauto.
  - simpl. eauto.
  - simpl. eauto.
  - simpl. eauto.
  - simpl in *. 
    pose proof (insert_kind_kinding H1 H).
    specialize (IHtyping X e' H1).
    rewrite tsubst_tshift_swapN.
    + eauto.
    + omega.
Qed.

(** ** Suppression d'une variable de terme de l'environnement. *)

Fixpoint remove_var e x := match e with
| nil => nil
| (etvar k)::e' => (etvar k)::remove_var e' x
| (evar T)::e' => match x with
  | 0 => e'
  | S y => (evar T)::(remove_var e' y)
  end
end.

(** *** [remove_var] est ignoré par [kinding] et [get_kind] *)

Lemma get_kind_remove_var_noop e : forall x y, get_kind e y = get_kind (remove_var e x) y.
Proof.
  induction e as [|[|]]; intros; simpl in *; auto; [destruct x | destruct y]; eauto.
Qed.

Lemma kinding_remove e U p x : kinding e U p -> kinding (remove_var e x) U p.
admit.
Qed.

Lemma kinding_remove_impl e x U p : kinding (remove_var e x) U p -> kinding e U p.
admit.
Qed.

(** Cas particulier : Weakening par terme préserve [kinding] *)
   
Lemma kinding_remove_impl1 e U p T : kinding e U p -> kinding (evar T::e) U p.
Proof.
  replace e with (remove_var (evar T::e) 0) at 1 by auto.
  apply kinding_remove_impl.
Qed.


(** Relation entre [remove_var] et [get_typ] *)

(** Les variables de terme "avant" la variable enlevée restent en place celles "après" sont décalées vers la gauche. *)

Lemma rem_var_less x y T e : get_typ e y = Some T -> y < x -> get_typ (remove_var e x) y = Some T.
admit.
Qed.

Lemma rem_var_more x y T e : get_typ e y = Some T -> y > x -> get_typ (remove_var e x) (y-1) = Some T.
admit.
Qed.

Lemma rem_var_more_conv e x y T : get_typ (remove_var e x) y = Some T -> x <= y -> get_typ e (S y) = Some T.
admit.
Qed.

Lemma rem_var_less_conv e x y T : get_typ (remove_var e x) y = Some T -> x > y -> get_typ e y = Some T.
admit.
Qed.

(** *** Relation entre [remove_var] et [wf_env] *)

Lemma remove_var_preserve_wf_env e x : wf_env e -> wf_env (remove_var e x).
admit.
Qed.

(** ** [typing] préservé par substitution *)

Lemma subst_preserves_typing :
  forall e x t u Tt Tu,
  typing e t Tt ->
  typing (remove_var e x) u Tu -> get_typ e x = Some Tu ->
  typing (remove_var e x) (subst t u x) Tt.
Proof.
  intros. revert H1 H0. revert x u Tu. induction H; intros. 
  - simpl. destruct (le_dec x0 x); 
    [ destruct (le_lt_eq_dec x0 x _) | ]. 
    + constructor.     
      * now apply rem_var_more.
      * now apply remove_var_preserve_wf_env.
    + subst.
      rewrite H in H1. 
      now inv H1.
    + constructor.
      * apply rem_var_less; [assumption | omega].
      * now apply remove_var_preserve_wf_env.
  - simpl.
    apply typing_weak1 with (U:=T) in H0.
    specialize (IHtyping (S x) (shift u 1 0) Tu).
    eauto.
  - simpl; eauto.
  - simpl in *.
    constructor.
    specialize (IHtyping x (tshift_in_term u 1 0) (tshift Tu 1 0)). 
    apply IHtyping; auto. 
    + setoid_rewrite <- tshift_ident with (p:=0) in H1.
      rewrite tshift_plus1.
      now apply get_typ_aux_shift.
    + eapply insert_kind_typing; eauto.    
  - simpl in *.
    apply kinding_remove with (x:=x) in H0.
    apply rtapp with (p:=p); eauto.
Qed.

(** ** Préservations de [typing]/[kinding] par weakening *)

(** Well-formedness maintenue par weakening *)

Lemma remove_var_preserves_wf_typ T : forall e x, wf_typ (remove_var e x) T -> wf_typ e T.
Proof.
  induction T as [y | | ]; intros e X A; simpl in *; intuition; eauto.
  contradict A.
  now rewrite <- get_kind_remove_var_noop.
Qed.


Lemma remove_var_implies_wf_typ T : forall e x, wf_typ (remove_var e x) T -> wf_typ e T.
Proof.
  induction T as [y | | ]; intros e X A; simpl in *; intuition; eauto.
  contradict A.
  now rewrite <- get_kind_remove_var_noop.
Qed.

(** [typing] maintenu par weakening *)

Lemma typing_weakening_var_ind :
  forall e x t T,
  wf_env e -> typing (remove_var e x) t T -> typing e (shift t 1 x) T.
Proof.
  intros e x t T A B. revert A. dependent induction B; intros; simpl in *; eauto.
  - constructor; auto.
    destruct (le_dec x x0).
    + apply rem_var_more_conv with (x:=x); auto.
    + apply rem_var_less_conv with (x:=x); auto; omega.
  - constructor.
    specialize (IHB (evar T::e) (S x)). simpl in *.
    apply IHB.
    + auto.
    + split; auto.
      apply typing_impl_wf_env in B as [? ?]. 
      now apply remove_var_preserves_wf_typ with (x:=x).
  - apply kinding_remove_impl in H.
    eapply rtapp with (p:=p); auto. 
Qed.


(** Version générale de la préservation du kinding dans un environnement affaibli
    par des variables de terme et de type *)

Lemma get_typ_kinding_general e : 
  forall x T m, 
  get_typ_aux e x 0 = Some (tshift T m 0) -> 
  wf_env e -> 
  exists p, kinding e (tshift T m 0) p.
Proof.
induction e as [|[U|q]]; intros x T m A B.
- discriminate.
- destruct x.
  + destruct B.
    inv A.
    rewrite tshift_ident in H2.
    subst.
    apply wf_typ_impl_kinding in H as [? ?].
    rewrite tshift_ident.
    eauto using kinding_remove_impl1.
  + simpl in *.
    destruct B as [B1 B2].
    destruct (IHe _ _ _ A B2) as [k C]. 
    exists k.
    now apply kinding_remove_impl1.
- simpl in *.
  destruct (get_typ_aux_unshift A) as (T' & D & C).
  setoid_rewrite <- tshift_ident with (p:=0) in C.
  pose proof (IHe _ _ _ C B) as [p E].
  subst.
  exists p.
  rewrite D.
  rewrite tshift_ident in *. 
  now apply insert_kind_kinding with (e:=e) (T:=T').
Qed.

(** ** Préservation du [kinding] par subsitution *)

Lemma tsubst_preserves_kinding e e' X U T kU kT :
insert_kind X e e' ->
get_kind e' X = Some kU ->
kinding e' T kT ->
kinding e U kU ->
kinding e (tsubst T U X) kT.
Proof.
intros A B C. revert A B. revert e X U kU. dependent induction C ; intros e0 X0 U' kU A B C'.
- simpl.
  assert (wf_env e0) by eauto using insert_kind_wf_env_conv. 
  destruct (le_dec X0 X).
  + destruct (le_lt_eq_dec _ _ _).
    * destruct X; try omega.
      cut (get_kind e0 X = Some p); eauto.
      erewrite get_kind_insert_shift with (e':=e) (X:=X0);
      simpl; eauto.
    * subst. 
      assert (p = kU) by congruence. 
      subst.
      eauto.
  + cut (get_kind e0 X = Some p); eauto. 
    erewrite get_kind_insert_shift with (e':=e) (X:=X0);
    simpl; eauto.
- simpl in *. eauto.
- simpl in *.
  constructor.
  apply (IHC (etvar q::e0) (S X0) (tshift U' 1 0) kU (icons _ A) B (insert_kind_kinding (inil e0 q) C')).
Qed.

