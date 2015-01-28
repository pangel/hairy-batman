Require Export shift_lemmas.

(** Les variables avec les noms suivants prennent le type correspondant par défaut : *)
Implicit Types 
(x y z X Y Z : nat)
(T U V : typ)
(n k p q : kind)
(t s u v : term)
(e f : env).

(** [insert_kind X e e'] est vrai quand [e'] est [e] avec une variable de type 
   insérée en [X]ième position. *)

Inductive insert_kind : nat -> env -> env -> Prop :=
| inil e p : insert_kind 0 e ((etvar p)::e)
| iskip n T e e' : insert_kind n e e' -> insert_kind n ((evar T)::e) ((evar (tshift T 1 n))::e')
| icons n p e e' : insert_kind n e e' -> insert_kind (S n) ((etvar p)::e) ((etvar p)::e').
Hint Constructors insert_kind.

(** Relation entre [insert_kind] et [get_kind] : l'insertion en position [X] maintient
    le résultat à de [get_kind _ Y] à [shift_var Y 1 X] près. *)

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

(** Relation entre [insert_kind] et [wf_env] : la well-formedness est fermée 
    par insertion/suppression. *)

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

(** Relation entre [insert_kind] et [kinding] : les variables de type "après"
    [X] doivent avoir leur pointeur décalé. *)

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

(** Version générale de l'effet d'[insert_kind] sur [get_typ] *)

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
  now apply get_typ_plusone.
- destruct Y; eauto.
  rewrite tshift_ident in *.
  inv A.
  f_equal.
  replace (n-p') with (n-p'+0) by omega.
  rewrite <- tshift_commut . do 2 f_equal. auto.
- apply get_typ_aux_1 in A as [T' [A B]].
  destruct p' as [|p'].
  + rewrite tshift_ident in A. 
    replace T' with (tshift T' 0 0) in B.
    subst.
    * specialize (IHinsert_kind _ _ _ B).
      rewrite tshift_ident in *.
      simpl in *.
      apply get_typ_plusone in IHinsert_kind.
      rewrite IHinsert_kind.
      rewrite <- minus_n_O.      
      now rewrite tshift_swap1.      
    * apply tshift_ident.   
  + apply tshift_rem1 in A.
    rewrite tshift_ident in A.
    subst.
    specialize (IHinsert_kind _ _ _ B).
    apply get_typ_plusone in IHinsert_kind.
    rewrite IHinsert_kind.
    f_equal. 
    replace (S n - S p') with (n - p') by omega.
    now rewrite <- tshift_plus1.
Qed.

Arguments get_typ / _ _.


(** Préservation du typage par [insert_kind] *)

Lemma insert_kind_typing X e e' t T : 
  insert_kind X e e' -> typing e t T -> typing e' (tshift_in_term t 1 X) (tshift T 1 X).
Proof.
  intros.
  revert H. revert X e'.
  induction H0; intros.
  - simpl in *. 
    pose proof (tshift_shape H) as (k & T'' & A); subst.
    pose proof (get_type_insert_some H1 H).
    rewrite tshift_swapN in H2.
    apply (insert_kind_wf_env H1) in H0.
    simpl.
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


(* TODO *)
(*
Definition subst_env T x (d:envElem) := match d with
| (evar U) => evar (tsubst U T x)
| d => d
end.

Inductive env_subst p T : env -> env -> Prop :=

| snil e : env_subst 0 T ((etvar p)::e) e

| scons e e' d : env_subst p T e e' -> env_subst p T (d::e) (d::e').

Fixpoint replace_var e n p := match e with
| nil => nil
| d::e' => match n with
  | 0 => match d with
    | etvar q => (etvar p)::e'
    | d => d::e'
    end
  | S n' => d::(replace_var e' n p)
  end

*)

(** Suppression d'une variable de terme de l'environnement. *)

Fixpoint remove_var e x := match e with
| nil => nil
| (etvar k)::e' => (etvar k)::remove_var e' x
| (evar T)::e' => match x with
  | 0 => e'
  | S y => (evar T)::(remove_var e' y)
  end
end.

(** [remove_var] préserve [get_kind] et [kinding]. *)

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


(** Relation entre [remove_var] et [get_typ] : les variables de terme "avant" la variable enlevée restent en place, 
celles "après" sont décalées vers la gauche. *)

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

(** Enlever une variable de terme n'impacte pas la well-formedness. *)

Lemma remove_var_preserve_wf_env e x : wf_env e -> wf_env (remove_var e x).
admit.
Qed.

(** Substituer un terme dans un terme préserve le typage si les types de la variable et du substituant coïncident. *)

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
      now apply get_typ_aux_shift1 in H1.
    + eapply insert_kind_typing; eauto.    
  - simpl in *.
    apply kinding_remove with (x:=x) in H0.
    apply rtapp with (p:=p); eauto.
Qed.


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

(** Typage maintenu par weakening *)

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
  get_typ_aux e x m = Some (tshift T m 0) -> 
  wf_env e -> 
  exists p, kinding e T p.
Proof.
induction e as [|[U|q]]; intros x T m A B.
- discriminate.
- destruct x.
  + destruct B.
    inv A. 
    apply tshift_remN in H2. 
    subst. 
    apply wf_typ_impl_kinding in H as [? ?].
    eauto using kinding_remove_impl1.
  + simpl in *.
    destruct B as [B1 B2].
    destruct (IHe _ _ _ A B2) as [k C]. 
    exists k.
    now apply kinding_remove_impl1.
- simpl in *.
  apply get_typ_aux_unshift1 in A as [T' [C D]].
  pose proof (IHe _ _ _ C B) as [p E].
  subst.
  exists p.
  now apply insert_kind_kinding with (e:=e).
Qed.

(** Substituer un type dans un type préserve le kinding si les kinds de la
    variable de type et du substituant coïncident *)

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
      simpl; eauto. destruct (le_dec X0 X); try omega. simpl. eauto.
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

(*
env_subst_wf_typ :
wf_typ E1 E2
wf_env E1
env_subst X T E1 E2
wf_env E2
wf_typ E2 (tsubst T2 X T)

Lemma env_subst_wf_env : wf_env E1 
env_subst X T E1 E2
wf_env E2

Lemma env_subst_kinding env_subst X T1 E1 E2
kinding E1 T2 k
kinding E2 (tsubst T2 X T1) k.

Lemma env_subst_typing env_subst X T1 E1 E2
typing E1 t T2
typing E2 (subst_typ t X T1) T2
*)
