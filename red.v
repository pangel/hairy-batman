Require Import init .

Implicit Types 
(x y z X Y Z : nat)
(T U V : typ)
(n k p q : kind)
(t s u v : term)
(e f : env).


Inductive red_step : term -> term -> Prop :=
| red_typ p t T : red_step (tapp (tabs p t) T) (subst_type t T 0)
| red_term t u T : red_step (app (abs T t) u) ((subst t u) 0)
| red_abs t u T : red_step t u -> red_step (abs T t) (abs T u)
| red_appl t u v : red_step t u -> red_step (app t v) (app u v)
| red_appr t u v : red_step u v -> red_step (app t u) (app t v)
| red_tabs t u k : red_step t u -> red_step (tabs k t) (tabs k u)
| red_tapp t u T : red_step t u -> red_step (tapp t T) (tapp u T). 

Definition red := clos_trans term red_step.
Hint Constructors red_step.
Hint Extern 3 => (match goal with |- red _ _=> econstructor end).

Lemma red_congruent t u : red t u -> 
(  (forall T, red (abs T t) (abs T u))
/\ (forall v, red (app t v) (app u v))
/\ (forall v, red (app v t) (app v u))
/\ (forall k, red (tabs k t) (tabs k u))
/\ (forall T, red (tapp t T) (tapp u T))).
Proof.
  repeat split ; induction H ; intros ; eauto.
  - eapply t_trans with (y := abs T y) ; firstorder.
  - eapply t_trans with (y := app y v) ; firstorder.
  - eapply t_trans with (y := app v y) ; firstorder.
  - eapply t_trans with (y := tabs k y) ; firstorder.
  - eapply t_trans with (y := tapp y T) ; firstorder.
Qed.

(* Bizarre. Il faut 2 variantes de neutral et les prédicats
   ne sont pas mutuellement inductifs *)
Inductive normal : term -> Prop :=
| nvar x : normal (var x)
| nabs T t : normal t -> normal (abs T t)
| napp t u : normal t -> normal u -> neutral t -> normal (app t u)
| ntabs k t : normal t -> normal (tabs k t)
| ntapp t T : normal t -> neutralT t -> normal (tapp t T)

with neutral : term -> Prop :=
| neutral_var x : neutral (var x)
| neutral_app t u : neutral (app t u)
| neutral_tabs k t : neutral (tabs k t)
| neutral_tapp t T : neutral (tapp t T)

with neutralT : term -> Prop :=
| neutralT_var x : neutralT (var x)
| neutralT_app t u : neutralT (app t u)
| neutralT_abs T t : neutralT (abs T t)
| neutralT_tapp t T : neutralT (tapp t T).

Theorem normal_neutral_preserved_typ_subst t T X :
   (normal t -> normal (subst_type t T X)) 
/\ (neutral t -> neutral (subst_type t T X)) 
/\ (neutralT t -> neutralT (subst_type t T X)).
Proof.
  revert T X.
  induction t.
  - intros.
    repeat split; intros ; simpl ; assumption.
  - intros.
    repeat split ; intros ; inversion H ; econstructor ; apply IHt ; assumption.
  - intros.
    repeat split.
    + intros.
      simpl.
      inversion H.
      econstructor.
      * apply IHt1 ; auto.
      * apply IHt2 ; auto.
      * apply IHt1 ; auto.
    + intros.
      simpl.
      inversion H.
      econstructor.
    + intros.
      simpl.
      inversion H.
      econstructor.
  - intros.
    repeat split.
    + intros.
      inversion H.
      simpl.
      econstructor.
      apply IHt;auto.
    + intros.
      inversion H.
      simpl.
      econstructor.
    + intros.
      inversion H.
  - intros.
    repeat split.
    + intros.
      simpl.
      inversion H.
      econstructor.
      * apply IHt ; auto.
      * apply IHt ; auto.
    +  intros.
      simpl.
      inversion H.
      econstructor.
    +  intros.
      simpl.
      inversion H.
      econstructor.
Qed.

Theorem normal_is_really_normal : forall u,  normal u <-> (forall v , red u v -> False).
intros.
induction u.
- split.
  + intros.
    revert H.
    dependent induction H0.
    *  intros. inversion H.
    *  intros. apply IHclos_trans1. assumption.
  + intros.
    econstructor.
- split.
  + intros.
    dependent induction H0.
    * { intros. inversion H0. subst. inversion H.
        inversion IHu.
        assert (forall v, red u v -> False).
        - apply H5.
          assumption.
        - specialize (H7 u0).
          apply H7.
          econstructor.
          apply H4.
      }
    * apply IHclos_trans1 ; assumption.
  + intros.
    econstructor.
    apply IHu.
    intros.
    specialize (H (abs T v)).
    apply H.
    apply red_congruent.
    assumption.
- split.
  + intros.
    inversion H.
    dependent induction H0.
    * { 
      - inversion H0.
        + inversion H5 ;rewrite <- H9 in H7; discriminate.
        + assert ( (forall v, red u1 v -> False)).
          * apply IHu1 ; auto.
          * specialize (H10 u0).
            apply H10.
            econstructor.
            apply H9.
        + assert ( (forall v, red u2 v -> False)).
          * apply IHu2 ; auto.
          * specialize (H10 v).
            apply H10.
            econstructor.
            apply H9.
      }
    * apply (IHclos_trans1 IHu2 IHu1 H u1 u2 H3 H4 H5) ;auto.
  + intros.
    econstructor.
    * apply IHu1.
      intros.
      specialize (H (app v u2)).
      apply H.
      apply red_congruent.
      assumption.
    * apply IHu2.
      intros.
      specialize (H (app u1 v)).
      apply H.
      apply red_congruent.
      assumption.
    * destruct u1; try econstructor.
      intros.
      exfalso.
      specialize (H (subst u1 u2 0)).
      apply H.
      econstructor.
      econstructor.
- split.
  + intros.
    inversion H.
    dependent induction H0.
    * inversion H0.
      subst.
      inversion IHu.
      specialize (H1 H2 u0).
      apply H1.
      econstructor.
      apply H7.
   * apply (IHclos_trans1 IHu H n u) ;auto.
  + intros.
    econstructor.
    apply IHu.
    intros.
    specialize (H (tabs n v)).
    apply H.
    apply red_congruent. auto.
- split.
  + intros.
    inversion H.
    dependent induction H0.
    * { inversion IHu.
        inversion H0.
        - subst.
          inversion H4.
        - subst. 
          specialize (H5 H3 u0).
          apply H5.
          econstructor.
          auto.
      }
    * apply (IHclos_trans1 IHu H u T H3 H4) ; auto.
  + intros.
    econstructor.
    * apply IHu.
      intros.
      specialize (H (tapp v T)).
      apply H.
      apply red_congruent. auto.
    * destruct u; try econstructor.
      exfalso.
      specialize (H (subst_type u T 0)). 
      apply H.
      econstructor.
      econstructor.
Qed.

Theorem big_step_congruent :
   (forall T t u, red t u -> red (abs T t) (abs T u)) 
/\ (forall u t v, red t v -> red (app u t) (app u v)) 
/\ (forall u t v, red t v -> red (app t u) (app v u)) 
/\ (forall k t u, red t u -> red (tabs k t) (tabs k u)) 
/\ (forall T t u, red t u -> red (tapp t T) (tapp u T)).
Proof.
repeat split ; intros a b c H ; induction H.
- do 2 econstructor ; auto.
- apply t_trans with (y := abs a y).
  + apply IHclos_trans1.
  + apply IHclos_trans2.
- do 2 econstructor ; auto.
- apply t_trans with (y := app a y).
  + apply IHclos_trans1.
  + apply IHclos_trans2.
- do 2 econstructor ; auto.
- apply t_trans with (y := app y a).
  + apply IHclos_trans1.
  + apply IHclos_trans2.
- do 2 econstructor ; auto.
- apply t_trans with (y := tabs a y).
  + apply IHclos_trans1.
  + apply IHclos_trans2.
- do 2 econstructor ; auto.
- apply t_trans with (y := tapp y a).
  + apply IHclos_trans1.
  + apply IHclos_trans2.
Qed.
