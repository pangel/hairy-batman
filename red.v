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

with neutralT : term -> Prop :=
| neutralT_var x : neutralT (var x)
| neutralT_app t u : neutralT (app t u)
| neutralT_abs T t : neutralT (abs T t).

Lemma normal_neutral_preserved_typ_subst t T X :
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
    +  intros.
      simpl.
      inversion H.
Qed.
