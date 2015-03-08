Require Import lemmas_regularity.

(** Les variables avec les noms suivants prennent le type correspondant par défaut : *)

Implicit Types 
(x y z X Y Z : nat)
(T U V : typ)
(n k p q : kind)
(t s u v : term)
(e f : env).

Inductive env_subst : typ -> nat -> env -> env -> Prop :=
| snil T e k : kinding e T k -> env_subst T 0 ((etvar k)::e) e
| styp T n e e' U : env_subst T n e e' -> env_subst T n (evar U :: e) (evar (tsubst U T n) :: e')
| skind T n e e' k : env_subst T n e e' -> env_subst (tshift T 1 0) (S n) (etvar k :: e) (etvar k :: e').
Hint Constructors env_subst.

Lemma env_subst_less e e' x T:
  env_subst T x e e' -> forall y, y < x -> get_kind e y = get_kind e' y.
Proof.
  induction 1; intros; simpl in *.
  - omega.
  - auto.
  - destruct y; firstorder.
Qed.

Lemma env_subst_more e e' x T :
  env_subst T x e e' -> forall y, y >= x -> get_kind e (S y) = get_kind e' y.
Proof.
  induction 1; intros; simpl in *.
  - trivial.
  - auto.
  - destruct y; firstorder. 
Qed.

Lemma env_subst_wf_substitutee e : forall e' U X, env_subst U X e e' -> wf_typ e' U.
Proof.
induction 1; intros; simpl in *.
- apply (kinding_implies_wf_typ H).
- now eapply remove_var_implies_wf_typ with (x:=0). 
- now eapply insert_kind_wf_typ with e'.
Qed.

Lemma env_subst_wf_typ e e' X T U :
  wf_typ e T ->
  env_subst U X e e' ->
  wf_typ e' (tsubst T U X).
Proof.
  revert e e' X U.
  induction T; intros; simpl in *.
  - simpl; repeat destruct_match.
    destruct x; try omega.
    simpl in *.
    + erewrite <- env_subst_more; eauto.
    + eapply env_subst_wf_substitutee; eauto.
    + erewrite <- env_subst_less; eauto.
  - destruct H; split; eauto.
  - eauto. 
Qed.

Lemma env_subst_wf_env e e' X T : 
  wf_env e ->
  env_subst T X e e' ->
  wf_env e'.
Proof.
  intros.
  induction H0.
  - auto.
  - simpl in *.
    destruct H.
    split; auto.
    apply env_subst_wf_typ with (e := e); auto.
  - simpl in *. auto. 
Qed.

Lemma env_subst_kinds_substituee U X e e' : 
  env_subst U X e e' -> wf_env e -> forall p, get_kind e X = Some p -> kinding e' U p.
Proof.
  induction 1; intros B p A.
  - now inv A.
  - eapply remove_var_implies_kinding with (x:=0); auto.
    + destruct B as [B B'].
      pose proof (env_subst_wf_env B' H).
      split; eauto using env_subst_wf_typ.
    + eapply IHenv_subst; firstorder.
  - apply insert_kind_kinding with (e:=e'); auto.
Qed.

Lemma env_subst_kinding e e' T U X k : 
  env_subst U X e e' ->
  kinding e T k ->
  kinding e' (tsubst T U X) k.
Proof.
  intros.
  pose proof (env_subst_wf_env (kinding_implies_wf_env H0) H).
  revert H1 H. revert e' U X. dependent induction H0; intros; simpl.
  - repeat destruct_match.
    + destruct X; [ omega| ].
      clear Heqs Heqs0. simpl.
      econstructor; eauto. 
      erewrite <- env_subst_more; eauto. 
      omega.
    + subst.
      eauto using env_subst_kinds_substituee.
    + destruct X0; [omega|].
      clear Heqs.
      econstructor; eauto.
      erewrite <- env_subst_less; eauto.
      omega.
  - econstructor; eauto.
  - econstructor.
    eapply IHkinding; auto.
Qed.

Lemma env_subst_var U X e e' : 
  env_subst U X e e' -> forall x T, get_typ e x = Some T -> get_typ e' x = Some (tsubst T U X).
Proof.
  induction 1; intros; simpl in *.
  - destruct (get_typ e x) eqn:K; [|discriminate].
    inv H0.
    f_equal.    
    apply tsubst_tshift_ident.
  - destruct x; auto.
  - destruct (get_typ e x) as [U|] eqn:K; [|discriminate]. 
    erewrite IHenv_subst with (T0:=U); auto.
    f_equal.
    inv H0.
    pose proof (tsubst_tshift_swapUp U 0 0 1 n T). 
    rewrite tshift_ident in H0.
    now symmetry.
Qed.

Theorem env_subst_typing e e' U T t X : 
  env_subst U X e e' ->
  typing e t T ->
  typing e' (subst_type t U X) (tsubst T U X).
Proof.
  intros.
  revert H. revert X e' U.
  induction H0; intros.
  - constructor.
    + eapply env_subst_var; eauto.
    + eapply env_subst_wf_env; eauto.
  - constructor. eapply IHtyping.
    + econstructor. eauto.
  - econstructor; eauto.
  - eapply skind with (k:=p) in H. 
    simpl. econstructor.
    eapply (IHtyping _ _ _ H).
  - simpl.
    rewrite tsubst_commut.
    eapply rtapp with (p:=p).
    + apply IHtyping in H1. 
      simpl in *. auto.
    + eapply env_subst_kinding; eauto. 
Qed.
