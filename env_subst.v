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

Lemma env_subst_wf_typ E1 E2 X T T2 :
  wf_typ E1 T2 ->
  wf_env E1 ->
  env_subst T X E1 E2 ->
  wf_env E2 ->
  wf_typ E2 (tsubst T2 T X).
Proof.
  admit.
Qed.

Lemma env_subst_wf_env E1 E2 X T : 
  wf_env E1 ->
  env_subst T X E1 E2 ->
  wf_env E2.
Proof.
  admit.
Qed.


Lemma env_subst_kinds_substituee U X e e' : 
  env_subst U X e e' -> wf_env e -> forall p, get_kind e X = Some p -> kinding e' U p.
Proof.
  induction 1; intros B p A.
  - now inv A.
  - destruct B as [B B'].
    eapply remove_var_implies_kinding with (x:=0); auto.
    pose proof (env_subst_wf_env B' H). 
    split; eauto using env_subst_wf_typ.
  - apply insert_kind_kinding with (e:=e'); auto.
Qed.

Lemma env_subst_kinding e e' T U X k : 
  env_subst U X e e' ->
  kinding e T k ->
  kinding e' (tsubst T U X) k.
Proof.
  intros.
  pose proof (env_subst_wf_env (kinding_implies_wf_env H0) H).
  revert H1 H. revert e' U X. dependent induction H0; intros.
  - simpl.
    repeat destruct_match.
    + destruct X; [ omega| ].
      clear Heqs Heqs0.
      { revert l l0 H0 H. revert X. induction H3; intros.
      - econstructor ; eauto.
      - eapply remove_var_implies_kinding with (e:=(_::e')) (x:=0); auto.
        eapply IHenv_subst; firstorder.
      - simpl in *.
        destruct X ; [omega|].
        replace (tvar (S X)) with (tshift (tvar X) 1 0) by auto.
        eapply insert_kind_kinding with (e:=e'); eauto.
        eapply IHenv_subst; firstorder. }
    + subst.
        eauto using env_subst_kinds_substituee.
    + destruct X0; [omega|].
       clear Heqs.
      { revert n H H0. revert X. induction H3; intros.
      - omega.
      - eapply remove_var_implies_kinding with (e:=(_::e')) (x:=0); auto.
        eapply IHenv_subst; firstorder.
      - simpl in *.
        destruct X.
        + inv H. econstructor; firstorder.
        + replace (tvar (S X)) with (tshift (tvar X) 1 0) by auto.
          eapply insert_kind_kinding with (e:=e'); eauto. }
  - simpl; econstructor; eauto.
  - simpl; econstructor.
    eapply IHkinding; auto.
    now constructor.
Qed.

Theorem env_subst_typing E1 E2 T1 T2 t X : 
  env_subst T1 X E1 E2 ->
  typing E1 t T2 ->
  typing E2 (subst_type t T1 X) T2.
Proof.
  admit.
Qed.


(* ??? *
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
