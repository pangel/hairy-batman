Require Export shift_lemmas.

(** * Lemmes utiles pour prouver [narrowing] *)

(** Les variables avec les noms suivants prennent le type correspondant par défaut : *)

Implicit Types 
(x y z X Y Z : nat)
(T U V : typ)
(n k p q : kind)
(t s u v : term)
(e f : env).

(** *** Donne le kind [p] à la [n]ième variable de type de [e] *)

Fixpoint replace_kind e n p := match e with
| nil => nil
| evar T :: e' => evar T :: replace_kind e' n p
| etvar q :: e' => match n with
  | 0 => etvar p :: e'
  | S n' => etvar q :: replace_kind e' n' p
  end
end.

(* *** [replace_kind] renvoie un ancien kind ou le kind de remplacement *)

Lemma replace_choice e n p q m :
  get_kind e n = Some p -> get_kind (replace_kind e n q) m = if eq_nat_dec n m then Some q else get_kind e m.
Proof.
  destruct (eq_nat_dec n m).
  - rewrite e0.
    clear e0.
    revert m.
    induction e; try induction a.
    + simpl. auto.
    + simpl. auto.
    + induction m.
      * simpl. auto.
      * simpl. intuition.
  - revert n0.
    revert n m.
    induction e; try induction a.
    + simpl. auto.
    + simpl. auto.
    + intros.
      induction n0; induction m; try omega; try tauto.
      simpl. 
      intuition.
Qed.

(* *** [replace_kind] préserves la well-formedness *)

Lemma replace_consistency e n x p q k:
  get_kind e n = Some p -> get_kind (replace_kind e x k) n = if eq_nat_dec x n then Some k else Some p.
Proof.
  revert n x.
  induction e; try induction a.
  - simpl in *. auto. 
  - simpl in *. auto. 
  - intros.
    induction n0.
    + induction x; tauto.
    + destruct (eq_nat_dec x (S n0)).
      * rewrite e0. simpl. 
        simpl in H.
        apply replace_choice with (m := n0) (q := k) in H.
        destruct (eq_nat_dec n0 n0); tauto.
      * induction x; auto.
        simpl. simpl in H.
        specialize (IHe n0 x).
        apply IHe in H.
        destruct (eq_nat_dec x n0) eqn:?; auto.
        omega.
Qed.

Lemma get_kind_exists x : 
  forall e, (get_kind e x = None -> False) <-> exists p, get_kind e x = Some p.
Proof.
  intros. split; destruct (get_kind e x).
  - exists k. auto.
  - tauto.
  - auto. 
  - intuition. 
    destruct H. 
    auto.
Qed.

Lemma replace_kind_preserves_wf_typ e T n p : 
  wf_typ e T -> wf_typ (replace_kind e n p) T.
Proof.
  revert e n.
  induction T.
  - intros.
    simpl in *.
    apply get_kind_exists in H. 
    destruct H.
    apply get_kind_exists.
    apply replace_consistency with (k := p) (x := n) in H.
    + destruct (eq_nat_dec n x).
      * exists p. auto.
      * exists x0. auto.
    + auto.
  - intros. simpl in *. intuition.
  - intros.
    specialize (IHT (etvar n :: e) (S n0)). 
    simpl in *. 
    auto.
Qed.

(** ** Lemmes directement utilisés par [narrowing] *)

(** *** [replace_kind] n'a pas d'effet sur les types *)

Lemma replace_kind_noop e x n p : get_typ e x = get_typ (replace_kind e n p) x.
Proof.
  revert x n.
  induction e; try induction a.
  - simpl. auto.
  - induction x; 
    simpl; 
    auto.
  - induction n0; 
    simpl;
    auto.
    specialize (IHe x n0).
    rewrite IHe.
    auto.
Qed.

(** *** [replace_kind] n'a pas d'effet sur les environnements *)

Lemma replace_kind_preserves_wf_env e n p : 
  wf_env e -> wf_env (replace_kind e n p).
Proof.
  revert n.
  induction e; try induction a.
  - simpl; auto.
  - simpl.
    intros.
    destruct H.
    split; auto.
    apply replace_kind_preserves_wf_typ.
    auto.
  - induction n0; auto.
    simpl.
    auto.
Qed.

(* *** [replace_kind] préserve le kinding si le kind de remplacement est plus petit *)

Lemma replace_kind_preserves_kinding e U n p q k : 
  get_kind e n = Some p -> q <= p -> kinding e U k -> kinding (replace_kind e n q) U k.
Proof.
intros.
revert H H0.
revert n p q.
induction H1; intros.
- apply replace_kind_preserves_wf_env with (n:=n) (p:=q0) in H1.
  pose proof (@replace_choice e n p0 q0 X H2).
  destruct (eq_nat_dec n X).
  + subst.
    replace p with p0 in * by congruence.
    eauto.
  + rewrite H in H4. 
    eauto. 
- eauto.
- econstructor.
  now eapply (IHkinding (S n) p0 q0).
Qed.
