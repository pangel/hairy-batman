Require Export init.

(* Les variables avec les noms suivants prennent le type correspondant par défaut *)
Implicit Types 
(x y z X Y Z : nat)
(T U V : typ)
(n k p q : kind)
(t s u v : term)
(e f : env).

Inductive insert_kind : nat -> env -> env -> Prop :=
| inil e p : insert_kind 0 e ((etvar p)::e)
| iskip n T e e' : insert_kind n e e' -> insert_kind n ((evar T)::e) ((evar (tshift T 1 n))::e')
| icons n p e e' : insert_kind n e e' -> insert_kind (S n) ((etvar p)::e) ((etvar p)::e').
Hint Constructors insert_kind.

Lemma get_kind_insert_some e e' X Y p :
  insert_kind X e e' -> get_kind e Y = Some p -> get_kind e' (shift_var Y 1 X) = Some p.
Proof.
  intros D E.
  revert E. revert Y.
  induction D as [e p'| | ]; intros Y E.
  - simpl. auto.
  - simpl in *.
    auto.
  - simpl in *.
    destruct Y.
    + destruct (le_dec (S n) 0); [omega|auto].
    + specialize (IHD Y E).
      destruct (le_dec n Y);
      destruct (le_dec (S n) (S Y));
      auto; omega.
Qed.

Lemma get_kind_insert_none e e' X Y : 
  insert_kind X e e' -> get_kind e' (shift_var Y 1 X) = None -> get_kind e Y = None.
Proof.
  intros A B.
  destruct (get_kind e Y) as [k|] eqn:K.
  - apply (get_kind_insert_some A) in K.
    congruence.
  - reflexivity.
Qed.

Lemma insert_kind_wf_typ n e e' T : insert_kind n e e' -> wf_typ e T -> wf_typ e' (tshift T 1 n).
Proof.
  revert n e e'.
  induction T;
  intros n' e e' A B;
  simpl in *.
  - contradict B.
    apply (get_kind_insert_none A B).
  - destruct B as [B C]. 
    split; eauto.
  - refine (IHT (1+n') (etvar n::e) _ _ _).
    + apply (icons _ A).
    + assumption.
Qed.

Lemma insert_kind_wf_env X e e' : 
  insert_kind X e e' -> wf_env e -> wf_env e'.
Proof.
  induction 1; simpl; auto.
  intros [D E].
  split; auto.
  now apply insert_kind_wf_typ with (n:=n) (e:=e).
Qed.

Lemma insert_kind_kinding X e e' T p: 
  insert_kind X e e' -> kinding e T p -> kinding e' (tshift T 1 X) p.
Proof.
  revert p X e e'.
  induction T; intros p X e e' D E.
  - inversion E. subst.
    refine (kvar _ H1 _).
    + eapply get_kind_insert_some; eauto. 
    + eapply insert_kind_wf_env; eauto. 
  - inversion E. subst.
    simpl.
    refine (karrow _ _); eauto.
  - apply (icons n) in D.
    inversion E. subst.
    refine (kall _).
    eapply IHT; eauto.
Qed.

Lemma tshift_ident : forall T p , tshift T 0 p = T.
Proof.
  induction T.
  - intros.
    unfold tshift.
    unfold shift_var.
    destruct (le_dec p x) as []eqn:?.
    + replace (0+x) with (x).
      * reflexivity.
      * omega.
    + reflexivity.
  - intros.
    simpl.
    replace (tshift T1 0 p) with T1.
    + replace (tshift T2 0 p) with T2.
      * reflexivity.
      * symmetry.
        apply (IHT2 p).
    + symmetry.
      apply (IHT1 p).
  - intros.
    simpl.
    replace (tshift T 0 (S p)) with T.
    + reflexivity.
    + symmetry.
      apply (IHT (S p)).
Qed.

Hint Extern 1 => 
match goal with
| |- context [le_dec ?a ?b] => destruct (le_dec a b); try omega
| |- context [eq_nat_dec ?a ?b] => destruct (eq_nat_dec a b); try omega
| H : context [le_dec ?a ?b] |- _ => destruct (le_dec a b); try omega
end.

Lemma tshift_commut T :
  forall a c d (p : nat) , tshift (tshift T a p) c (d+p) = tshift (tshift T c (d-a+p)) a (p).
Proof.
induction T; intros a c d p; simpl in *.
- f_equal; eauto 7.
- f_equal; eauto.
- simpl. 
  replace (S (d+p)) with (d + (S p)) by omega.
  rewrite IHT with (p := (S p)). 
  do 3 f_equal. 
  omega.
Qed.

Lemma tshift_plus1_m T p : forall m, tshift T (S p) m = tshift (tshift T 1 m) p (m+1).
Proof.
induction T.
- intros.
  simpl in *.
  eauto.
- intros.
  simpl in *.
  rewrite IHT1.
  rewrite IHT2.
  auto.
- intros.
  simpl in *.
  rewrite IHT.
  f_equal.
Qed.

Lemma tshift_plus1 T p :  tshift T (S p) 0 = tshift (tshift T 1 0) p 0.
Proof.
transitivity (tshift (tshift T 1 0) p 1).
- apply tshift_plus1_m.
- transitivity (tshift (tshift T p 0) 1 0). 
  + apply (tshift_commut T 1 p 1 0) .
  + apply (tshift_commut T p 1 0 0) .
Qed.

Lemma tshift_plus1_conv T p :  tshift T (S p) 0 = tshift (tshift T p 0) 1 0.
Proof.
transitivity (tshift (tshift T 1 0) p 0).
- apply tshift_plus1.
- apply (tshift_commut T 1 p 0 0).
Qed.


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
          apply tshift_plus1_conv.
        }
      * { intros.
          eauto.
         }
    + simpl in *.
      intros.
      rewrite IHe with (T :=T) ; auto.
Qed.

Lemma get_typ_aux_1 e Y T : 
  get_typ_aux e Y 1 = Some T -> exists T', T = tshift T' 1 0 /\ get_typ_aux e Y 0 = Some T'.
admit.
Qed.

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

Lemma tshift_rem1 T U p k : tshift T (S p) 0 = tshift U (S k) 0 -> tshift T p 0 = tshift U k 0.
Proof.
intros.
refine (@tshift_inject _ _  0 _).
replace (tshift (tshift T p 0) 1 0) with (tshift T (S p) 0).
- replace (tshift (tshift U k 0) 1 0) with (tshift U (S k) 0).
  + apply H.
  + apply tshift_plus1_conv.
- apply tshift_plus1_conv.
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
    now rewrite <- tshift_plus1_conv.
Qed.

Arguments get_typ / _ _.
Compute (tshift (tsubst (tvar (1)) (tvar(0)) 0) 1 1).
Compute (tsubst (tshift (tvar 1) 1 1) (tshift (tvar(0)) 1 1) 0).

Ltac destruct_match :=
  match goal with
  | |- context[match ?a with _ => _ end] => destruct a; simpl in *; try destruct_match
  | H:context[match ?a with _ => _ end] |- _ => destruct a; simpl in *; try destruct_match
  end.

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

Lemma insert_kind_typing X e e' t T : 
  insert_kind X e e' -> typing e t T -> typing e' (tshift_in_term t 1 X) (tshift T 1 X).
Proof.
  intros.
  revert H. revert X e'.
  induction H0; intros.
  - simpl in *. 
(* with preshifted env : 
Lemma get_typ_aux e x 0 = Some T -> insert_kind X e e' -> get_typ_aux e' x 0 = tshift T 1 X
*)
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
Definition subst_env T x (d:envElem) := match d with
| (evar U) => evar (tsubst U T x)
| d => d
end.

Inductive env_subst p T : env -> env -> Prop :=
| snil e : env_subst p T ((etvar p)::e) (map (subst_env T p) e)
| scons e e' d : env_subst p T e e' -> env_subst p T (d::e) (d::e').

Fixpoint remove_var e x := match e with
| nil => nil
| (etvar k)::e' => (etvar k)::remove_var e' x
| (evar T)::e' => match x with
  | 0 => e'
  | S y => (evar T)::(remove_var e' y)
  end
end.

Fixpoint replace_var e n p := match e with
| nil => nil
| d::e' => match n with
  | 0 => match d with
    | etvar q => (etvar p)::e'
    | d => d::e'
    end
  | S n' => d::(replace_var e' n p)
  end
end.

(* TODO *)

Lemma rem_var_less x y T e : get_typ e y = Some T -> y < x -> get_typ (remove_var e x) y = Some T.
admit.
Qed.

Lemma rem_var_more x y T e : get_typ e y = Some T -> y > x -> get_typ (remove_var e x) (y-1) = Some T.
admit.
Qed.

Lemma remove_var_preserve_wf_env e x : wf_env e -> wf_env (remove_var e x).
admit.
Qed.

Lemma typing_weak1 e t T U : typing e t T -> typing ((evar U)::e) (shift t 1 0) T.
admit.
Qed.

Lemma get_typ_aux_shift1 e x Tu n : 
  get_typ_aux e x 0 = Some (tshift Tu n 0) -> get_typ_aux e x 1 = Some (tshift Tu (1+n) 0).
admit.
Qed.

Lemma kinding_remove e U p x : kinding e U p -> kinding (remove_var e x) U p.
admit.
Qed.

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

Lemma rem_var_more_conv e x y T : get_typ (remove_var e x) y = Some T -> x <= y -> get_typ e (S y) = Some T.
admit.
Qed.

Lemma rem_var_less_conv e x y T : get_typ (remove_var e x) y = Some T -> x > y -> get_typ e y = Some T.
admit.
Qed.

Lemma kinding_remove_impl e x U p : kinding (remove_var e x) U p -> kinding e U p.
admit.
Qed.

Lemma get_kind_remove_var_noop e : forall x y, get_kind e y = get_kind (remove_var e x) y.
Proof.
  induction e as [|[|]]; intros; simpl in *; auto; [destruct x | destruct y]; eauto.
Qed.

Lemma typing_impl_wf_env e t T : typing e t T -> wf_env e.
Proof.
  induction 1; simpl in *; auto; tauto.
Qed.

Lemma remove_var_preserves_wf_typ T : forall e x, wf_typ (remove_var e x) T -> wf_typ e T.
Proof.
  induction T as [y | | ]; intros e X A; simpl in *; intuition; eauto.
  contradict A.
  now rewrite <- get_kind_remove_var_noop.
Qed.

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

Lemma wf_typ_impl_kinding e T : wf_typ e T -> exists p, kinding e T p.
admit.
Qed.
   
Lemma kinding_remove_impl1 e U p T : kinding e U p -> kinding (evar T::e) U p.
Proof.
  replace e with (remove_var (evar T::e) 0) at 1 by auto.
  apply kinding_remove_impl.
Qed.


Lemma get_typ_aux_unshift1 e x T m: 
  get_typ_aux e x (S m) = Some (tshift T m 0) ->
  exists T', get_typ_aux e x m = Some (tshift T' m 0) /\ T = (tshift T' 1 0).
Proof.
admit.
Qed.

Lemma tshift_remN:
  forall T U m,
  tshift T m 0 = tshift U m 0 -> T = U.
Proof.
admit.
Qed.

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

Lemma insert_shiftl e e' Y X p : 
  insert_kind Y e e' -> Y < (S X) -> get_kind e' (S X) = Some p -> get_kind e X = Some p.
admit.
Qed.

Lemma insert_shiftr e e' Y X p :
  insert_kind Y e e' -> ~ Y <= X -> get_kind e' X = Some p -> get_kind e X = Some p.
admit.
Qed.

Lemma insert_kind_wf_env_conv X e e' :
  insert_kind X e e' -> wf_env e' -> wf_env e.
admit.
Qed.

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
      replace (S X - 1) with X by omega.
      assert (get_kind e0 X = Some p) by eauto using insert_shiftl.
      eauto.
    * subst. 
      assert (p = kU) by congruence. 
      subst.
      eauto.
  + assert (get_kind e0 X = Some p) by eauto using insert_shiftr.
    eauto.
- simpl in *. eauto.
- simpl in *.
  constructor.
  apply (IHC (etvar q::e0) (S X0) (tshift U' 1 0) kU (icons _ A) B (insert_kind_kinding (inil e0 q) C')).
Qed.

