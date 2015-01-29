Require Import reg_nar_lemmas.

(* Les variables avec les noms suivants prennent le type correspondant par défaut *)
Implicit Types 
(x y z X Y Z : nat)
(T U V : typ)
(n k p q : kind)
(t s u v : term)
(e f : env).

Lemma regularity e t T : typing e t T -> exists p, kinding e T p.
Proof.
  intros.
  induction H.
  - setoid_rewrite <- tshift_ident with (p:=0).
    setoid_rewrite <- tshift_ident with (p:=0) in H. 
    eapply get_typ_kinding_general with (m:=0); eauto.
  - destruct IHtyping as [p A].
    apply typing_impl_wf_env in H.
    destruct H.
    apply wf_typ_impl_kinding in H as [q H].
    apply kinding_remove with (x:=0) in A. 
    eauto.
  - destruct IHtyping1 as [p A].
    inv A.
    eauto.
  - destruct IHtyping as [q A].
    eauto.
  - destruct IHtyping as [q A].
    inv A.
    exists p0.
    eapply tsubst_preserves_kinding with (e':=etvar p::e) (kU:=p); eauto.
Qed.

(*
Lemma kind_well_formed : forall e T x, get_typ_aux e x 0 = Some T -> wf_env e -> wf_typ e T.
Proof.
intros e T x.
revert e T.
induction x.
- intros.
  destruct e.
  + inversion H.
  + destruct e.
    * { simpl in *.
        inversion H.
        replace (tshift T0 0 0) with (T0).
        - apply H0.
        - symmetry. apply tshift_ident.
      }
    * simpl in *.
      
- intros.
  destruct a.
  + refine (IHe T ).
*)


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
Lemma narrowing e t T : 
  forall n p q,
  get_kind e n = Some p -> 
  typing e t T -> 
  q <= p -> 
  typing (replace_var e n q) t T.
Proof.
admit.
Qed.

