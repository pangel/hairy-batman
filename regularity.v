Require Import lemmas_regularity.

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
    apply typing_implies_wf_env in H.
    destruct H.
    apply (wf_implies_kinding H0) in H as [q H].
    apply remove_var_preserves_kinding with (x:=0) in A. 
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
