Require Import lemmas_narrowing.

(* Les variables avec les noms suivants prennent le type correspondant par défaut *)

Implicit Types 
(x y z X Y Z : nat)
(T U V : typ)
(n k p q : kind)
(t s u v : term)
(e f : env).

Lemma narrowing e t T : 
  forall n p q,
  get_kind e n = Some p -> 
  typing e t T -> 
  q <= p -> 
  typing (replace_kind e n q) t T.
Proof.
  intros H p q H1.
  induction H; econstructor; eauto.
  - now rewrite <- replace_kind_noop.
  - now apply replace_kind_preserves_wf_env.
  - now apply (IHtyping (S n)).
  - eapply replace_kind_preserves_kinding; eauto.
Qed.
