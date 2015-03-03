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
admit.
Qed.
