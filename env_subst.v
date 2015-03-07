Require Import lemmas_regularity.

(** Les variables avec les noms suivants prennent le type correspondant par défaut : *)

Implicit Types 
(x y z X Y Z : nat)
(T U V : typ)
(n k p q : kind)
(t s u v : term)
(e f : env).

Inductive env_subst T : nat -> env -> env -> Prop :=
| snil e k : env_subst T 0 ((etvar k)::e) e
| styp n e e' U : env_subst T n e e' -> env_subst T n (evar T :: e) (evar (tsubst U T n) :: e')
| skind n e e' k : env_subst T n e e' -> env_subst T (S n) (etvar k :: e) (etvar k :: e').

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

Lemma env_subst_kinding E1 E2 T1 T2 X T k : 
  env_subst T1 X E1 E2 ->
  kinding E1 T2 k ->
  kinding E2 (tsubst T2 T1 X) k.
Proof.
  admit.
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
