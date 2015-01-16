(*Indentation : 2 espaces *)

(* On n'a pas à écrire les arguments inférables *)
Global Set Implicit Arguments. 
Global Unset Strict Implicit.

Require Import List Arith.

Definition kind := nat.

Inductive typ := 
| tvar (x:nat) 
| arrow (T:typ) (S:typ) 
| all (n:kind) (T:typ).

Inductive term := 
| var (x:nat) 
| abs (T:typ) (t:term) 
| app (t:term) (u:term) 
| tabs (n:kind) (t:term) 
| tapp (t:term) (T:typ).

(* On pourrait aussi définir un type list-like avec 3 constructeurs *)
Inductive envElem :=
| evar (T:typ)
| etvar (n:kind).

Definition env := list envElem.



(* Les variables avec les noms suivants prennent le type correspondant par défaut *)
Implicit Types 
(x y z X Y Z : nat)
(T U V : typ)
(n k p q : kind)
(t s u v : term)
(e f : env).

(* TODO *)
SearchAbout nat.
Fixpoint shift T (m : nat) (p : nat) := 
  match T with
    | tvar n => if (leb p n) then (tvar (n+m)) else (tvar (n))
    | arrow A B => arrow (shift A m p) (shift B m p)
    | all k u => all (k) (shift u m (p+1))
  end
.

Definition Tex := all (0) (arrow (tvar (1)) (tvar(2))).

Fixpoint tsubstaux T (n : nat) V (prof : nat) := 
  match T with
    | tvar m => 
      (
        if (beq_nat m n) then (
          shift V prof 0
        ) else (
          tvar m
        )
        )
     | arrow A B => arrow (tsubstaux A n V prof) (tsubstaux B n V prof)
     | all k u => all k (tsubstaux u (n+1) V (prof+1))
   end.

Definition tsubst T U X :=
tsubstaux T X U 0
.

(*Compute tsubst Tex (all (0) (tvar 1)) 1.
Compute shift (all (0) (tvar 0)) 1 0.*)
Fixpoint subst_type t T X :=
  match t with
    | var x => var x
    | abs U s => abs (tsubst U T X) (subst_type s T X)
    | app s u => app (subst_type s T X) (subst_type u T X) 
    | tabs n t => tabs n (subst_type t T (X+1))
    | tapp s U => app (subst_type s T X) (tsubst U T X)

  end.

Definition subst t u x :=
  t.

Definition get_kind e (n:nat) : (option kind) := None.
Definition get_typ e (n:nat) : (option typ) := None.

Fixpoint wf_typ e T {struct T} : Prop :=
match T with
| tvar X => get_kind e X = None -> False
| arrow U V => wf_typ e U /\ wf_typ e V
| all p U => wf_typ ((etvar p)::e) U
end.

Fixpoint wf_env e : Prop :=
match e with
| nil => True
| (evar T)::e' => wf_typ e T /\ wf_env e'
| (etvar p)::e' => wf_env e'
end.

(* Ou alors avec un Fixpoint ? On verra ce qui est plus pratique *)
Inductive kinding e : typ -> kind -> Prop :=
| kvar X p q : get_kind e X = Some p -> p <= q -> wf_env e -> kinding e (tvar X) q
| karrow T U p q : kinding e T q -> kinding e U q -> kinding e (arrow T U) (max p q)
| kall T p q : kinding ((etvar q)::e) T q -> kinding e (all q T) ((max p q) + 1).

Inductive typing e : term -> typ -> Prop :=
| rvar x T : get_typ e x = Some T -> wf_env e -> typing e (var x) T
| rabs t T U : typing ((evar T)::e) t U -> typing e (abs T t) (arrow T U)
| rapp t u T U : typing e t (arrow T U) -> typing e u T -> typing e (app t u) U
| rtabs t T p : typing ((etvar p)::e) t T -> typing e (tabs p t) (all p T)
| rtapp t T U p : typing e t (all p T) -> kinding e U p -> typing e (subst_type t U 1) (tsubst T U 1).

(* TODO *)
Lemma cumulativity : forall e T p q, kinding e T p -> p <= q -> kinding e T q.
Proof.
  admit.
Qed.

Inductive insert_kind : kind -> env -> env -> Prop :=
| inil e p : insert_kind 0 e ((etvar p)::e)
| icons n d e e' : insert_kind n e e' -> insert_kind (S n) (d::e) (d::e') .

(* 1.3.1.2 : Show that well-formedness, kinding and typing are invariant
   by weakening by a kind declaration. e.g. *)

(* TODO *)
Lemma insert_kind_wf_env X e e' : 
  insert_kind X e e' -> wf_env e -> wf_env e'.
Proof.
  admit.
Qed.

(* TODO *)
Lemma insert_kind_typing X e e' T p: 
  insert_kind X e e' -> kinding e T p -> kinding e' T p.
Proof.
  admit.
Qed.

(* TODO *)
Lemma insert_kind_kinding X e e' t T : 
  insert_kind X e e' -> typing e t T -> typing e' t T.
Proof.
  admit.
Qed.

(* TODO *)
Definition subst_env T x d := 
  d.

Inductive env_subst p T : env -> env -> Prop :=
| snil e : env_subst p T ((etvar p)::e) (map (subst_env T p) e)
| scons e e' d : env_subst p T e e' -> env_subst p T (d::e) (d::e').

Fixpoint remove_var e x := match e with
| nil => nil
| d::e' => match x with
  | 0 => e'
  | S y => d::(remove_var e' y)
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
Lemma subst_preserves_typing :
  forall e x t u T U,
  typing e t T ->
  typing (remove_var e x) u U -> get_typ e x = Some U ->
  typing (remove_var e x) (subst t u x) T.
Proof.
  admit.
Qed.

(* TODO *)
Lemma typing_weakening_var_ind :
  forall e x t T,
  wf_env e -> typing (remove_var e x) t T -> typing e (shift x t) T.

(* TODO *)
Lemma regularity e t T : exists p, kinding e T p.

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

Definition red t u := match t with
| tapp (tabs p t') T => u = subst_type t' T 0
| app (abs T t') t'' => subst t' t'' 0 = u
| 
end.
