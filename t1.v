(*Indentation : 2 espaces *)

(* On n'a pas à écrire les arguments inférables *)
Global Set Implicit Arguments. 
Global Unset Strict Implicit.

Require Import List Arith Relations.

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

Fixpoint eq_typ_dec T U : sumbool (T = U) (T <> U).
Proof.
  repeat decide equality.
Qed.

(* Awesome :'(
Coercion tvar : nat >-> typ.
Coercion var : nat >-> term.
*)

(* TODO *)

Definition shift_var n floor inc :=
  if (le_dec floor n) then inc+n else n.
Arguments shift_var / _ _ _.

Fixpoint tshift T (m : nat) (p : nat) := 
  match T with
    | tvar n => tvar (shift_var n p m)
    | arrow A B => arrow (tshift A m p) (tshift B m p)
    | all k u => all (k) (tshift u m (1+p))
  end
.

Definition Tex := all (0) (arrow (tvar (1)) (tvar(2))).

Fixpoint tsubstaux T (n : nat) V (prof : nat) := 
  match T with
    | tvar m => 
      (
        if (eq_nat_dec m n) then (
          tshift V prof 0
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
    | tapp s U => tapp (subst_type s T X) (tsubst U T X)
  end.

Fixpoint shift t (m : nat) (p : nat) := 
  match t with
    | var n => var (shift_var n p m)
    | abs T s =>  abs T (shift s m (p+1))
    | app s u => app (shift s m p) (shift u m p) 
    | tabs n s => tabs n (shift s m p) 
    | tapp s T => tapp (shift s m p) T
   end
.
Fixpoint substaux t x u prof :=
  match t with
    |var n => if (eq_nat_dec x n) then 
      (
        shift u prof 0
      ) else (
        var n
      )
      | abs T s => abs T (substaux s (x+1) u (prof +1))
      | app s h => app (substaux s x u prof) (substaux s x u prof)
      | tabs n s => tabs n (substaux s x u prof)
      | tapp s T => tapp (substaux s x u prof) T
  end.

Definition subst t u x :=
  substaux t x u 0.

Fixpoint get_kind e (n:nat) : (option kind) := 
  match e with
    |(etvar m)::e' => match n with 0 => Some m | S n => get_kind e' n end
    |(evar T)::e' => get_kind (e') n
    |nil => None
  end
.

Fixpoint get_typ_aux e (n: nat) (m : nat) : (option typ) :=
  match e with
    |(etvar m)::e' => get_typ_aux (e') n (1+m)
    |(evar T)::e' => match n with 0 => Some (tshift T m 0) | S n => get_typ_aux (e') n m end
    |nil => None
  end
.

Fixpoint get_typ e (n:nat) : (option typ) :=
 get_typ_aux e n 0
.

Require Import Bool.

Fixpoint wf_typ e T {struct T} : Prop :=
match T with
| tvar X => get_kind e X = None -> False
| arrow U V => wf_typ e U /\ wf_typ e V
| all p U => wf_typ ((etvar p)::e) U
end.

Lemma wf_typ_dec e T : { wf_typ e T } + { wf_typ e T -> False }.
Proof.
  revert e.
  induction T; intro e; simpl.
  - destruct (get_kind e x) eqn:K.
    + left. discriminate.
    + right. auto.
  - destruct (IHT1 e); destruct (IHT2 e); tauto.
  - destruct (IHT (etvar n :: e)); tauto.
Qed.

Fixpoint wf_env e : Prop :=
match e with
| nil => True
| (evar T)::e' => wf_typ e T /\ wf_env e'
| (etvar p)::e' => wf_env e'
end.

Lemma wf_env_dec e : { wf_env e } + { wf_env e -> False }.
Proof. 
  induction e as [|[U|p]]; simpl; auto.
  destruct (wf_typ_dec (evar U :: e) U); tauto.
Qed.

(* Ou alors avec un Fixpoint ? On verra ce qui est plus pratique *)
Inductive kinding e : typ -> kind -> Prop :=
| kvar X p q : get_kind e X = Some p -> p <= q -> wf_env e -> kinding e (tvar X) q
| karrow T U p q : kinding e T p -> kinding e U q -> kinding e (arrow T U) (max p q)
| kall T p q : kinding ((etvar q)::e) T p -> kinding e (all q T) (1 + (max p q)).

Inductive typing e : term -> typ -> Prop :=
| rvar x T : get_typ e x = Some T -> wf_env e -> typing e (var x) T
(* not sure about tshift *)
| rabs t T U : typing ((evar (tshift T 1 0))::e) t U -> typing e (abs T t) (arrow T U)
| rapp t u T U : typing e t (arrow T U) -> typing e u T -> typing e (app t u) U
| rtabs t T p : typing ((etvar p)::e) t T -> typing e (tabs p t) (all p T)
| rtapp t T U p : typing e t (all p T) -> kinding e U p -> typing e (tapp t U) (tsubst T U 0).




Require Import Coq.Program.Equality.
Require Import Omega.
Lemma cumulativity : forall e T p q, kinding e T p -> p <= q -> kinding e T q.
Proof.
  intros e T.
  revert e.
  induction T.
  - intros.
    inversion H.
    refine (kvar H2 _ H4).
    now transitivity p.
  - intros.
    inversion H.
    subst.
    rewrite <- (Max.max_idempotent q).
    refine (karrow _ _).
    + refine (IHT1 e p0 q H3 _).
      apply (Max.max_lub_l _ _ _ H0).
    + refine (IHT2 e q0 q H5 _).
      apply (Max.max_lub_r _ _ _ H0).
  - intros.
    inversion H.
    subst.
    assert (kinding ((etvar n)::e) T (q-1)).
    + apply (IHT (etvar n ::e) p0 (q-1)).
      * apply H4.
      * { transitivity (max p0 n).
        - apply Max.le_max_l.
        - omega.
        }
    + replace q with (1 + max (q-1) n).
      * refine (kall H1).
      * { replace (max (q-1) n) with (q-1).
        - omega.
        - assert ((max (q-1) n) = q-1).
          + apply Max.max_l.
            transitivity (max p0 n).
              * apply Max.le_max_r.
              * omega.
          + omega.
          }
Qed. 

(* TODO *)
Fixpoint infer_kind e T : option kind := match T with
| tvar X => if wf_env_dec e then get_kind e X else None
| arrow T U => match infer_kind e T with
  | Some p => match infer_kind e U with
    | Some q => Some (max p q)
    | None => None
    end
  | None => None
  end
| all q T => match infer_kind ((etvar q)::e) T with
  | Some p => Some (1 + (max p q))
  | None => None
  end
end.

Fixpoint infer_typ e t : option typ := match t with
| var x => if (wf_env_dec e) then get_typ e x else None
| abs T t => match infer_typ (evar (tshift T 1 0)::e) t with
  | Some U => Some (arrow T U)
  | None => None
  end
| app t u => match (infer_typ e u) with
  | Some T' => match (infer_typ e t) with
    | Some (arrow T U) => if (eq_typ_dec T T') then Some U else None 
    | _ => None 
    end
  | None => None 
  end
| tabs p t => match (infer_typ (etvar p::e) t) with
  | Some T => Some (all p T)
  | None => None 
  end
| tapp t T => match (infer_kind e T) with
  | Some p => match (infer_typ e t) with
    | Some (all p' U) => if (le_dec p p') then Some (tsubst U T 0) else None
    | _ => None
    end
  | None => None
  end
end.


Require Import Omega.
(* We prove correctness and minimality wrt inductive predicate [kinding] *)

Lemma infer_kind_impl e T p k :
  (infer_kind e T = Some p) -> p <= k -> kinding e T k.
Proof.
  revert e p k.
  induction T; intros e p k A B.
  - simpl in A.
    destruct (wf_env_dec e).
    + now apply kvar with (p:=p).
    + discriminate.
  - simpl in A.
    destruct (infer_kind e T1) eqn:K;
    destruct (infer_kind e T2) eqn:L;
    try discriminate.
    inversion A; subst.
    apply cumulativity with (p:= max k0 k1); auto.
    now refine (karrow (IHT1 _ k0 _ _ _) (IHT2 _ k1 _ _ _)).
  - simpl in A.
    destruct (infer_kind _ T) eqn:K; 
    try discriminate.
    inversion A; subst.
    apply cumulativity with (p:= 1 + max k0 n); auto.
    eapply kall. 
    firstorder.
Qed.

Lemma infer_kind_conv e T p :
  kinding e T p -> exists q, q <= p /\ infer_kind e T = Some q.
Proof.
  revert e p.
  induction T; intros e p A.
  - inversion A. subst.
    exists p0.
    intuition.
    simpl.
    destruct (wf_env_dec e); tauto.
  - inversion A. subst.
    pose proof (IHT1 e p0 H1) as [q' [B C]].
    pose proof (IHT2 e q H3) as [q'' [D E]].
    simpl.
    destruct (infer_kind e T1) eqn:K;
    destruct (infer_kind e T2) eqn:L; try discriminate.
    inversion C; inversion E; subst.
    exists (max q' q'').
    intuition.
    now apply NPeano.Nat.max_le_compat.
  - inversion A; subst.
    simpl.
    pose proof (IHT _ p0 H2) as [q' [B C]].
    destruct (infer_kind _ T); try discriminate.
    inversion C; subst.
    exists (S (max q' n)).
    split.
    + now apply le_n_S, NPeano.Nat.max_le_compat_r.
    + auto.
Qed.

(* Informal proof of minimality for kind inference
  (infer_kind e T = Some p) <-> (forall q, p <= q <-> kinding e T q).

inferred p -> p <= q -> kinding q 
  use infer_kind_impl

inferred p -> kinding q -> p <= q
  kinding q -> exists q', q' <= q /\ inferred q' by infer_kind_conv
  inferred q' /\ inferred p -> q' = p by injection (1)
  q' <= q -> p <= q by (1)

(all q: kinding q <-> p <= q) -> inferred p
  since p <= p, kinding p by hypothesis
  so for some r <= p, inferred r by infer_kind_conv (2)
  since inferred r, and r <= r, kinding r by infer_kind_impl (3)
  so p <= r by hypothesis.
  so p = r by (2) and (3).
*)

Lemma infer_typ_reflects e t T : 
  (infer_typ e t = Some T) <-> (typing e t T).
Proof.
  revert e T.
  induction t; intros e T'; split; intros B.
  - simpl in B.
    destruct (wf_env_dec e).
    + now apply rvar.
    + discriminate.
  - simpl. 
    inversion B. subst.
    destruct (wf_env_dec e).
    + assumption.
    + exfalso. 
      tauto.
  - simpl in B.
    specialize (IHt (evar (tshift T 1 0)::e) T').
    destruct (infer_typ _ t); try discriminate. 
    inversion B. subst.
    refine (rabs _).
    admit.
  - inversion B. subst.
    inversion B. subst.
    simpl.
    replace (infer_typ _ t) with (Some U).
    + reflexivity.
    + symmetry.
      firstorder.
  - simpl in B.
    destruct (infer_typ e t1) as [T1|] eqn:K;
    destruct (infer_typ e t2) as[T2|] eqn:L;
    try discriminate.
    pose proof ((proj1 (IHt1 _ _)) K) as C.
    pose proof ((proj1 (IHt2 _ _)) L) as D.
    destruct T1; try discriminate.
    destruct (eq_typ_dec T1_1 T2); try discriminate. subst.
    injection B as E; subst. 
    apply (rapp C D).
  - inversion B; subst.
    pose proof ((proj2 (IHt1 _ _)) H1) as C.
    pose proof ((proj2 (IHt2 _ _)) H3) as D.
    simpl.
    rewrite C, D.
    destruct (eq_typ_dec T T); congruence.
  - simpl in B.
    (* destruct eqn:_ fails here *)
    assert (exists T'', infer_typ (etvar n::e) t = Some T'').
    + destruct (infer_typ _ _).
      * exists t0. congruence.
      * discriminate.
    + destruct H as [C D].
      rewrite D in B.
      inversion B; subst.
      pose proof ((proj1 (IHt _ _)) D) as E.
      apply (rtabs E).
  - inversion B; subst.
    pose proof ((proj2 (IHt _ _)) H2) as C.
    simpl.
    now rewrite C.
  - simpl in B.
    destruct (infer_kind e T) eqn:K;
    destruct (infer_typ e t) as [[ | | p' U]|] eqn:L;
    try destruct (le_dec k p') eqn:M; 
    try discriminate.
    inversion B; subst.
    pose proof ((proj1 (IHt _ _) L)) as C.
    apply (rtapp C).
    now apply infer_kind_impl with (p:=k) (k:=p').
  - inversion B; subst.
    simpl.
    apply infer_kind_conv in H3 as [k [C D]].
    rewrite D.
    pose proof ((proj2 (IHt _ _)) H1) as E.
    rewrite E.
    destruct (le_dec k p); congruence.
Qed.

Inductive insert_kind : nat -> env -> env -> Prop :=
| inil e p : insert_kind 0 e ((etvar p)::e)
| iskip n T e e' : insert_kind n e e' -> insert_kind n ((evar T)::e) ((evar (tshift T 1 n))::e')
| icons n p e e' : insert_kind n e e' -> insert_kind (S n) ((etvar p)::e) ((etvar p)::e').


Lemma get_kind_insert_some e e' X Y p :
  insert_kind X e e' -> get_kind e Y = Some p -> get_kind e' (shift_var Y X 1) = Some p.
Proof.
  intros D E.
  revert E. revert Y.
  induction D as [e p'| | ]; intros Y E.
  - auto.
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
  insert_kind X e e' -> get_kind e' (shift_var Y X 1) = None -> get_kind e Y = None.
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
  induction 1.
  - auto.
  - simpl.
    intros [D E].
    split.
    + apply iskip with (T:=T) in H.
      now apply insert_kind_wf_typ with (n:=n) (e:=(evar T::e)).
    + auto.
  - auto.
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

(* TODO *)
Lemma insert_kind_typing X e e' t T : 
  insert_kind X e e' -> typing e t T -> typing e' t T.
Proof.
  admit.
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

Lemma shift_noop : forall t n, shift t 0 n = t.
Proof.
  induction t; simpl; intro n'; [destruct (leb n' x)|..]; auto; congruence.
Qed.

Lemma subst_preserves_typing :
  forall e x t u T U,
  typing e t T ->
  typing (remove_var e x) u U -> get_typ e x = Some U ->
  typing (remove_var e x) (subst t u x) T.
Proof.
  intros e x t. revert e x.
  induction t as [y | | | | ].
  - intros e x u T U A B C.
    unfold subst.
    simpl.
    destruct (beq_nat x y) eqn:K.
    apply beq_nat_true in K. subst.
    + rewrite (shift_noop u 0).
      inversion A; subst.
      replace T with U by congruence.
      assumption.
    + 
      * .
simpl.
  admit.
Qed.

Inductive kinding e : typ -> kind -> Prop :=
| kvar X p q : get_kind e X = Some p -> p <= q -> wf_env e -> kinding e (tvar X) q
| karrow T U p q : kinding e T p -> kinding e U q -> kinding e (arrow T U) (max p q)
| kall T p q : kinding ((etvar q)::e) T p -> kinding e (all q T) (1 + (max p q)).

Inductive typing e : term -> typ -> Prop :=
| rvar x T : get_typ e x = Some T -> wf_env e -> typing e (var x) T
| rabs t T U : typing ((evar T)::e) t U -> typing e (abs T t) (arrow T U)
| rapp t u T U : typing e t (arrow T U) -> typing e u T -> typing e (app t u) U
| rtabs t T p : typing ((etvar p)::e) t T -> typing e (tabs p t) (all p T)
| rtapp t T U p : typing e t (all p T) -> kinding e U p -> typing e (tapp t U) (tsubst T U 1).


(* TODO *)
Lemma typing_weakening_var_ind :
  forall e x t T,
  wf_env e -> typing (remove_var e x) t T -> typing e (shift t 1 x) T.

(* TODO *)
Lemma regularity e t T : exists p, kinding e T p.
Proof.
  admit.
Qed.

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

Inductive red_step : term -> term -> Prop :=
| red_typ p t T : red_step (tapp (tabs p t) T) (subst_type t T 0)
| red_term t u T : red_step (app (abs T t) u) ((subst t u) 0)
| red_abs t u T : red_step t u -> red_step (abs T t) (abs T u)
| red_appl t u v : red_step t u -> red_step (app t v) (app u v)
| red_appr t u v : red_step u v -> red_step (app t u) (app t v)
| red_tabs t u k : red_step t u -> red_step (tabs k t) (tabs k u)
| red_tapp t u T : red_step t u -> red_step (tapp t T) (tapp u T). 

Definition red := clos_trans term red_step.

Lemma red_congruent t u : red t u -> 
(  forall T, red (abs T t) (abs T u)
/\ forall v, red (app t v) (app u v)
/\ forall v, red (app v t) (app v u)
/\ forall k, red (tabs k t) (tabs k u)
/\ forall T, red (tapp t T) (tapp u T)).
Proof.
  admit.
Qed.

(* Bizarre. Il faut 2 variantes de neutral et les prédicats
   ne sont pas mutuellement inductifs *)
Inductive normal : term -> Prop :=
| nvar x : normal (var x)
| nabs T t : normal t -> normal (abs T t)
| napp t u : normal t -> normal u -> neutral t -> normal (app t u)
| ntabs k t : normal t -> normal (tabs k t)
| ntapp t T : normal t -> neutralT t -> normal (tapp t T)

with neutral : term -> Prop :=
| neutral_var x : neutral (var x)
| neutral_app t u : neutral (app t u)
| neutral_tabs k t : neutral (tabs k t)

with neutralT : term -> Prop :=
| neutralT_var x : neutralT (var x)
| neutralT_app t u : neutralT (app t u)
| neutralT_abs T t : neutralT (abs T t).

Lemma normal_neutral_preserved_typ_subst t T X :
   normal t -> normal (subst_type t T X) 
/\ neutral t -> neutral (subst_type t T X) 
/\ neutralT t -> neutralT (subst_type t T X).
Proof.
  admit.
Qed.
