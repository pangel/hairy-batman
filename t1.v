(*Indentation : 2 espaces *)

(* On n'a pas à écrire les arguments inférables *)
Global Set Implicit Arguments. 
Global Unset Strict Implicit.

Require Import 
  List 
  Arith 
  Relations
  Omega
  Bool
  Coq.Program.Equality.

(* Hints, tactics *)

Hint Resolve 
  NPeano.Nat.max_le_compat 
  NPeano.Nat.max_le_compat_r 
  Max.max_idempotent
  le_n_S.

Hint Extern 1 =>
  match goal with
  | [ H: ?A , I: ?A -> False |- _ ] => exfalso; apply (I H)
  end.

Hint Extern 4 =>
  match goal with
  | H: (_ = _) |- _ => discriminate
  end.

Ltac inv H := inversion H; clear H; subst.

(* Definitions *)

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
    |(etvar q)::e' => get_typ_aux (e') n (1+m)
    |(evar T)::e' => match n with 0 => Some (tshift T m 0) | S n => get_typ_aux (e') n m end
    |nil => None
  end
.

Fixpoint get_typ e (n:nat) : (option typ) :=
 get_typ_aux e n 0
.

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

Hint Constructors kinding typing.

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

(* We prove correctness and minimality wrt inductive predicate [kinding] *)
Hint Extern 4 =>
  match goal with
  | H: context[if wf_env_dec ?e then _ else _] |- _  =>
  let K := fresh "K" in
  destruct (wf_env_dec e) eqn:K; try discriminate
  | H: context[match infer_kind ?e ?T with _ => _ end] |- _ =>
  let K := fresh "K" in
  destruct (infer_kind e T) eqn:K; try discriminate
  | H: Some _ = Some _ |- _ => inversion H; subst
  end.

Hint Extern 2 =>
match goal with
  | H:_ |- context[wf_env_dec ?e] => 
  let K := fresh "K" in
  destruct (wf_env_dec e) eqn:K; try discriminate
end.

Hint Extern 4 =>
match goal with
  | H: Some _ = Some _ |- _ => inversion H; subst
  end.

Lemma infer_kind_impl e T p :
  infer_kind e T = Some p -> kinding e T p.
Proof.
  revert e p.
  induction T; intros e p A; simpl in A; eauto 7.
Qed.

Lemma infer_kind_conv e T p :
  kinding e T p -> exists q, q <= p /\ infer_kind e T = Some q.
Proof.
  revert e p.
  induction T; intros e p A; inv A; simpl.
  - eauto.
  - pose proof (IHT1 _ _ H1) as [? [? C]].
    pose proof (IHT2 _ _ H3) as [? [? E]].
    rewrite C, E.
    eauto.
  - pose proof (IHT _ p0 H2) as [? [? ?]].
    destruct (infer_kind _ T); 
    eauto 7.
Qed.

(* Informal proof of minimality for kind inference
  (infer_kind e T = Some p) <-> (forall q, p <= q <-> kinding e T q).

inferred p -> p <= q -> kinding q 
  use infer_kind_impl and cumulativity

inferred p -> kinding q -> p <= q
  kinding q -> exists q', q' <= q /\ inferred q' by infer_kind_conv
  inferred q' /\ inferred p -> q' = p by injection (1)
  q' <= q -> p <= q by (1)

(all q: kinding q <-> p <= q) -> inferred p
  since p <= p, kinding p by hypothesis
  so for some r <= p, inferred r by infer_kind_conv (2)
  since inferred r, kinding r by infer_kind_impl (3)
  so p <= r by hypothesis.
  so p = r by (2) and (3).
*)

Hint Extern 2 =>
match goal with
  | H: context[if eq_typ_dec ?T ?T' then _ else _] |- _ =>
  let K := fresh "K" in
  destruct (eq_typ_dec T T') eqn:K; try discriminate
end.

Hint Extern 1 =>
match goal with
  | H: context[match infer_typ ?e ?T with _ => _ end] |- _ =>
  let K := fresh "K" in
  destruct (infer_typ e T) eqn:K; try discriminate
end.

Hint Extern 1 =>
match goal with
  | H: context[match (?t:typ) with _ => _ end] |- _ =>
  let K := fresh "K" in
  destruct t eqn:K; try discriminate
end.

Lemma infer_typ_impl e t T : 
  (infer_typ e t = Some T) -> (typing e t T).
Proof.
  revert e T.
  induction t; intros e T' B; simpl in B.
  - eauto.
  - eauto.
  - eauto 7. destruct (infer_typ e t1) eqn:K;
destruct (infer_typ e t2) eqn:L; eauto.
destruct t eqn:K'; try discriminate.
eauto 15. destruct (infer_typ e t1) as [[ | | ]|] eqn:K;
    destruct (infer_typ e t2) eqn:L; eauto 7. eauto 7.
    destruct (eq_typ_dec T t) eqn:K'; try discriminate. eauto.
    

destruct (infer_typ e t1) as [[ | | ]|] eqn:K;
    destruct (infer_typ e t2) eqn:L;
    try destruct (eq_typ_dec _ _);
    inv B. 
    eauto.
  - destruct (infer_typ _ _) eqn:K; inv B.
    eauto.
  - destruct (infer_kind e T) eqn:K;
    destruct (infer_typ e t) as [[ | | p' U]|] eqn:L;
    try destruct (le_dec k p') eqn:M; 
    inv B.
    pose proof (infer_kind_impl K). eauto.
    apply cumulativity with (q:=p') in H; eauto.
Qed.

Lemma infer_typ_conv e t T : 
  (typing e t T) -> (infer_typ e t = Some T).
Proof.
  revert e T.
  induction t; intros e T'; intros B; simpl; inv B.
  - destruct (wf_env_dec e); auto.
  - now rewrite (IHt _ _ H2).
  - rewrite (IHt1 _ _ H1), (IHt2 _ _ H3).
    destruct (eq_typ_dec _ _); congruence.
  - now rewrite (IHt _ _ H2).
  - apply infer_kind_conv in H3 as [k [C D]].
    rewrite D, (IHt _ _ H1).
    destruct (le_dec _ _); congruence.
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

Lemma shift_l : forall k T T0 l, tshift T0 k l = T -> tshift T0 (S k) l = tshift T 1 l.
induction T.
- intros.
  destruct T0.
  + simpl in *.
    f_equal.
    injection H as H1.
    destruct (le_dec l x0) as []eqn:?.
    * destruct (le_dec l x) as []eqn:? ; omega.
    * destruct (le_dec l x) as []eqn:? ; omega.
  + simpl. discriminate.
  + simpl. discriminate.
- intros.
  destruct T0.
  + simpl tshift in H.
    discriminate.
  + simpl tshift in *.
    inversion H.
    rewrite IHT1 ; auto.
    rewrite IHT2 ; auto.
    rewrite H1.
    rewrite H2.
    auto.
  + simpl tshift in H.
    discriminate.
- intros.
  destruct T0.
  + simpl  in *.
    discriminate.
  + simpl in *.
    discriminate.
  + simpl tshift in *.
    inversion H.
    subst.
    f_equal.
    rewrite IHT ; auto.
Qed.

Lemma recur_lemma : forall T e k n, get_typ_aux e n k = Some T -> get_typ_aux e n (S k) = Some (tshift T 1 0).
Proof.
induction e.
- intros.
  simpl in *.
  discriminate.
- intros.
  destruct a.
  + simpl in *.
    destruct n.
    * f_equal.
      injection H as H1.
      simpl tshift in .
      apply (shift_l H1).
    * apply (IHe k n).
      apply H.
  + simpl.
    apply (IHe (S k) n).
    simpl get_typ_aux in H.
    apply H.
Qed.
Lemma get_typ_aux_shift : forall T e k n, get_typ_aux e n 0 = Some T -> get_typ_aux e n k = Some (tshift T k 0).
Proof.
induction k.
- intros.
  induction e.
  + simpl.
    discriminate.
  + destruct a.
    * { simpl in *.
        destruct n.
        - f_equal.
          f_equal.
          injection H as H1.
          transitivity (tshift T0 0 0).
          + symmetry. 
            apply tshift_ident.
          + apply H1.
        - replace (tshift T 0 0) with T.
          + apply H.
          + symmetry.
            apply tshift_ident.
            }
    * { simpl in *.
        replace (tshift T 0 0) with T.
        - apply H.
        - symmetry.
          apply tshift_ident.
      }
- intros.
  assert ( get_typ_aux e n k = Some (tshift T k 0)).
  + specialize (IHk n).
    apply IHk.
    apply H.
  + assert (get_typ_aux e n (S k) = Some (tshift (tshift T k 0) 1 0)).
    * apply (recur_lemma H0).
    * { transitivity (Some (tshift (tshift T k 0) 1 0)).
          - apply H1. 
          - symmetry.
            f_equal. 
            refine (shift_l _).
            reflexivity.
      }
Qed.
(*
forall T e n, (forall k, get_typ_aux e n k = None) \/ (forall k, get_typ_aux e n k = Some (shift T k 0))
*)

Lemma get_typ_et : forall T e Y p, get_typ e Y = Some T -> get_typ (etvar p :: e) Y = Some (tshift T 1 0).
Proof.
(*
induction Y.
- induction e.
  + intros.
    simpl get_typ in H.
    discriminate.
  + intros.
    simpl in *.
    destruct a.
    * { injection H as H1.
        f_equal.
        f_equal.
        transitivity (tshift T0 0 0).
        - symmetry.
          apply tshift_ident.
        - apply H1.
      }
    * { simpl in H .
        destruct e0.
        - admit.
        -
   *)  

induction e.
- intros.
  simpl in H.
  discriminate.
- destruct a.
  + intros.
    simpl.
    destruct Y.
    * { simpl get_typ in H.
        assert (tshift T0 0 0 = T0).
        - apply (tshift_ident T0 0).
        - injection H as H1.
          replace T0 with T.
          + reflexivity.
          + transitivity (tshift T0 0 0).
            * symmetry.
              apply H1.
            * apply H0.
       }
    * simpl get_typ in H.
      now apply get_typ_aux_shift with (k :=1).
  + intros.
    simpl in *.
    admit.
Qed.

Lemma get_type_insert_some e e' X Y T :
  forall m p, insert_kind X e e' -> get_typ_aux e Y m = Some (tshift T (m+ p) 0) -> 
  get_typ_aux e' Y m = Some (tshift (tshift T 1 (X-p)) (m+p) 0).
Proof.
  intros m p E. revert E Y T m p. intros D.

(*
 revert Y. revert D. revert e e' T.
  induction (X-p).
  - intros.
    admit.
  - intros.
    rewrite IHn with (e := e) (T :=T).
    +admit.
    +auto.
    +auto.
    destruct e'.
    + inversion D.
    + destruct e0.
      * { simpl in *.
        - destruct Y.
          + inversion D. subst.
            do 2 f_equal.
     *)  
    
  induction D.
  - intros.
    simpl get_typ in H.
    simpl.
    admit.
    (*refine (get_typ_et p _).
    apply E.*)
  -intros.
   simpl .
   simpl in *.
   destruct Y.
   + admit.
   + admit. 
  - intros.
    (*now apply IHD.*)
    simpl get_typ_aux in *.
(*    destruct p0.
    + rewrite IHD with (p := -1).
      *)
      rewrite (IHD Y T (S m) (p0-1)).
      + admit.
      + 
      destruct p0.
      + admit.
      + rewrite (IHD Y T (S m) (p0-1)) 
    
  
    + admit.
    + rewrite H. do 2 f_equal. omega.
    simpl in *.
    rewrite IHD with (p := p0).
    simpl in *.
 apply (IHD _ m E).
 - intros.
   simpl in *.
   apply (IHD _ _ E).
rewrite E.
    + intros.
      subst.
      unfold get_typ.
      unfold get_typ_aux.
      simpl.
      simpl in E.
      apply E.
      unfold get_typ.
      unfold get_typ_aux.
      destruct E.
    simpl in *.
    destruct Y.
    + destruct (le_dec (S p) 0).
      * omega.
      * { unfold get_typ_aux.
          destruct e.
          - unfold get_typ in E.
            unfold get_typ_aux in E.
            apply E.
          - destruct e.
            + unfold get_typ in E.
              unfold get_typ_aux in E.
              unfold tshift in E.
              
          simpl in *.


(*  intros D E.
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
      auto; omega.*)

(* TODO *)
Lemma insert_kind_typing X e e' t T : 
  insert_kind X e e' -> typing e t T -> typing e' t T.
Proof.
  generalize T e e' X t.
  induction T0.
  - intros.
    inversion H0.
    subst.
    refine (rvar H1 _ _). 
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
