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

Ltac inv H := inversion H; clear H; subst.

Hint Resolve 
  NPeano.Nat.max_le_compat 
  NPeano.Nat.max_le_compat_r 
  Max.max_idempotent
  le_n_S.

Hint Extern 1 =>
  match goal with
  | H: ?A , I: ?A -> False |- _ => exfalso; apply (I H)
  | H: ?A , I: ~ ?A |- _ => exfalso; apply (I H)
  | H: (?A <> ?A) |- _ => exfalso; now apply H
  | H: Some _ = Some _ |- _ => inv H
  end.

Hint Extern 4 =>
  match goal with
  | H: (_ = _) |- _ => discriminate
  end.

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

Fixpoint tshiftone T p := 
  match T with
    | tvar n => tvar (shift_var n p 1)
    | arrow A B => arrow (tshiftone A p) (tshiftone B p)
    | all k u => all (k) (tshiftone u (1+p))
  end
.

Fixpoint tshiftrec T m p := 
  match m with
    | S n => tshiftone (tshiftrec (T) n p) (p+n)
    | 0 => T
  end
. 
Fixpoint tshift T (m : nat) (p : nat) := 
  match T with
    | tvar n => tvar (shift_var n p m)
    | arrow A B => arrow (tshift A m p) (tshift B m p)
    | all k u => all (k) (tshift u m (1+p))
  end
.

Fixpoint tshift_in_term t (m p : nat) :=
  match t with
  | var x => var x
  | abs U s => abs (tshift U m p) (tshift_in_term s m p)
  | app s u => app (tshift_in_term s m p) (tshift_in_term u m p) 
  | tabs n t => tabs n (tshift_in_term t m (1+p))
  | tapp s U => tapp (tshift_in_term s m p) (tshift U m p)
  end.

Definition Tex := all (0) (arrow (tvar (1)) (tvar(2))).
  
Fixpoint tsubstaux T (n : nat) V (prof : nat) := 
  match T with
    | tvar m => 
      match le_dec n m with
      | left prf => (* n <= m *)
        if le_lt_eq_dec n m prf 
        then tvar (m-1) (* n < m *)
        else tshift V prof 0 (* n = m *)
      | _ => tvar m (* n > m *)
      end
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

Fixpoint get_typ_aux_no_shift e (n: nat) (m : nat) : (option typ) :=
  match e with
    |(etvar q)::e' => get_typ_aux_no_shift (e') n (1+m)
    |(evar T)::e' => match n with 0 => Some (T) | S n => get_typ_aux_no_shift (e') n m end
    |nil => None
  end
.

Definition get_typ e (n:nat) : (option typ) :=
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
  - destruct (get_kind e x) eqn:?; eauto.
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
| rabs t T U : typing ((evar T)::e) t U -> typing e (abs T t) (arrow T U)
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
| abs T t => match infer_typ (evar T::e) t with
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

Hint Extern 1 =>
  let destr T := destruct T eqn:?; try discriminate
  in match goal with
    | H: ?s <= ?b |- kinding _ _ ?b  => apply cumulativity with (p:=s) (q:=b)
    | H: match ?T with _ => _ end = Some _ |- _ => destr T
    | H:_ |- (match ?T with _ => _ end) = Some _ => destr T
  end.

Lemma infer_kind_impl T :
  forall e p, infer_kind e T = Some p -> kinding e T p.
Proof.
  induction T; simpl; eauto 10.
Qed.
Hint Resolve infer_kind_impl.

Lemma infer_kind_conv T :
  forall e p, kinding e T p -> exists q, q <= p /\ infer_kind e T = Some q.
Proof.
  induction T; intros e p A; inv A; simpl.
  - eauto.
  - apply IHT1 in H1 as (? & ? & ?).
    apply IHT2 in H3 as (? & ? & ?).
    eauto 8.
  - apply IHT in H2 as (? & ? & ?).
    eauto 7.
Qed.

Lemma infer_typ_impl t : 
  forall e T, infer_typ e t = Some T -> typing e t T.
Proof.
  induction t; simpl; eauto 10.
Qed.

Lemma infer_typ_conv t : 
  forall e T, typing e t T -> infer_typ e t = Some T.
Proof.
  induction t; intros e T' B; simpl; inv B.
  - eauto.
  - now erewrite IHt.
  - erewrite IHt2, IHt1; eauto; simpl; eauto.
  - now erewrite IHt.
  - apply infer_kind_conv in H3 as [k [C D]].
    erewrite D, IHt by eauto.
    simpl. eauto.
Qed.

Inductive insert_kind : nat -> env -> env -> Prop :=
| inil e p : insert_kind 0 e ((etvar p)::e)
| iskip n T e e' : insert_kind n e e' -> insert_kind n ((evar T)::e) ((evar (tshift T 1 n))::e')
| icons n p e e' : insert_kind n e e' -> insert_kind (S n) ((etvar p)::e) ((etvar p)::e').
Hint Constructors insert_kind.

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

Lemma tshift_commut_0 T :
  forall a b, tshift (tshift T a 0) b 0 = tshift (tshift T b 0) a 0.
  admit.
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

Lemma tsubstaux_tshift_swap : 
  forall T U X (m k:nat), m <= X ->
  tshift (tsubstaux T m U k) 1 X = tsubstaux (tshift T 1 (S X)) m (tshift U 1 (X-k)) k.
Proof.
induction T; intros; simpl in *.
- destruct_match; try omega.
  + f_equal; omega.
  + f_equal; omega.
  + replace (X - k) with (X - k + 0) by omega.
    replace X with (X + 0) at 1 by omega. 
    apply tshift_commut with (a:=k) (c:=1) (d:=X) (p:=0).
  + auto.
- rewrite IHT1, IHT2; auto.
- rewrite IHT; try omega.
  do 3 f_equal. 
  omega.
Qed.

Lemma tsubst_tshift_swap: 
  forall T U X, (tshift (tsubst T U 0) 1 X) = tsubst (tshift T 1 (S X)) (tshift U 1 X) 0.
Proof.
intros.
replace X with (X-0) at 3 by omega.
apply tsubstaux_tshift_swap. 
omega.
Qed.


Lemma insert_kind_typing X e e' t T : 
  insert_kind X e e' -> typing e t T -> typing e' (tshift_in_term t 1 X) (tshift T 1 X).
Proof.
  intros.
  revert H. revert X e'.
  induction H0; intros.
  - simpl in *. pose proof (tshift_shape H) as (k & T'' & A); subst.
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
    rewrite tsubst_tshift_swap. 
    eauto.
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
  induction t; simpl; intro n'; [destruct (le_dec n' x)|..]; auto; congruence.
Qed.


Fixpoint substaux t x u prof :=
  match t with
    |var m => 
      match le_dec x m with
      | left prf => (* x <= m *)
        if le_lt_eq_dec x m prf 
        then var (m-1) (* x < m *)
        else shift u prof 0 (* x = m *)
      | _ => var m (* x > m *)
      end
      | abs T s => abs T (substaux s (1+x) u (1+prof))
      | app s h => app (substaux s x u prof) (substaux s x u prof)
      | tabs n s => tabs n (substaux s x u prof)
      | tapp s T => tapp (substaux s x u prof) T
  end.

Definition subst t u x :=
  substaux t x u 0.


Lemma rem_var_less x y T e : get_typ e y = Some T -> y < x -> get_typ (remove_var e x) y = Some T.
admit.
Qed.

Lemma rem_var_more x y T e : get_typ e y = Some T -> y > x -> get_typ (remove_var e x) (y-1) = Some T.
admit.
Qed.

Lemma remove_var_preserve_wf_env e x : wf_env e -> wf_env (remove_var e x).
admit.
Qed.
Lemma subst_preserves_typing_test :
  forall e x t u T U p,
  typing e t T ->
  typing (remove_var e (x+p)) u U -> get_typ_aux e (x+p) 0 = Some U ->
  typing (remove_var e (x+p)) (substaux t (x+p) u p) T.
Proof.
  intros e x t. revert e x.
  induction t as [y | | | | ].
  - intros e x u T U p A B C.
    unfold subst.
    simpl.
    destruct (le_dec (x+p) y);
    [ destruct (le_lt_eq_dec (x+p) y _) | ].
    + inv A.
      apply remove_var_preserve_wf_env with (x:=(x+p)) in H1.
      apply rem_var_more with (x:=(x+p)) in H0. 
      * eauto. 
      * omega.
    + subst. 
      (*rewrite shift_noop.
      inversion A.
      now rewrite C in H0; inversion H0; subst.*)
      admit.
    + inv A.
      apply remove_var_preserve_wf_env with (x:=(x+p)) in H1.
      apply rem_var_less with (x:=(x+p)) in H0.
      * eauto.
      * omega. 
  - intros.
    inv H. simpl. apply rabs.
    replace (evar T :: remove_var e (x + p)) with (remove_var (evar T :: e) (S (x+p))).
    * { replace (S (x+p)) with (x + S (p)) by omega.
        refine (IHt (evar T :: e) x u U0 U (S p)_ _ _).
        - apply H5.
        - admit.
        - simpl. 
          replace (x + S p) with (S (x+p)) by omega.
          apply H1.
      }
    * simpl.
      reflexivity.
  - intros.


Lemma subst_preserves_typing :
  forall e x t u T U,
  typing e t T ->
  typing (remove_var e x) u U -> get_typ_aux e x 0 = Some U ->
  typing (remove_var e x) (substaux t x u 0) T.
Proof.
  intros e x t. revert e x.
  induction t as [y | | | | ].
  - intros e x u T U A B C.
    unfold subst.
    simpl.
    destruct (le_dec x y); 
    [ destruct (le_lt_eq_dec x y _) | ].
    + inv A.
      apply remove_var_preserve_wf_env with (x:=x) in H1.
      apply rem_var_more with (x:=x) in H0. 
      * eauto. 
      * omega.
    + subst. 
      (*rewrite shift_noop.
      inversion A.
      now rewrite C in H0; inversion H0; subst.*)
      admit.
    + inv A.
      apply remove_var_preserve_wf_env with (x:=x) in H1.
      apply rem_var_less with (x:=x) in H0.
      * eauto.
      * omega. 
  - intros.
    inv H. simpl. apply rabs.  
    (* ça coince là *)
(*    je laisse ça pour mémoire mais ça aide pas : specialize (IHt _ (S x) u _ U k 

typing e t U0 ->
      typing (remove_var e x) u U ->
      get_typ_aux e x 0 = Some U ->
      typing (remove_var e x) (substaux t x u 0) U
U:=U0
e:=(remove_var e x)
t:=(substaux t (x+1) u 1)
T:=T

so as a premise we need
typing (evar T::(remove_var e x)) (substaux t (x+1) u 1) U0

we can get
typing (remove_var e x) (subst (abs T t) u x) T0

    eauto. rabs simpl.
    
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
