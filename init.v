(** * Projet Coq, cours MPRI 2014-2015

Groupe : Matthieu Journault, Lucas Randazzo, Adrien Husson.

On montre plusieurs propriétés du système F stratifié en se basant sur l'article
disponible à l'adresse ci-dessous : décidabilité de l'inférence de type, 
cumulativity, regularity, narrowing, congruence de la beta-réduction, 
préservation de la normalisation par substitution de type.

http://homepage.divms.uiowa.edu/~astump/papers/pstt-2010.pdf

Enoncé du projet :

https://wikimpri.dptinfo.ens-cachan.fr/lib/exe/fetch.php?media=cours:upload:2-7-2-projet.pdf

*)

(** ** Hints et tactiques globales *)

(** On n'a pas à écrire les arguments inférables *)

Global Set Implicit Arguments. 
Global Unset Strict Implicit.

Require Export 
  List 
  Arith 
  Relations
  Omega
  Bool
  Coq.Program.Equality.

(** Inversion légèrement améliorée *)

Ltac inv H := inversion H; clear H; subst.

Hint Resolve 
  NPeano.Nat.max_le_compat 
  NPeano.Nat.max_le_compat_r 
  Max.max_idempotent
  le_n_S.


(** Raisonnement propositinnel simple et élimination du constructeur [Some] *)

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

(** ** Définitions de base *)

Definition kind := nat.

(** On utilise les indices de Bruijn localement et globalement.
    On n'a pas à s'occuper d'alpha-conversion, mais beaucoup de lemmes sont
    dûs au shifts lors de passage sous / sortie de binders.

    On aurait pu utiliser Autosubst ou l'un des autres travaux mentionnés ici :

    https://www.ps.uni-saarland.de/autosubst/

    Mais ça aurait été moins intéressant. *)

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

(** L'environnement est une liste d'éléments d'un type à deux constructeurs.
    On a donc un seul environnement, mais bien deux ensembles d'indices : la
    [n]ième variable de type de [e] est la [n]ième variable de [e] privé de
    toutes ses variables de terme. L'inverse est vrai pour les variables de
    terme.

    Il serait peut-être plus simple d'avoir un type list-like à trois
    constructeurs [enil], [evar] et [etvar].

    Lorsqu'une variable de terme est extraite d'un environnement, son type est
    [tshift]é d'autant de variables de type qu'il y a à sa gauche. On aurait pu
    effectuer ce shift à chaque insertion d'une variable de type, mais cela
    aurait rendu les énoncés plus complexes puisque même un énoncé simple comme
    [wf_env] (well-formedness d'environnement) aurait dû mentionner des shifts
    d'environnement lors de ses appels récursifs.

    Maintenir deux environnements forcerait soit à aussi utiliser le
    pré-shifting mentionné ci-dessus, soit à garder trace du contexte de kind
    auquel une variable de terme peut faire référence.

    Enfin, on pourrait avoir un seul ensemble d'indices pour les variables et
    traiter tous les binders de façon uniforme lors des substitutions. C'est
    une possibilité que nous n'avons pas explorée. *)

Inductive envElem :=
| evar (T:typ)
| etvar (n:kind).

Definition env := list envElem.

(** Les variables avec les noms suivants prennent le type correspondant par défaut : *)

Implicit Types 
(x y z X Y Z : nat)
(T U V : typ)
(n k p q : kind)
(t s u v : term)
(e f : env).

(** ** Shifting et substitutions *)

(** Décale [n] de [inc] si [n >= floor]. *)

Definition shift_var n inc floor :=
  if (le_dec floor n) then inc+n else n.
Arguments shift_var / _ _ _.

(** Décale de [m] les variables de {type,terme,type} de {[T],[t],[t]} qui pointent après [p] (non strict). *)

Fixpoint tshift T (m : nat) (p : nat) := 
  match T with
    | tvar n => tvar (shift_var n m p)
    | arrow A B => arrow (tshift A m p) (tshift B m p)
    | all k u => all (k) (tshift u m (1+p))
  end
.

Fixpoint shift t (m : nat) (p : nat) := 
  match t with
    | var n => var (shift_var n m p)
    | abs T s =>  abs T (shift s m (1+p))
    | app s u => app (shift s m p) (shift u m p) 
    | tabs n s => tabs n (shift s m p) 
    | tapp s T => tapp (shift s m p) T
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

(** Dans {[T],[t],[t]}, remplace les variables de {type,terme,type} qui pointent vers {[X],[x],[X]} par {[U],[u],[U]}. *)

Fixpoint tsubst T U (X : nat) := 
  match T with
    | tvar m => 
      match le_dec X m with
      | left prf => (* X <= m *)
        if le_lt_eq_dec X m prf 
        then tvar (pred m) (* X < m *)
        else U (* X = m *)
      | _ => tvar m (* X > m *)
      end
     | arrow A B => arrow (tsubst A U X) (tsubst B U X)
     | all k u => all k (tsubst u (tshift U 1 0) (1+X))
   end.

Fixpoint subst t u x :=
  match t with
    |var m => 
      match le_dec x m with
      | left prf => (* x <= m *)
        if le_lt_eq_dec x m prf 
        then var (pred m) (* x < m *)
        else u (* x = m *)
      | _ => var m (* x > m *)
      end
      | abs T s => abs T (subst s (shift u 1 0) (1+x))
      | app s h => app (subst s u x) (subst h u x)
      | tabs n s => tabs n (subst s (tshift_in_term u 1 0) x)
      | tapp s T => tapp (subst s u x) T
  end.

Fixpoint subst_type t U X :=
  match t with
    | var x => var x
    | abs T s => abs (tsubst T U X) (subst_type s U X)
    | app s u => app (subst_type s U X) (subst_type u U X) 
    | tabs n t => tabs n (subst_type t U (1+X))
    | tapp s T => tapp (subst_type s U X) (tsubst T U X)
  end.

(** ** Manipulation des contextes *)

(** Récupère le kind donné par [e] à la [n]ième variable de type. *)

Fixpoint get_kind e (n:nat) : (option kind) := 
  match e with
    |(etvar m)::e' => match n with 0 => Some m | S n => get_kind e' n end
    |(evar T)::e' => get_kind e' n
    |nil => None
  end
.

(** Récupère le type donné par [e] à la [n]ième variable de terme.
   Chaque variable de type située à gauche du type trouvé occasionne un 
   tshift du type retourné. *)

Fixpoint get_typ e (n: nat) : (option typ) :=
  match e with
    |(etvar q)::e' => match get_typ e' n with
      | Some T => Some (tshift T 1 0)
      | None => None
      end
    |(evar T)::e' => match n with 0 => Some T | S n => get_typ (e') n end
    |nil => None
  end
.

(** ** Well-formedness *)

(** Définition et preuve de décidabilité de la well-formedness des types
   et des environnements. *)

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
| (evar T)::e' => wf_typ e' T /\ wf_env e'
| (etvar p)::e' => wf_env e'
end.

Lemma wf_env_dec e : { wf_env e } + { wf_env e -> False }.
Proof. 
  induction e as [|[U|p]]; simpl; auto.
  destruct (wf_typ_dec e U); tauto.
Qed.

(** ** Prédicats de kinding et de typing. *)

Inductive kinding e : typ -> kind -> Prop :=
| kvar X p q : get_kind e X = Some p -> p <= q -> wf_env e -> kinding e (tvar X) q
| karrow T U p q : kinding e T p -> kinding e U q -> kinding e (arrow T U) (max p q)
| kall T p q : kinding ((etvar q)::e) T p -> kinding e (all q T) (1 + (max p q)).

Inductive typing e : term -> typ -> Prop :=
| rvar x T : get_typ e x = Some T -> wf_env e -> typing e (var x) T
| rabs t T U : typing ((evar T)::e) t U -> typing e (abs T t) (arrow T U)
| rapp t u T U : typing e t (arrow T U) -> typing e u T -> typing e (app t u) U
| rtabs t T p : typing ((etvar p)::e) t T -> typing e (tabs p t) (all p T)
| rtapp t T U p : typing e t (all p T) -> kinding e U p -> typing e (tapp t U) (tsubst T U 0).

Hint Constructors kinding typing.

(** *** Lemmes simples sur [kinding] et [typing] *)

Lemma kinding_implies_wf_typ e T p : kinding e T p -> wf_typ e T.
Proof.
  induction 1; simpl; auto; congruence.
Qed.

Lemma kinding_implies_wf_env e T p : kinding e T p -> wf_env e.
Proof.
  induction 1; auto.
Qed.

(** Well-formedness de [T] et [e] implique [kinding] de [T] dans [e]. *)

Lemma wf_implies_kinding T : forall e, wf_env e -> wf_typ e T -> exists p, kinding e T p.
Proof.
  induction T;
  intuition;
  simpl wf_typ in H0.
  - destruct (get_kind e x) eqn:N.
    + exists k. 
      assert (A : k <= k). 
      * trivial.
      * apply (kvar N A H). 
    + tauto.
  - destruct H0.
    specialize (IHT1 e).
    specialize (IHT2 e).
    intuition.
    destruct H2.
    destruct H4.
    exists (max x0 x).
    apply (karrow H3 H2).
  - assert (W : wf_env (etvar n :: e)).
    + simpl.
      tauto.
    + specialize (IHT (etvar n :: e)).
      intuition.
      destruct H2.
      exists (1 + (max x n)).
      apply (kall H1).    
Qed.

(** Le typage implique la well-formedness. *)

Lemma typing_implies_wf_env e t T : typing e t T -> wf_env e.
Proof.
  induction 1; simpl in *; auto; tauto.
Qed.


(** Cas utile : si [e] type un terme, la tête de [e] est bien formée *)
Lemma typing_implies_wf_typ T e t U : typing (evar T::e) t U -> wf_typ e T.
Proof.
  intro.
  apply typing_implies_wf_env with (e := evar T::e) in H.
  destruct H. auto.
Qed.

(** ** Cumulativité : Dans [e], si [T] as pour kind [p] et [p <= q], alors [T] a pour kind [q] *)

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
Hint Resolve cumulativity.
