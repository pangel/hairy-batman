(** * Correction et complétude de l'inférence de type pour le système F stratifié.

*)

Require Import init.

(* Les variables avec les noms suivants prennent le type correspondant par défaut : *)

Implicit Types 
(x y z X Y Z : nat)
(T U V : typ)
(n k p q : kind)
(t s u v : term)
(e f : env).

 
(* L'égalité des types est décidable *)
Fixpoint eq_typ_dec T U : sumbool (T = U) (T <> U).
Proof.
  repeat decide equality.
Qed.

(** ** Inférence de kind et de type *)

(** On reprend exactement les règles données dans l'article *)

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

(** ** Correction et complétude de l'inférence *)

(** On automatise la disjonction de cas au moment de traverser les fonctions
    d'inférence *)

Hint Local Extern 1 =>
  let destr T := destruct T eqn:?; try discriminate
  in match goal with
    | H: ?s <= ?b |- kinding _ _ ?b  => apply cumulativity with (p:=s) (q:=b)
    | H: match ?T with _ => _ end = Some _ |- _ => destr T
    | H:_ |- (match ?T with _ => _ end) = Some _ => destr T
    | H: exists a, _ /\ _ |- _ => decompose [ex and] H; clear H
  end.

(** Correction d'[infer_kind] *)

Theorem infer_kind_correct T :
  forall e p, infer_kind e T = Some p -> kinding e T p.
Proof.
  induction T; simpl; eauto 10.
Qed.
Hint Resolve infer_kind_correct.

(** Complétude d'[infer_kind] *)

Theorem infer_kind_complete T e p:
  kinding e T p -> exists q, q <= p /\ infer_kind e T = Some q.
Proof.
  induction 1; simpl; eauto 10.
Qed.
Hint Resolve infer_kind_complete.

(** Correction d'[infer_typ] *)

Theorem infer_typ_correct t : 
  forall e T, infer_typ e t = Some T -> typing e t T.
Proof.
  induction t; simpl; eauto 10.
Qed.

(** Complétude d'[infer_typ] *)

Theorem infer_typ_complete t e T : 
  typing e t T -> infer_typ e t = Some T.
Proof.
  induction 1; intros; simpl; eauto 7.
  apply infer_kind_complete in H0. 
  eauto 9.
Qed.
