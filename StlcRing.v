Set Warnings "-notation-overridden,-parsing".

Require Import Coq.Strings.String.
Require stdpp.stringmap.
Require Coq.setoid_ring.Ncring.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.setoid_ring.Algebra_syntax.

From PLF Require Import Maps.

Module STLCRingCompiler.
  
  Local Open Scope string_scope.
  Context {R: Type}`{Coq.setoid_ring.Ncring.Ring_ops R}.

  Inductive ty : Type :=
  | Ty_Arrow : ty -> ty -> ty
  | Ty_Bool  : ty
  | Ty_Ring  : ty.

  Inductive tm : Type :=
  (* pure STLC *)
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
  (* Bool algebra *)
  |tm_boolc: bool -> tm
  | tm_and : tm -> tm -> tm
  | tm_or : tm -> tm -> tm
  | tm_neg: tm -> tm                        
  (* Ring algebra *)
  |tm_rc: R -> tm
  |tm_opp: tm -> tm
  |tm_add: tm -> tm -> tm
  |tm_mul: tm -> tm -> tm
  |tm_eq: tm -> tm -> tm
  |tm_if: tm -> tm -> tm -> tm.

  Definition x : string := "x".
  Definition y : string := "y".
  Definition z : string := "z".
  Definition f: string := "f".
  Definition a: string := "a".
  Hint Unfold x : core.
  Hint Unfold y : core.
  Hint Unfold z : core.
  Hint Unfold f : core.
  Hint Unfold a : core.

  Declare Custom Entry stlc.
  Declare Custom Entry stlc_ty.

  Notation "<{ e }>" := e (e custom stlc at level 99).
  Notation "<{{ e }}>" := e (e custom stlc_ty at level 99).
  Notation "( x )" := x (in custom stlc, x at level 99).
  Notation "( x )" := x (in custom stlc_ty, x at level 99).
  Notation "x" := x (in custom stlc at level 0, x constr at level 0).
  Notation "x" := x (in custom stlc_ty at level 0, x constr at level 0).
  Notation "S -> T" := (Ty_Arrow S T) (in custom stlc_ty at level 50, right associativity).
  Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
  Notation "\ x : t , y" :=
    (tm_abs x t y) (in custom stlc at level 90, x at level 99,
                       t custom stlc_ty at level 99,
                       y custom stlc at level 99,
                       left associativity).
  Coercion tm_var : string >-> tm.
  
  Notation "{ x }" := x (in custom stlc at level 1, x constr).

  Notation "'Ring'" := Ty_Ring (in custom stlc_ty at level 0).
  Notation "'Bool'" := Ty_Ring (in custom stlc_ty at level 0).
  Notation "x && y" := (tm_and x y) (in custom stlc at level 2,
                                        left associativity).
  Notation "x || y" := (tm_or x y) (in custom stlc at level 2,
                                        left associativity).
  Notation "'opp' x" := (tm_opp x) (in custom stlc at level 0,
                                        x custom stlc at level 0).
  Notation "'neg' x" := (tm_neg x) (in custom stlc at level 0,
                                       x custom stlc at level 0).
  Notation "x + y" := (tm_add x y) (in custom stlc at level 2,
                                        left associativity).
  Notation "x * y" := (tm_mul x y) (in custom stlc at level 2,
                                        left associativity).
  Notation "x == y" := (tm_eq x y) (in custom stlc at level 1,
                                        left associativity).
  Notation "'if' x 'then' y 'else' z" :=
    (tm_if x y z) (in custom stlc at level 89,
                       x custom stlc at level 99,
                       y custom stlc at level 99,
                       z custom stlc at level 99,
                       left associativity).
  
  Coercion tm_rc : R >-> tm.
  Coercion tm_boolc : bool >-> tm.

  Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).
  
  Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
    match t with
    (* pure STLC *)
    | tm_var y =>
      if eqb_string x y then s else t
    | <{\y:T, t1}> =>
      if eqb_string x y then t else <{\y:T, [x:=s] t1}>
    | <{t1 t2}> =>
      <{([x:=s] t1) ([x:=s] t2)}>
    (* booleans *)
    | tm_boolc _ => t
    | <{neg t}> => <{ neg ([x:=s] t) }>
    | <{t1 && t2}> => <{ ([x:=s]t1) && ([x:=s]t2) }>
    | <{t1 || t2}> => <{ ([x:=s]t1) || ([x:=s]t2) }>
    (* numbers *)
    | tm_rc _ => t
    | <{opp t}> => <{opp ([x:=s] t)}>
    | <{t1 + t2}> =>
      <{ ([x := s] t1) + ([x := s] t2)}>
    | <{t1 * t2}> =>
      <{ ([x := s] t1) * ([x := s] t2)}>
    | <{t1 == t2}> =>
      <{ ([x := s] t1) == ([x := s] t2)}>
    | <{if t1 then t2 else t3}> =>
      <{if [x := s] t1 then [x := s] t2 else [x := s] t3}>
    end
  where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).

  Inductive value : tm -> Prop :=
  | value_abs : forall x T e,
      value <{\x:T, e}>
  | v_b : forall b: bool,
      value <{b}>
  | v_r : forall n : R,
      value <{n}>.

  Reserved Notation "t '-->' t'" (at level 40).
  
  Inductive step : tm -> tm -> Prop :=
  (* pure STLC *)
  | ST_AppAbs : forall x T2 t1 v2,
      value v2 ->
      <{ (\x:T2, t1) v2 }> --> <{ [x:=v2]t1 }>
  | ST_App1 : forall t1 t1' t2,
      t1 --> t1' ->
      <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      <{v1 t2}> --> <{v1  t2'}>
  (* Bools *)
  |ST_And: forall b1 b2: bool, <{b1 && b2}> --> <{ {andb b1 b2} }>
  |ST_And1: forall t1 t2 t1', t1 --> t1' ->
                         <{t1 && t2}> --> <{t1' && t2 }>
  |ST_And2: forall t1 t2 t2', value t1 ->
                         t2 --> t2' ->
                         <{t1 && t2}> --> <{t1 && t2' }>
  |ST_Or: forall b1 b2: bool, <{b1 || b2}> --> <{ {orb b1 b2} }>
  |ST_Or1: forall t1 t1' t2: bool, t1 --> t1' ->
                           <{t1 || t2}> --> <{t1' || t2 }>
  |ST_Or2: forall t1 t2 t2': bool, value t1 ->
                           t2 --> t2' ->
                           <{t1 || t2}> --> <{ t1 || t2' }>
  |ST_Neg: forall b: bool, <{ neg b }> --> <{ {negb b} }>
  |ST_Neg1: forall t t', t --> t' ->
                    <{ neg t }> --> <{ neg t' }>
  (* Numbers *)
  |ST_Addc: forall n1 n2 : R, <{n1 + n2}> --> <{ {n1+n2} }>
  |ST_Add1: forall t1 t1' t2, t1 --> t1'->
                          <{t1 + t2}> --> <{t1' + t2}>
  |ST_Add2:forall v1 t2 t2',value v1 ->
                        t2 --> t2' ->
                        <{v1 + t2}> --> <{v1 + t2'}>
  |ST_EqTrue: forall n1 n2 : R, n1 == n2 ->
                        <{n1 == n2}> --> <{ {true} }>
  |ST_EqFalse: forall n1 n2: R, ~(n1 == n2) ->
                           <{n1 == n2}> --> <{ {false} }>
  |ST_Eq1: forall t1 t1' t2, t1 --> t1'->
                          <{t1 == t2}> --> <{t1' == t2}>
  |ST_Eq2:forall v1 t2 t2',value v1 ->
                        t2 --> t2' ->
                        <{v1 == t2}> --> <{v1 == t2'}>                      
  |ST_Mulc: forall n1 n2 : R, <{n1*n2}> --> <{ {n1*n2} }>
  |ST_Mult1: forall t1 t1' t2, t1 --> t1'->
                          <{t1*t2}> --> <{t1'*t2}>
  |ST_Mult2:forall v1 t2 t2',value v1 ->
                        t2 --> t2' ->
                        <{v1 * t2}> --> <{v1 * t2'}>
  |ST_If: forall t1 t1' t2 t3, t1 --> t1'->
                          <{ if t1 then t2 else t3 }> --> <{if t1' then t2 else t3}>
  |ST_If_true: forall t2 t3, <{if {true} then t2 else t3}> --> t2
  |ST_If_false: forall t2 t3,<{if {false} then t2 else t3}> --> t3
  where "t '-->' t'" := (step t t').
                  
(** Big-step semantics *)
Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Hint Constructors step : core.
Hint Constructors value : core.
Hint Constructors multi: core.
(* ----------------------------------------------------------------- *)
(** *** Typing *)

Definition context := partial_map ty.

(** Next we define the typing rules.  These are nearly direct
    transcriptions of the inference rules shown above. *)

Reserved Notation "Gamma '|-' t '\in' T" (at level 40, t custom stlc, T custom stlc_ty at level 0).

Inductive has_type : context -> tm -> ty -> Prop :=
  (* pure STLC *)
  | T_Var : forall Gamma x T1,
      Gamma x = Some T1 ->
      Gamma |- x \in T1
  | T_Abs : forall Gamma x T1 T2 t1,
    (x |-> T2 ; Gamma) |- t1 \in T1 ->
      Gamma |- \x:T2, t1 \in (T2 -> T1)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |- t1 \in (T2 -> T1) ->
      Gamma |- t2 \in T2 ->
      Gamma |- t1 t2 \in T1
  (* bools *)
  | T_Eq: forall Gamma t1 t2,
      Gamma |- t1 \in Ring ->
      Gamma |- t2 \in Ring ->
      Gamma |- t1 == t2 \in Bool
  | T_And: forall Gamma t1 t2,                                             
      Gamma |- t1 \in Bool ->
      Gamma |- t2 \in Bool ->
      Gamma |- t1 && t2 \in Bool
  | T_Or: forall Gamma t1 t2,
      Gamma |- t1 \in Bool ->
      Gamma |- t2 \in Bool ->
      Gamma |- t1 || t2 \in Bool
  | T_Neg: forall Gamma t1,
      Gamma |- t1 \in Bool ->
      Gamma |- neg t1 \in Bool
  (* numbers *)
  | T_Ring : forall Gamma (n : R),
      Gamma |- n \in Ring
  | T_Add : forall Gamma t1 t2,
      Gamma |- t1 \in Ring ->
      Gamma |- t2 \in Ring ->
      Gamma |- t1 + t2 \in Ring
  | T_Mult : forall Gamma t1 t2,
      Gamma |- t1 \in Ring ->
      Gamma |- t2 \in Ring ->
      Gamma |- t1 * t2 \in Ring
  | T_If : forall Gamma c t2 t3 T0,
      Gamma |- c \in Bool ->
      Gamma |- t2 \in T0 ->
      Gamma |- t3 \in T0 ->
      Gamma |- if c then t2 else t3 \in T0
where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type : core.

(** 
    HELPER LEMMAS
*)
Lemma weakening : forall Gamma Gamma' t T,
     inclusion Gamma Gamma' ->
     Gamma  |- t \in T  ->
     Gamma' |- t \in T.
Proof.
  intros Gamma Gamma' t T H Ht.
  generalize dependent Gamma'.
  induction Ht; eauto 7 using inclusion_update.
Qed.

Lemma weakening_empty : forall Gamma t T,
     empty |- t \in T  ->
     Gamma |- t \in T.
Proof.
  intros Gamma t T.
  eapply weakening.
  discriminate.
Qed.


Lemma substitution_preserves_typing : forall Gamma x U t v T,
  (x |-> U ; Gamma) |- t \in T ->
  empty |- v \in U   ->
  Gamma |- [x:=v]t \in T.
Proof with eauto.
  intros Gamma x U t v T Ht Hv.
  generalize dependent Gamma. generalize dependent T.
  (* Proof: By induction on the term [t].  Most cases follow
     directly from the IH, with the exception of [var]
     and [abs]. These aren't automatic because we must
     reason about how the variables interact. The proofs
     of these cases are similar to the ones in STLC.
     We refer the reader to StlcProp.v for explanations. *)
  induction t; intros T Gamma H;
  (* in each case, we'll want to get at the derivation of H *)
    inversion H; clear H; subst; simpl; eauto.
  - (* var *)
    rename s into y. destruct (eqb_stringP x y); subst.
    + (* x=y *)
      rewrite update_eq in H2.
      injection H2 as H2; subst.
      apply weakening_empty.
      assumption.
    + (* x<>y *)
      apply T_Var. rewrite update_neq in H2; auto.
  - (* abs *)
    rename s into y, t into S.
    destruct (eqb_stringP x y); subst; apply T_Abs.
    + (* x=y *)
      rewrite update_shadow in H5. assumption.
    + (* x<>y *)
      apply IHt.
      rewrite update_permute; auto.
Qed.

Theorem multi_trans :
  forall (X : Type) (R : relation X) (x y z : X),
      multi R x y  ->
      multi R y z ->
      multi R x z.
Proof.
  intros X R x y z G H.
  induction G.
    - (* multi_refl *) assumption.
    - (* multi_step *)
      apply multi_step with y0. assumption.
      apply IHG. assumption.
Qed.

End STLCRingCompiler.
