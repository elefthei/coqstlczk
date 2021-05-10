Require Import Metalib.Metatheory.
From STLCZK Require Import GaloisField.
From STLCZK Require Import Stlc.
From STLCZK Require Import R1cs.
From STLCZK Require Import Ltac.

Require Import Coqprime.elliptic.ZEll.
Require Import Coq.Numbers.BinNums.
Require Import Coqprime.elliptic.GZnZ.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.ZArith.BinIntDef.
Import Z.
Require Import Coq.ZArith.BinInt.

Module Gadget(PF: GaloisField).
  Import PF.
  Include R1CS PF.
  Include Stlc PF.
  
  (** TR closure *)
  Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
      R x y ->
      multi R y z ->
      multi R x z.
  Notation " t '-->*' t' " := (multi step t t') (at level 40).

  (** TRC with step count *)
  Inductive multi_k {X: Type} (R: relation X) : nat -> relation X :=
  | multi_k_refl: forall e,
      multi_k R 0 e e
  | multi_k_trans: forall a b c n,
      R a b ->
      multi_k R n b c ->
      multi_k R (S n) a c.
  Notation " t '==>*' k t' " := (multi_k step k t t') (at level 40).

  Definition circuit_equiv(c: exp) (c': exp): Prop :=
    forall (n: Fp), forall (w: Fp),
        (<{ c' (fp n) (fp w) }> -->* <{ true }> <->
        <{ c (fp n) }> -->* <{ fp w }>). 
  Notation "a '~~' b" := (circuit_equiv a b) (at level 50).

  Definition circuit_equiv_poly(c: exp) (c': exp): Prop :=
    forall n w T,
      <{{ nil |- c n :: T }}> ->
      <{{ nil |- c' n w :: Bool }}> ->
      (<{ c' n w }> -->* <{ true }> <->
       <{ c n }> -->* <{ w }>).
  Notation "a ~= b" := (circuit_equiv_poly a b) (at level 99).

  Fixpoint normalize(e: exp) :=
    match e with
    | tm_app (tm_abs T e1) v1 =>
      open_exp_wrt_exp (normalize e1) (normalize v1)
    | tm_abs T e => tm_abs T e
    | tm_app e1 e2 => tm_app (normalize e1) (normalize e2)
    | tm_let e1 e2 =>
      open_exp_wrt_exp (normalize e2) (normalize e1)
    | tm_binop a op b =>
      tm_binop (normalize a) op (normalize b)
    | tm_eq e1 e2 =>
      tm_eq (normalize e1) (normalize e2)
    | tm_not e1 => tm_not (normalize e1)
    | tm_ifthenelse e e1 e2 =>
      tm_ifthenelse (normalize e) (normalize e1) (normalize e2)
    | tm_pair e1 e2 =>
      tm_pair (normalize e1) (normalize e2)
    | tm_proj_1 e => tm_proj_1 (normalize e)
    | tm_proj_2 e => tm_proj_2 (normalize e)
    | e => e
    end.

  Fixpoint normalizer(e: exp)(gas: nat): exp :=
    match gas with
    | 0%nat => e
    | S g' => normalizer (normalize e) g'
    end.

  Definition normalization_lemma: forall e e', (exists G, normalizer e G = e') <-> e -->* e'.
  Admitted.
  

  (** Evaluate closures *)
  
  Inductive r1cs_type: typ -> Prop :=
  | fo_field: r1cs_type <{{ Field }}>
  | fo_bool: r1cs_type <{{ Bool }}>
  | fo_pair_field: forall b,
      r1cs_type b ->
      r1cs_type <{{ Field * b }}>
  | fo_pair_bool: forall b,
      r1cs_type b ->
      r1cs_type <{{ Bool * b }}>.


  Inductive r1cs_exp: exp -> Prop :=
  | eo_field: forall f, r1cs_exp <{ fp f }>
  | eo_true: r1cs_exp <{ true }>
  | eo_false: r1cs_exp <{ false }>
  | eo_pair_field: forall b f,
      r1cs_exp b ->
      r1cs_exp <{ {fp f, b} }>
  | eo_pair_true: forall b,
      r1cs_exp b ->
      r1cs_exp <{ {true, b} }>
  | eo_pair_false: forall b,
      r1cs_exp b ->
      r1cs_exp <{ {false, b} }>.
  
  Definition fo_closure(e: exp)(args: exp): Prop :=
    forall A: typ,
      r1cs_type A ->
    <{{ nil |- args :: A }}> ->
    <{{ nil |- e :: (A -> Field) }}>.

  Require Import Coq.Vectors.VectorDef.
  Import VectorNotations.

  Fixpoint vec_to_exp_aux{n}(v: Vfp n)(b: Fp): exp :=
    match v with
    | [] => <{ fp b }>
    | h :: vs => tm_pair <{ fp b }> (vec_to_exp_aux vs h)
    end.

  Definition vec_to_exp{n}(v: Vfp (S n)): exp :=
    @Vector.caseS _ (fun n v => exp) (fun h n t => vec_to_exp_aux t h) _ v.

  Inductive exp_vec: forall n, exp -> Vfp n -> Prop :=
  | ev_field: forall f, exp_vec 1 <{ fp f }> [f]
  | ev_true: exp_vec 1 <{ true }> [1:%p]
  | ev_false: exp_vec 1 <{ false }> [0:%p]
  | ev_pair_true: forall m v t, 
      exp_vec m t v ->
      exp_vec (S m) <{ {true , t} }> (1:%p :: v)
  | ev_pair_false: forall m v t,
      exp_vec m t v ->
      exp_vec (S m) <{ {false , t} }> (0:%p :: v)
  | ev_pair_field: forall m f v t,
      exp_vec m t v ->
      exp_vec (S m) <{ {fp f, t} }> (f :: v).

  Inductive exp_typ: forall n, typ -> Vfp n -> Prop :=
  | et_field: forall f, exp_typ 1 <{{ Field }}> [f]
  | et_bool: forall f, f = 0:%p \/ f = 1:%p -> exp_typ 1 <{{ Bool }}> [f]
  | et_pair_bool: forall m v t f, 
      exp_typ m t v ->
      f = 0:%p \/ f = 1:%p ->
      exp_typ (S m) <{{ Bool * t }}> (f :: v)
  | et_pair_field: forall m f v t,
      exp_typ m t v ->
      exp_typ (S m) <{{ Field * t }}> (f :: v).

  Lemma inversion_principle_bool_bool: forall t a b,
      <{{ Datatypes.nil |- t :: Bool * Bool }}> ->
      exp_vec 2 t [a; b] ->
      ((t = <{ {true, true} }> /\ a = 1:%p /\ b = 1:%p) \/
       (t = <{ {true, false} }> /\ a = 1:%p /\ b = 0:%p) \/
       (t = <{ {false, true} }> /\ a = 0:%p /\ b = 1:%p) \/
       (t = <{ {false, false} }> /\ a = 0:%p /\ b = 0:%p)).
  Proof.
    intros t a b Ht Hv.
    invert Hv;
    devec1 v;
    invert H3; invert H2; invert Ht; invert H3; invert H5.
    - left; intuition auto.
    - right; left; intuition auto.
    - right; right; left; intuition auto.
    - right; right; right; intuition auto.
  Qed.

  Lemma inversion_principle_bool: forall t a G,
      <{{ G |- t :: Bool }}> -> exp_vec 1 t [a] ->
      ((t = <{ true }> /\ a = 1:%p) \/ (t = <{ false }> /\ a = 0:%p)).
  Proof.
    intros t a G Ht Hv.
    invert Ht; invert Hv.
    left; split; reflexivity.
    right; split; reflexivity.
  Qed.

  Lemma inversion_principle_field: forall t a G,
      <{{ G |- t :: Field }}> -> exp_vec 1 t [a] ->
      t = <{ fp a }>.
  Proof.
    intros t a G Ht Hv.
    invert Ht; invert Hv.
    reflexivity.
  Qed.

  Close Scope vector_scope.
  Import ListNotations.

  Definition cannonical
             (args: exp) (G: typing_env) (t: typ) (n: nat) (inps: Vfp (S n)) :=
    <{{ G |- args :: t }}> /\
    r1cs_type t /\
    exp_vec (S n) args inps.

  Check typing_env.
  Definition r1cs_lambda_tequiv{n i o v}(e: exp)
             (cs: @r1cs n (S i) (S o) v): Prop :=
    forall args results inps outs vars t t',
      <{{ [] |- e :: (t -> t') }}> ->
      cannonical args [] t i inps ->
      cannonical results [] t' o outs ->
      <{ e args }> -->* <{ results }> <->
      correct cs inps outs vars.
(*
  Definition r1cs_lambda_equiv{n i o v}(e: exp)
             (cs: @r1cs n (S i) (S o) v): Prop :=
    forall args results inps outs vars,
      exp_vec (S i) args inps ->
      exp_vec (S o) results outs ->
      <{ e args }> -->* <{ results }> <->
      correct cs inps outs vars.
  *)
  Notation "e <=*=> r" := (r1cs_lambda_tequiv e r) (at level 50).

  Ltac solve_stlc :=
    repeat match goal with
           | [ |- step (tm_eq ?a ?b) _ ] =>
             apply step_eq_refl || apply step_eq_cog_1 || apply step_eq_cog_2
           | [ |- step (tm_binop _ op_mul _) _ ] => apply step_mul_const
           | [ |- step (tm_app ((tm_abs _ _))  _) _] => eapply step_beta
           | [ H: step ?a ?b |- ?g ] => inversion H; subst; clear H
           | [ H: ?a -->* ?b |- _ ] => inversion H; subst; clear H
           | [ |- Is_true _ ] => idtac "is_true"; constructor
           | [ H: ?x `notin` ?L |- lc_exp <{ \_: _, _ }> ] =>
             idtac "intro binders"; apply (lc_tm_abs (AtomSetImpl.add ?x ?L)); intros
           | [ |- lc_exp <{ \_ : _, _ }> ] =>
             idtac "empty binders"; apply (lc_tm_abs empty); intros
           | [ |- lc_exp _ ] => idtac "lc_exp"; constructor
           | [ H: context[open_exp_wrt_exp _ _] |- _] => cbn in H
           | [ |- context[open_exp_wrt_exp _ _] ] => cbn
           | [ H: ?a |- ?a ] => exact H
           | [ |- _ -->* _ ] => idtac "forward" ; econstructor; fail
           end.

End Gadget.     
