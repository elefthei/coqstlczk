Require Import Metalib.Metatheory.
From STLCZK Require Import GaloisField.
From STLCZK Require Import Stlc.
From STLCZK Require Import R1cs.

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
  Notation " t '-' k '->*' t' " := (multi_k step k t t') (at level 40).

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

  (** Evaluate closures *)
  (**
  Inductive first_order_type: typ -> Prop :=
  | fo_field: first_order_type <{{ Field }}>
  | fo_pair: forall a b,
      first_order_type a ->
      first_order_type b ->
      first_order_type <{{ a * b }}>.
                       
  Definition fo_closure(e: exp)(args: exp): Prop :=
    forall A: typ,
      first_order_type A ->
    <{{ nil |- args :: A }}> ->
    <{{ nil |- e :: (A -> Field) }}>.

  (** Don't need the state monad yet *)
  Record EvalState :=
    mkEvalState {
        vars: list Fp
      }.

  Import MonadNotation.
  Variable m : Type -> Type.
  
  Fixpoint eval_closure
             (e: exp)
             (args: exp)
             {Hc: fo_closure e args}
             {MM: Monad m}
             {MS: MonadState EvalState m} : m exp.
  Admitted.
   *)

  Require Import Coq.Vectors.VectorDef.
  Import VectorNotations.

  Fixpoint vec_to_exp_aux{n}(v: Vfp n)(h: Fp): exp :=
    match v with
    | [] => <{ fp h }>
    | b :: vs => tm_pair <{ fp h }> (vec_to_exp_aux vs b)      
    end.

  Definition vec_to_exp{n}(v: Vfp (S n)): exp :=
    @Vector.caseS _ (fun n v => exp) (fun h n t => vec_to_exp_aux t h) _ v.

  (** Example *)
  Eval cbn in vec_to_exp [1:%p; 2:%p; 6:%p].  

  Definition r1cs_equiv{n i o v}(e: exp)(cs: @r1cs n (S i) (S o) v): Prop :=
    forall (inputs: Vfp (S i))(outputs: Vfp (S o))(vars: Vfp v),
      let args := vec_to_exp inputs in
      let results := vec_to_exp outputs in
      <{ e args }> -->* <{ results }> <-> correct cs inputs outputs vars.

  Notation "e <=*=> r" := (r1cs_equiv e r) (at level 50).

End Gadget.     
