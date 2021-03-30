Require Import Metalib.Metatheory.
From STLCZK Require Import Stlc.

Require Import Coqprime.elliptic.ZEll.
Require Import Coq.Numbers.BinNums.
Require Import Coqprime.elliptic.GZnZ.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.ZArith.BinIntDef.
Import Z.
Require Import Coq.ZArith.BinInt.

Module Gadgets.
  Include GaloisField.
  Include Stlc_Fp.

  (** Notation on Stlc_Ott *)
  Coercion tm_var_f: expvar >-> exp.
  Coercion tm_constant: constant >-> exp.
  
  Declare Custom Entry stlc_ty.
  Declare Custom Entry stlc.
  Notation "'fp' n" := (const_field n) (in custom stlc at level 0).
  Notation "'fb' b" := (const_bool b) (in custom stlc at level 0).
  Notation "'F0'" := (const_field 0:%p) (in custom stlc at level 0).
  Notation "'F1'" := (const_field 1:%p) (in custom stlc at level 0).
  Notation "'true'" := (const_bool true) (in custom stlc at level 0).
  Notation "'false'" := (const_bool false) (in custom stlc at level 0).
  Notation "<{ e }>" := e (e custom stlc at level 99).
  Notation "<{{ e }}>" := e (e custom stlc_ty at level 99).
  Notation "( x )" := x (in custom stlc, x at level 99).
  Notation "( x )" := x (in custom stlc_ty, x at level 99).
  Notation "x" := x (in custom stlc at level 0, x constr at level 0).
  Notation "x" := x (in custom stlc_ty at level 0, x constr at level 0).  
  Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
  Notation "\_ : t , y" :=
    (tm_abs t y) (in custom stlc at level 90,
                     t custom stlc_ty at level 99,
                     y custom stlc at level 80,
                     left associativity).
  Notation "# n" := (tm_var_b n%nat) (in custom stlc at level 0).
  Notation "{ x }" := x (in custom stlc at level 1, x constr).
  Notation "S -> T" := (ty_arrow S T) (in custom stlc_ty at level 2, right associativity).
  Notation "Gamma '|-' t '::' T" := (typing Gamma t T) (in custom stlc_ty at level 40, t custom stlc, T custom stlc_ty at level 1).
  Notation "'Field'" := ty_field (in custom stlc_ty at level 0).
  Notation "'Bool'" := ty_bool (in custom stlc_ty at level 0).
  Notation "a * b" := (ty_prod a b) (in custom stlc_ty at level 1, left associativity).
  Notation "x + y" := (tm_binop x op_add y) (in custom stlc at level 2,
                                                left associativity).
  Notation "x - y" := (tm_binop x op_sub y) (in custom stlc at level 2,
                                                left associativity).
  Notation "x * y" := (tm_binop x op_mul y) (in custom stlc at level 1,
                                                left associativity).
  Notation "x / y" := (tm_binop x op_div y) (in custom stlc at level 1,
                                                left associativity).
  Notation "x && y" := (tm_binop x op_and y) (in custom stlc at level 4,
                                                 left associativity).
  Notation "x || y" := (tm_binop x op_or y) (in custom stlc at level 4,
                                               left associativity).
  Notation "x == y" := (tm_eq x y) (in custom stlc at level 3,
                                       left associativity).
  Notation "! x " := (tm_not x) (in custom stlc at level 3).
  Notation "'if' x 'then' y 'else' z" :=
    (tm_ifthenelse x y z) (in custom stlc at level 89,
                              x custom stlc at level 99,
                              y custom stlc at level 99,
                              z custom stlc at level 99,
                              left associativity).
  Notation "'let' t1 'in' t2" :=
    (tm_let t1 t2) (in custom stlc at level 88,
                       t1 custom stlc at level 99,
                       t2 custom stlc at level 99,
                   left associativity).
  Notation "'{' a ',' b '}'" := (tm_pair a b) (in custom stlc at level 5, left associativity).
  Notation "'fst' a" := (tm_proj_1 a) (in custom stlc at level 5).
  Notation "'snd' a" := (tm_proj_2 a) (in custom stlc at level 5).
  
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

  Notation " t '-' k '->*' t' " := (multi_k step t t') (at level 40).

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

  Theorem normalize_bigstep: forall e v, e-->*v -> normalize e -->* v.
    induction 0; cbn; auto; intros.
    - invert H; cbn.
      + apply multi_refl.
      +
  Admitted.
       
End Gadgets.     
