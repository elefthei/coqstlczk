From STLCZK Require Import Stlc_Manual.

Require Import Metalib.Metatheory.
From STLCZK Require Import GaloisField.

Module Gadgets (Import M: StlcNat).

  Definition X : atom := fresh nil.
  Definition Y : atom := fresh (X :: nil).
  
  (** Notation on Stlc_Ott *)
  Coercion tm_var_f: expvar >-> exp.
  Coercion const_field: nat >-> constant.
  Coercion tm_constant: constant >-> exp.
  
  Declare Custom Entry stlc_ty.
  Declare Custom Entry stlc.
  Notation "<{ e }>" := e (e custom stlc at level 99).
  Notation "<{{ e }}>" := e (e custom stlc_ty at level 99).
  Notation "( x )" := x (in custom stlc, x at level 99).
  Notation "( x )" := x (in custom stlc_ty, x at level 99).
  Notation "x" := x (in custom stlc at level 0, x constr at level 0).
  Notation "x" := x (in custom stlc_ty at level 0, x constr at level 0).
  Notation "S -> T" := (ty_arrow S T) (in custom stlc_ty at level 50, right associativity).
  Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
  Notation "\_ : t , y" :=
    (tm_abs t y) (in custom stlc at level 90,
                     t custom stlc_ty at level 99,
                     y custom stlc at level 99,
                     left associativity).
  Notation "# n" := (tm_var_b n) (in custom stlc at level 1).
  Notation "{ x }" := x (in custom stlc at level 1, x constr).

  Notation "'Field'" := ty_field (in custom stlc_ty at level 0).
  Notation "'Bool'" := ty_bool (in custom stlc_ty at level 0).

  Notation "x + y" := (tm_binop x tm_add y) (in custom stlc at level 2,
                                                left associativity).
  Notation "x - y" := (tm_binop x tm_sub y) (in custom stlc at level 2,
                                                left associativity).

  Notation "x * y" := (tm_binop x tm_mul y) (in custom stlc at level 1,
                                                left associativity).
  Notation "x / y" := (tm_binop x tm_div y) (in custom stlc at level 1,
                                                left associativity).
  Notation "x && y" := (tm_binop x tm_and y) (in custom stlc at level 2,
                                                 left associativity).
  Notation "x || y" := (tm_binop x tm_or y) (in custom stlc at level 2,
                                               left associativity).
  Notation "x == y" := (tm_eq x y) (in custom stlc at level 1,
                                       left associativity).
  Notation "! x " := (tm_not x) (in custom stlc at level 1).


  Notation "'if' x 'then' y 'else' z" :=
    (tm_ifthenelse x y z) (in custom stlc at level 89,
                              x custom stlc at level 99,
                              y custom stlc at level 99,
                              z custom stlc at level 99,
                              left associativity).

  Notation "'let _' '=' t1 'in' t2" :=
    (tm_let t1 t2) (in custom stlc at level 0).

  (** TR closure *)
  Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
      R x y ->
      multi R y z ->
      multi R x z.

  Notation " t '-->*' t' " := (multi step t t') (at level 40).
  
  Definition circuit_equiv(c: exp) (c': exp): Prop :=
    forall (n: nat), exists (w: nat),
        <{ c' n w }> -->* const_true <->
        <{ c n }> -->* w.
  
  Notation "a '~' b" := (circuit_equiv a b) (at level 50).

  (** Example *)
  Definition div :=
    <{ \_: Field, (1 / #1) }>.

  Definition div_check :=
    <{ \_: Field,
           <{ \_: Field,
                  #1 * #2 == 1 }>
     }>.

  Ltac invert H := inversion H; subst; clear H.
  Theorem div_gadget_proof: div ~ div_check.
  Proof.
    unfold circuit_equiv, div, div_check.
    intros.
    eexists.
    split.
    - (* -> *) induction n; intro H.
      + invert H.
        invert H0.
        invert H5.
        invert H2.
        invert H3.
        invert H6.
        invert H7.
        
        inversion H0; subst.
        inversion H4. subst.
        * apply step_beta; try constructor.
          
   constructor. admit.
        eauto 12.
    - 
  Admitted.
      
