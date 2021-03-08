Require Import Metalib.Metatheory.
From STLCZK Require Import Stlc.

Require Import Coqprime.elliptic.ZEll.
Require Import Coq.Numbers.BinNums.

Module Gadgets.
  Import Stlc_Fp.
  
  Definition X : atom := fresh nil.
  Definition Y : atom := fresh (X :: nil).
  
  (** Notation on Stlc_Ott *)
  
  Coercion tm_var_f: expvar >-> exp.
  Coercion const_field: Fp >-> constant.
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

  Notation "x + y" := (tm_binop x op_add y) (in custom stlc at level 2,
                                                left associativity).
  Notation "x - y" := (tm_binop x op_sub y) (in custom stlc at level 2,
                                                left associativity).

  Notation "x * y" := (tm_binop x op_mul y) (in custom stlc at level 1,
                                                left associativity).
  Notation "x / y" := (tm_binop x op_div y) (in custom stlc at level 1,
                                                left associativity).
  Notation "x && y" := (tm_binop x op_and y) (in custom stlc at level 2,
                                                 left associativity).
  Notation "x || y" := (tm_binop x op_or y) (in custom stlc at level 2,
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

  (** Example 1: Division *)
  Definition div :=
    <{ \_: Field, ({const_field fp_one} / #0) }>.

  Definition div_applied(c: Fp) :=
    <{ div ({const_field c}) }>.
  Definition foo(c: Fp) :=
    match div_applied c with
    | tm_app ((tm_abs _ e1)) v => true
    | _ => false
    end.

  Compute foo fp_one.
  (** step (tm_app  ( (tm_abs T e1) )  v2)  (open_exp_wrt_exp  e1   v2 ) *)
  
  Print div_applied. 
  Definition div_check :=
    <{ \_: Field,
           (\_: Field,
                #0 * #1 == ({const_field fp_one}))
     }>.

  Definition circuit_equiv1(c: exp) (c': exp): Prop :=
    forall (n: Fp), exists (ans: Fp),
        typing nil c (ty_arrow ty_field ty_field) /\
        typing nil c' (ty_arrow ty_field (ty_arrow ty_field ty_bool)) ->
        (<{ c' n ans }> -->* const_true <->
        <{ c n }> -->* ans).
   
  Notation "a '~' b" := (circuit_equiv1 a b) (at level 50).

  Definition circuit_equiv2(c: exp) (c': exp): Prop :=
    forall (n: Fp), forall (ans: Fp),
        <{ c' n ans }> -->* const_true <->
        <{ c n }> -->* ans.
   
  Notation "a '~~' b" := (circuit_equiv2 a b) (at level 50).

  
  Ltac invert H := inversion H; subst; clear H.
  Ltac invert_log_solved H g := 
    solve [inversion H; fail; idtac "solved"] || invert H.

  Ltac solve_stlc :=
    repeat match goal with
           | [ H: <{ (open_exp_wrt_exp _ _) }> -->* _ |- _ ] => idtac "cbn"; cbn in H
           | [ H: <{ (open_exp_wrt_exp _ _) _ }> -->* _ |- _ ] => idtac "cbn"; cbn in H        
           | [ H: step ?a ?b |- ?g ] => idtac "Inverting" a "-->" b "for" g; invert_log_solved H g
           | [ H: ?a -->* ?b |- _ ] => idtac "Big-step" a "-->*" b; inversion H; subst; clear H
           end.
  
  (** This is not complete over all possible witnesses, but still passes *)
  Theorem div_gadget_equiv_1_noncomplete: div ~ div_check.
  Proof.
    unfold circuit_equiv1, div, div_check.
    intros.
    destruct n as (n', n_mod) eqn:N.
    induction n'.
    - exists fp_zero.
      intros [H_tyc H_tyc'].
      split; intro H; solve_stlc.
      unfold fp_zero, pkO, GZnZ.zero in *.
      apply eq_fp in H5.
      cbn in H5.
      intro H.
      solve_stlc.

      intro H. solve_stlc.
      solve_stlc.
      invert H.
      invert H0.
      invert H5.
      invert H6.
      invert H7.

      solve_stlc.
      invert H1.
      invert H.
      solve_stlc.

      invert H10.
      
      cbn in H1.
      intro H; solve_stlc.
  Qed.

  
  Theorem div_gadget_equiv_2_complete: div ~~ div_check.
  Proof.
    unfold circuit_equiv2, div, div_check.
    intros.    
    split; intro H; solve_stlc.
  Qed.
  
  (** This is complete over all possible witnesses, 
      how to make this accepted but the above not ? *)
  Theorem div_gadget_equiv_1_complete: div ~ div_check.
  Proof.
    unfold circuit_equiv1, div, div_check.
    intros.
    destruct n as (n', Hmod_n) eqn:F.
    induction n'.
    - exists fp_zero.
      split; intro H; solve_stlc.
    - exists (pkdiv fp_one n).
      split; intro H; solve_stlc.
    - exists (pkdiv (pkopp fp_one) n).
      split; intro H; solve_stlc.
  Qed.

  Fixpoint constant_to_boolnat(c: constant) : Fp :=
    match c with
    | const_true => fp_one
    | const_false => fp_zero
    | const_field (GZnZ.mkznz _ Z0 _) => fp_zero
    | const_field (GZnZ.mkznz _ _ _) => fp_one
    end.
  
  (** Example 2: Conditional *)
  Definition ite(c: constant):=
    <{ \_: Field,
           (\_: Field,
                if c then #2 else #3
           )
     }>.
  
  Definition ite_check(c: constant) :=
    <{ \_: Field,
           (\_: Field,
                (\_: Field,
                     (#3 == #1 + {constant_to_boolnat c} * (#2 - #1))
                )
           )
     }>.

  Theorem ite_equiv_1: forall c, ite c ~ ite_check c.
  Proof.
    intros.
    unfold circuit_equiv1, ite, ite_check.
    destruct 0; induction 0; exists fp_zero; split; intro H; solve.
  Qed.

  Theorem ite_equiv_2: forall c, ite c ~~ ite_check c.
  Proof.
    intros.
    unfold circuit_equiv2, ite, ite_check.
    intros; split; intro H; solve.
  Qed.

End Gadgets.     
