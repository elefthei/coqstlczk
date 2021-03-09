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

  Include Stlc_Fp.

  Definition X : atom := fresh nil.
  Definition Y : atom := fresh (X :: nil).
  
  (** Notation on Stlc_Ott *)
  
  Coercion tm_var_f: expvar >-> exp.
  Coercion tm_constant: constant >-> exp.
  
  Declare Custom Entry stlc_ty.
  Declare Custom Entry stlc.
  Notation "'fp' n" := (const_field n) (in custom stlc at level 0).
  Notation "'F0'" := (const_field fp_zero) (in custom stlc at level 0).
  Notation "'F1'" := (const_field fp_one) (in custom stlc at level 0).
  Notation "'true'" := (const_true) (in custom stlc at level 0).
  Notation "'false'" := (const_false) (in custom stlc at level 0).
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
                     y custom stlc at level 99,
                     left associativity).
  Notation "# n" := (tm_var_b n%nat) (in custom stlc at level 1).
  Notation "{ x }" := x (in custom stlc at level 1, x constr).

  Notation "S -> T" := (ty_arrow S T) (in custom stlc_ty at level 0, right associativity).
  Notation "Gamma '|-' t '::' T" := (typing Gamma t T) (in custom stlc_ty at level 40, t custom stlc, T custom stlc_ty at level 1).
                                                                       
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
    <{ \_: Field, (F1 / #0) }>.

  Definition div_check :=
    <{ \_: Field,
           (\_: Field,
                (#0 * #1) == F1)
     }>.


  Definition circuit_equiv(c: exp) (c': exp): Prop :=
    forall (n: Fp), forall (w: Fp),
        <{{ nil |- c :: Field -> Field }}> ->
        <{{ nil |- c' :: Field -> Field -> Bool }}> ->
        (<{ c' (fp n) (fp w) }> -->* <{ true }> <->
        <{ c (fp n) }> -->* <{ fp w }>).
   
  Notation "a '~~' b" := (circuit_equiv a b) (at level 50).
  
  Ltac invert H := inversion H; subst; clear H.
  Ltac invert_log_solved H g := 
    solve [inversion H; fail; idtac "solved"] || invert H.

  Ltac solve_stlc :=
    repeat match goal with
           | [ H: <{ (open_exp_wrt_exp _ _) }> -->* _ |- _ ] => idtac "cbn"; cbn in H
           | [ H: <{ (open_exp_wrt_exp _ _) _ }> -->* _ |- _ ] => idtac "cbn"; cbn in H        
           | [ H: step ?a ?b |- ?g ] => invert_log_solved H g
           | [ H: ?a -->* ?b |- _ ] => inversion H; subst; clear H
           end.

  Lemma neq_const: forall a b, <{ fp a }> <> <{ fp b }> -> a <> b.
  Proof.
    intros.
    destruct (eq_fp a b).
    - subst. contradiction.
    - assumption.
  Qed.

  Require Import Coq.setoid_ring.Field_theory.
  Require Import Coq.ZArith.BinInt.
  Print ring_theory.

  Lemma fp_mul_div_n0 : forall n w, n <> fp_zero ->
                             pkdiv (pkmul w n) n = w.
  Proof.
    intros.
    pose proof (pKfth p_prime) as FT.
    invert FT.
    rewrite Fdiv_def.
    invert F_R.
    rewrite <- Rmul_assoc.
    apply Finv_l in H.
    replace (pkmul n (pkinv n)) with (pkmul (pkinv n) n) by (apply Rmul_comm).
    rewrite H.
    rewrite <- Rmul_comm.
    rewrite Rmul_1_l.
    reflexivity.
  Qed.

  Lemma neq_stlc_fp: forall n w, <{ fp n }> <> <{ fp w }> <-> n <> w.
  Proof.
    intro n.
    destruct n as (n', n_mod).
    induction n'; split; intros.
    - intro. invert H0; contradiction.
    - intro. invert H0; contradiction.
    - intro. invert H0; contradiction.
    - intro. invert H0; contradiction.
    - intro. invert H0; contradiction.
    - intro. invert H0; contradiction.
  Qed.

  (** This is not complete over all possible witnesses, but still passes *)
  Theorem div_gadget_equiv: div ~~ div_check.
  Proof.
    unfold circuit_equiv, div, div_check.
    intros n w Hty Hty'.
    split; intro H; solve_stlc.
    - econstructor.
      eapply step_beta; repeat constructor.
      + econstructor. intros. cbn.
        constructor. constructor. constructor.
      + cbn.
        destruct (eq_fp n fp_zero).
        * subst.
          unfold pkmul in H9.
          invert H9.
          rewrite Zmult_comm in H0.
          simpl in *.
          pose proof (p_prime).
          invert H.
          rewrite Z.mod_0_l in H0.
          rewrite Z.mod_1_l in H0.
          invert H0.
          assumption.
          intro.
          rewrite H in H1.
          invert H1.
        * econstructor.
          eapply step_div_const.
          intro.
          invert H.
          contradiction.
          rewrite fp_mul_div_n0.         
          eapply multi_refl.
          assumption.
    - econstructor.      
      eapply step_app_1. repeat constructor.      
      eapply step_beta. repeat constructor.
      econstructor.
      intros.
      cbn.
      econstructor.
      intros.
      cbn.
      repeat constructor.
      repeat constructor.
      cbn.
      econstructor.
    
      eapply step_beta; repeat constructor.
      econstructor.
      intros.
      cbn.      
      repeat constructor.
      cbn.
      econstructor.
      eapply step_eq_cog_1. repeat constructor.
      eapply step_mul_const.
      pose proof (pKfth p_prime) as FT.
      invert FT.
      invert F_R.
      rewrite Fdiv_def.
      rewrite <- Rmul_assoc.
      rewrite neq_stlc_fp in H5.
      apply Finv_l in H5.
      rewrite H5.
      rewrite Rmul_1_l.
      econstructor.
      eapply step_eq_refl.
      apply multi_refl.
      Unshelve.
      (** Some atoms are left as holes! How to specify? *)
  Admitted.
 
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

  repeat match goal with
               | [ _ |- _ -->* _ ] => econstructor
               | [ _ |- step <{ (\_: ?F, _) _ }>  _ => idtac "beta"; eapply step_beta
               | [ _
End Gadgets.     
