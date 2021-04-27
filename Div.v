Require Import Metalib.Metatheory.
From STLCZK Require Import Stlc.
From STLCZK Require Import Gadgets.
From STLCZK Require Import R1cs.
From STLCZK Require Import GaloisField.
From STLCZK Require Import Ltac.

Require Import Coqprime.elliptic.ZEll.
Require Import Coq.Numbers.BinNums.
Require Import Coqprime.elliptic.GZnZ.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.ZArith.BinIntDef.
Import Z.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Vectors.VectorDef.
From Coq Require Import Field.


Module DivGadget(PF: GaloisField).
  Import PF.
  Include Gadget PF.
  Import VectorNotations.

  (** Example 1: Division *)
  Definition div :=
    <{ \_: Field, (F1 / #0) }>.

  Definition div_fp_check :=
    <{ \_: Field,
           (\_: Field,
                (#0 * #1) == F1)
     }>.

  Definition div_check :=
    <[ { (1i[0]) * (1o[0]) == ([1]) } ]>.

  (** Second equivalence proof over r1cs *)
  Theorem div_equiv_r1cs:
      div <=*=> div_check.
  Proof.
    unfold div_check, r1cs_equiv, div, div_check, correct, correct_lt.
    intros.
    cbn in vars.  
    unfold vec_to_exp.
    unfold Vfp in *.
    (** Need to get inputs: Vector.t Fp 1 => [ p: Fp ] *)
    pose proof (vec1_proj inputs).
    pose proof (vec1_proj outputs).
    exists_inverter.
    subst.
    cbn.
    destruct (pKfth p_prime).
    invert F_R.
    split; intro Hprem.    
    - (** evaluate the r1cs term *)
      constructor.   
      repeat rewrite Rmul_1_l.
      (** evaluate the lambda term *)
      solve_stlc.
      rewrite Fdiv_def.
      rewrite Rmul_1_l.
      rewrite neq_stlc_fp in H5.
      rewrite Rmul_comm.
      rewrite (Finv_l).
      rewrite Rsub_def.
      rewrite Ropp_def.
      reflexivity.
      exact H5.
      constructor.
    - (** evaluate the r1cs term *)
      invert Hprem.
      repeat rewrite Rmul_1_l in H2.
      econstructor.
      beta.
      cbn.
      econstructor.
      apply step_div_const.
      apply neq_stlc_fp.
      intro.
      rewrite H in H2.
      rewrite Rmul_comm in H2.
      rewrite Rmul_zero_l in H2.
      rewrite Rsub_def in H2.
      rewrite Radd_0_l in H2.
      apply  Ropp_1_not_0 in H2.
      contradiction.
      rewrite Fdiv_def.
      rewrite Rmul_1_l.
      apply Rsub_mul_1_inv in H2.
      rewrite H2.
      apply multi_refl.
      Unshelve.
      exact empty.
  Qed.

End DivGadget.     
