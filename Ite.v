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

Module IteGadget(PF: GaloisField).
  Import PF.
  Include Gadget PF.
  Import VectorNotations.

  
  (** Example 1: Division *)
  Check tm_cast.
  Definition ite :=
    <{ \_: Field,
           \_: Field,
               \_: Field,
                   if cast #0 then #1 else #2
     }>. 

  Definition ite_check :=
    <[ { (1i[0]) * (1i[2] + -1i[1]) == (1o[0] + -1i[0]) } ]>.

  Ltac solve_stlc :=
    repeat match goal with
           | [ |- step (tm_eq ?a ?b) _ ] =>
             apply step_eq_refl || apply step_eq_cog_1 || apply step_eq_cog_2
           | [ |- step (tm_binop _ op_mul _) _ ] => apply step_mul_const
           | [ |- step (tm_app ((tm_abs _ _))  _) _] => eapply step_beta
           | [ H: step ?a ?b |- ?g ] => invert_log_solved H g
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
  
  Lemma eq_proj_fp: forall a b, <{ fp a }> = <{ fp b }> -> a = b.
  Proof.
    intros.
    invert H.
    reflexivity.
  Qed.

   Ltac exists_inverter :=
    repeat match goal with
           | [H': exists a, _ |- _] => inversion H' as [?a ?H2]; clear H'        
    end.
  
   (** Second equivalence proof over r1cs *)
  Theorem ite_equiv_r1cs:
    ite <=*=> ite_check.
  Proof.
    unfold ite_check, r1cs_equiv, ite, correct, correct_lt.
    intros.
    cbn in vars.  
    unfold vec_to_exp.
    unfold Vfp in *.
    (** Need to get inputs: Vector.t Fp 1 => [ p: Fp ] *)
    pose proof (vec3_proj inputs).
    pose proof (vec1_proj outputs).
    exists_inverter.
    pose proof (pKfth p_prime) as HpK.
    invert HpK.
    invert F_R.
    split; intro H.
    - (** evaluate the r1cs term *)
      constructor; cbn.
      (** evaluate the lambda term *)
      solve_stlc.
      constructor.
    - cbn in H.
      invert H.
      
      rewrite Rmul_1_l.
      rewrite Rmul_comm.
      rewrite Finv_l.
      apply zirr.
      cbn.
      rewrite Z.sub_diag.
      reflexivity.

      apply neq_stlc_fp in H9.
      exact H9.

      constructor.
    - (** evaluate the lambda term *)
      econstructor.
      apply step_beta; try constructor.
      apply (lc_tm_abs empty); intros; solve_stlc.
      cbn.
      econstructor.
      (** single step *)
      apply step_div_const.
      
      (** evaluate the r1cs term *)
      invert Hprem.
      rename H6 into Hr1cs.
      do 2 rewrite Rmul_1_l in Hr1cs.

      destruct (eq_field (hd inputs) 0:%p); solve_stlc.
      + (** hd inputs = 0 *)
        rewrite e in Hr1cs.
        rewrite Rmul_comm in Hr1cs.
        rewrite fp_mul_zero_l in Hr1cs.
        pose proof pk_sub_wrap.
        contradiction.
      + (** hd inputs <> 0 *)
        intro.
        invert H3.
        contradiction.
      (** big-step *)
      + invert Hprem.
        do 2 rewrite Rmul_1_l in H6.
        

 
        rewrite Rsub_def in Hr1cs.
        
        invert Hr1cs.
        cbn in H4.
        apply Z.lt_gt in H1.
        
        rewrite Zdiv.Z_mod_zero_opp in H4.
        
        
        apply Zdiv.Z_mod_zero_opp

        



        rewrite H1 in H2.
        apply H in H2.
        
        cbn in H2.
        rewrite H1 in H2.
        inversion H2.
        destruct (p_prime).
        apply Z.lt_gt in H6.        
        apply gt_relax.
        exact H6.
      + (** hd inputs = Z.pos z *)
        admit.
      + admit.

        Unshelve.
        exact empty.
        
        rewrite H1 in H2.
      apply multi_refl.
      rewrite Fdiv_def in Hr1cs.
      
      econstructor; solve_stlc.
      solve_stlc.
      Search Z.sub.
      Search modulo.
      cbn.
      destruct p.
      Print inv.
      rewrite Z.mul_assoc.
      simple inversion Hlambda.
      rewrite H in H0.
      remember (pkmul 1 :%p (pkinv {| val := inp; inZnZ := inZnZ |})) as out_inv.
      remember ({| val := out; inZnZ := inZnZ0 |}) as out_fp.
      
      unfold pK in out_inv.
      
  Admitted.

End DivGadgets.     
