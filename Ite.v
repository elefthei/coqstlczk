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

From Coq Require Import Ring.
From Coq Require Import Field.
Require Import Coq.micromega.Lia.

Module IteGadget(PF: GaloisField).
  Import PF.
  Include Gadget PF.
  Import VectorNotations.

  (** Example 1: Division *)
  Definition ite :=
    <{ \_: Field * Field * Field,
           if to_bool (fst #0) then fst (snd #0) else snd (snd #0)
     }>. 

  Definition ite_check :=
    <[ { (1i[0]) * (1i[2] + -1i[1]) == (1o[0] + -1i[1]) } ]>.

   (** Second equivalence proof over r1cs *)
  Theorem ite_equiv_r1cs:
    ite <=*=> ite_check.
  Proof.
    unfold ite_check, r1cs_equiv, ite.
    intros.
    cbn in vars.  
    unfold vec_to_exp.
    unfold Vfp in *.
    (** Need to get inputs: Vector.t Fp 1 => [ p: Fp ] *)
    pose proof (vec3_proj inputs).
    pose proof (vec1_proj outputs).
    exists_inverter.
    subst.
    cbn.
    destruct (FTH).
    invert F_R.
    split; intro H.
    - (** evaluate the r1cs term *)
      constructor; cbn.
      ring_simplify.
      repeat rewrite Rmul_1_l.
      destruct (eq_field a0 1:%p) eqn:Ea0.
      + rewrite e.
        repeat rewrite Rmul_1_l.
        rewrite <- Ropp_pkmul.
        
        rewrite Rsub_def.
        replace (pkopp (pkopp b)) with b by ring.
        (** ((c - b) - a) + b *)
        replace (pkplus (pksub (pkplus c (pkopp b)) a) b) with (pksub c a) by ring.
        solve_stlc.
        admit.
        replace (pksub a a) with (0:%p) by ring.
        reflexivity.
      + 
    - cbn in H.
      invert H.
      cbn.
      econstructor.
      beta.
      cbn.
      econstructor.
      apply step_if_cog; repeat econstructor.
      app
      destruct (eq_bool <{ cast fp a0 }>).
      econstructor.
      econstructor.
      
      apply multi_step with
          (y:=              
             <{
               if cast (<{ fp a0 }>)
               then <{ fp b }>
               else <{ fp c }> }>).
      
                          econstructor.
      cbn i
      beta.
      
      beta.
      
      beta (Metatheory.add x
        econstructor.
        econstructor.
        econstructor.
      + repeat econstructor.
      + econstructor.
        cbn.
      solve_stlc.
      invert H2.
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

End IteGadget.     
