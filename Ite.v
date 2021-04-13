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

Module Foo.
  From Coq Require Import Ring.
  Open Scope bool_scope.

  Lemma boolSRth : semi_ring_theory false true orb andb (@eq bool).
  Proof.
    constructor.
    exact Bool.orb_false_l.
    exact Bool.orb_comm.
    exact Bool.orb_assoc.
    exact Bool.andb_true_l.
    exact Bool.andb_false_l.
    exact Bool.andb_comm.
    exact Bool.andb_assoc.
    exact Bool.andb_orb_distrib_l.
  Qed.

  Add Ring boolsr : boolSRth.

  Lemma ors a b : a || b = b || a.
  Proof. ring. Qed.
End Foo.

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

   Ltac beta :=
     eapply step_beta;
     solve [
         econstructor
         | repeat match goal with
                | [ H: ?x `notin` ?L |- lc_exp <{ \_: _, _ }> ] =>
                  idtac "intro binders"; apply (lc_tm_abs (AtomSetImpl.add ?x ?L)); intros
                | [ |- lc_exp <{ \_ : _, _ }> ] =>
                  idtac "empty binders"; apply (lc_tm_abs empty); intros
                  end
         | repeat econstructor]; repeat econstructor.

   Print ring_theory.
   Print PF.FTH.
   Definition RTH: ring_theory Fp _ _ _ _ _ _
     
   Add Ring fpr: FTH.
   Lemma Ropp_pkmul: forall (a: Fp),
       pkopp a = pkmul (-1):%p a.
   Proof.
     intros.
     ring.
     ring_simplify.
     ring Fp.
     unfold pkopp, GZnZ.opp, pkmul, GZnZ.mul.
     cbn.
     destruct a.
     cbn.
     apply zirr.
     rewrite Zdiv.Zmult_mod_idemp_l.
     replace (-1 * val) with (-val) by lia.
     reflexivity.
   Qed.
   
   Check zirr.
   Require Import Coq.micromega.Lra.
   Require Import Ring.

   Definition fp_ring := ring_theory fp0 fp1 fpplus fpmul fpsub.
   Check fp_ring.
   Print ring_theory.
   Definition fp_ring_theory: ring_theory.
     
   Add Ring Fp: (ring_theory fp0 fp1 fpplus fpmul
                             fpsub (pkopp (p:=p)) eq).

   Lemma Rplus_opp: forall a b,
       pkopp (pkplus b a) = pkplus (pkopp b) (@pkopp p a).
   Proof.
     intros.
     pose proof (pKfth p_prime) as HpK.
     invert HpK.
     Add Ring Fp: (ring_theory (pkO p) (pkI p) (pkplus (p:=p)) (pkmul (p:=p)) 
                               (pksub (p:=p)) (pkopp (p:=p)) eq).

     pkplus pkmul pkI (pkO p) (pkopp (p:=p)) eq. [ c1 ...cn ].
     Add Ring Fp: F_R.
     Search zify.
     ring
     invert F_R.
   
     unfold pkopp, GZnZ.opp.
     apply zirr.
     cbn.
     
     rewrite <- Zdiv.Zplus_mod.
     rewrite <- Z.sub_0_l.     
     rewrite Zdiv.Zminus_mod_idemp_r.
     rewrite Z.sub_0_l.
     rewrite Z.opp_add_distr.
     reflexivity.
   Qed.

   
   Lemma Rsub_add_distr: forall a b c,
       pksub (pkplus b c) (pkplus b a) = @pksub p c a.
   Proof.
     intros.
     pose proof (pKfth p_prime) as HpK.
     invert HpK.
     invert F_R.
     do 2 rewrite Rsub_def.
     rewrite <- Radd_assoc.
     rewr
   
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
    pose proof (pKfth p_prime) as HpK.
    invert HpK.
    invert F_R.
    split; intro H.
    - (** evaluate the r1cs term *)
      constructor; cbn; repeat rewrite Rmul_1_l.
      destruct (eq_field a0 1:%p) eqn:Ea0.
      rewrite e.
      rewrite Rmul_1_l.
      
      replace (pksub (pkplus (pkmul (-1) :%p b) c) (pkplus (pkmul (-1) :%p b) a)) with
          (pksub (
      
      (** evaluate the lambda term *)      
      cbn in H.
      solve_stlc.
      repeat rewrite Rmul_1_l.
      replace (pkmul (-1):%p 1:%p) with (pkmul 1:%p (-1):%p) by (apply Rmul_comm).
      rewrite Rmul_1_l.
      rewrite Rsub_def.
      
      do 3 rewrite Rmul_comm.
      rewrite Rmul_comm.
      (** solve_stlc. *)
      invert H.      
      invert H0.
      invert H5.
      invert H6.
      invert H7.
      invert H7.
      invert H8.
      invert H8.
      cbn in H1.

      (** After beta *)
      invert H1.
      invert H.
      invert H10.
      invert H1.
      invert H0. invert H. invert H14. invert H1. invert H. invert H16.
      invert H0. invert H. invert H2. invert H1. invert H. invert H0.
      
        invert H0. invert H. invert H2.
      solve_stlc.
      
      constructor.
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

End DivGadgets.     
