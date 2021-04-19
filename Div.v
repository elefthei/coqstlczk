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

     
   Lemma Rmul_neq_0:
     forall a b, pksub (pkmul a b) 1:%p = 0:%p -> a <> 0:%p /\ b <> 0:%p.
   Proof.
     intros.
     split.
     intro Hcontra;
       rewrite Hcontra in H;
       rewrite (Rmul_comm RTH) in H.
     rewrite Rmul_zero_l in H.
     destruct (pKfth p_prime).
     invert F_R.
     rewrite Rsub_def in H.
     rewrite Radd_0_l in H.
     
     inversion H.
     cbn in H.
     invert H.
     cbn in H1.
     pose proof (Z.mod_mod 1 p p_neq0).
   Admitted.

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
    inversion inputs as [tsinp|inp].
    inversion vars as [tsvar|var].
    inversion outputs as [tsout|out].
    subst.
    replace inputs with [inp].
    replace vars with ([]:Vfp 0).
    replace outputs with [out].
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
      rewrite neq_stlc_fp in H7.
      rewrite Rmul_comm.
      rewrite (Finv_l).
      rewrite Rsub_def.
      rewrite Ropp_def.
      reflexivity.
      exact H7.
      constructor.
    - (** evaluate the r1cs term *)
      invert Hprem.
      repeat rewrite Rmul_1_l in H4.
      econstructor.
      beta.
      cbn.

      econstructor.
      apply step_div_const.
      apply neq_stlc_fp.
      intro.
      rewrite H0 in H4.
      rewrite Rmul_comm in H4. rewrite Rmul_zero_l in H4.
      rewrite Rsub_def in H4.
      rewrite Radd_0_l in H4.
      apply  Ropp_1_not_0 in H4.
      inversion H4.

      
      
  Admitted.

End DivGadget.     
