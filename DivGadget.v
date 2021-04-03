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

  Lemma eq_field: forall (x y : Fp), {x = y} + {x <> y}.
  Proof.
    intros.
    unfold Fp in *.
    unfold pK in *.
    destruct x as (x0, Hx_mod), y as (y0, Hy_mod).
    pose proof (Coq.ZArith.BinInt.Z.eq_dec x0 y0).
    inversion H.
    - left. exact (GZnZ.zirr p x0 y0 Hx_mod Hy_mod H0).
    - right. intro. inversion H1. contradiction.
  Qed.

  Lemma fp_mul_inv: forall n, n <> 0:%p -> pkmul (pkdiv 1:%p n) n = 1:%p.
  Proof.
    intros.
    pose proof (pKfth p_prime) as FT.
    invert FT.
    rewrite Fdiv_def.
    invert F_R.
    rewrite <- Rmul_assoc.
    rewrite Finv_l.
    rewrite Rmul_1_l.
    reflexivity.
    assumption.
  Qed.

  Lemma fp_mul_div : forall n w, n <> 0:%p->
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

  Lemma fp_mul_zero_l: forall w, (pkmul w 0:%p) = 0:%p.
  Proof.
    intros.
    cbn.
    apply GZnZ.zirr.
    
    rewrite Zmult_comm.
    pose proof (p_prime).
    invert H.
    rewrite Z.mod_0_l.
    cbn.
    reflexivity.    
    intro Hcontra.    
    rewrite Hcontra in H0.
    invert H0.
  Qed.

  Lemma mod_0_neq_1: 0 mod p <> 1 mod p.
  Proof.
    destruct (p_prime).
    rewrite Z.mod_0_l.
    rewrite Z.mod_1_l.
    intro.
    invert H1.
    assumption.
    intro.
    rewrite H1 in H.
    invert H.
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

  (** First equivalence proof, monomorphic to Field *)
  Theorem div_gadget_equiv: div ~~ div_fp_check.
  Proof.
    unfold circuit_equiv, div, div_fp_check.
    intros n w.
    split; intro H; solve_stlc.
    - destruct (eq_field n 0:%p); solve_stlc.
      (* n = 0 *)
      subst.
      rewrite fp_mul_zero_l in H9.
      invert H9.
      apply mod_0_neq_1 in H0.
      contradiction.
      (* n <> 0 *)
      econstructor; solve_stlc.
      econstructor.
      apply step_div_const.
      generalize n0.
      apply neq_stlc_fp.
      rewrite -> (fp_mul_div n w n0).      
      apply multi_refl.
    - econstructor.
      eapply step_app_1; solve_stlc.
      cbn.
      econstructor; try eapply step_beta; solve_stlc.
      econstructor; solve_stlc.      
      econstructor.
      rewrite fp_mul_inv.
      eapply step_eq_refl.
      apply neq_stlc_fp.
      assumption.
      apply multi_refl.
  Qed.


  (** Try an example! *)
  Lemma div_check_ex1: correct div_check [1:%p] [1:%p] []. 
  Proof.
    unfold correct, correct_lt.
    cbn.
    constructor.
    - unfold pksub, pkmul.
      pose proof (Z.mod_1_l).
      pose proof (p_prime).
      invert H0.
      apply H in H1.
      unfold GZnZ.sub, GZnZ.mul.    
      cbn.
      rewrite H1.
      cbn.
      rewrite H1.
      cbn.
      rewrite H1.
      cbn.
      reflexivity.
    - constructor.
  Qed.
 

  Import VectorNotations.
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
    split; intro Hprem.    
    - (** evaluate the r1cs term *)
      constructor.
      unfold pksub, pkmul.
      pose proof (Z.mod_1_l).
      destruct (p_prime).
      apply H0 in H2.
      unfold GZnZ.sub, GZnZ.mul.
      destruct inp, out.
      cbn.
      rewrite H2.      
      repeat rewrite Z.mul_1_l.
      repeat rewrite <- Zdiv.Zmult_mod.
      apply zirr.
      cbn.
      
      (** evaluate the lambda term *)
      solve_stlc.
      invert H12.

  Admitted.

End DivGadgets.     
