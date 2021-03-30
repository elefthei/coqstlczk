Require Import Metalib.Metatheory.
From STLCZK Require Import Stlc.
From STLCZK Require Import Gadgets.
From STLCZK Require Import R1cs.
From STLCZK Require Import GaloisField.

Require Import Coqprime.elliptic.ZEll.
Require Import Coq.Numbers.BinNums.
Require Import Coqprime.elliptic.GZnZ.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.ZArith.BinIntDef.
Import Z.
Require Import Coq.ZArith.BinInt.

Module DivGadget.
  Include GaloisField.
  Include Gadgets.
  Include R1csDep.
  (** Example 1: Division *)
  Definition div :=
    <{ \_: Field, (F1 / #0) }>.

  Locate "*".
  Definition div_check :=
    <{ \_: Field,
           (\_: Field,
                (#0 * #1) == F1)
     }>.

  Compute normalize_all <{ div_check fp_one fp_one }>.
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
  Theorem div_gadget_equiv: div ~~ div_check.
  Proof.
    unfold circuit_equiv, div, div_check.
    intros n w.
    split; intro H; solve_stlc.
    - destruct (eq_field n fp_zero); solve_stlc.
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

  (** Second equivalence proof polymorphic *)
  Theorem div_equiv_poly:
      div ~= div_check.
  Proof.
    unfold circuit_equiv_poly, div, div_check.
    intros n w T Tc Tc'.
    invert Tc.
    invert Tc'.
    invert H2.
    invert H3.
    cbn in H1.
    invert H5.
    cbn in H2.
    
    split; intros; solve_stlc.
  Admitted.

End DivGadgets.     
