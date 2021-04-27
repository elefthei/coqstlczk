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

Module BoolGadget(PF: GaloisField).
  Import PF.
  Include Gadget PF.
  Import VectorNotations.

  (** Example 1: Division *)
  Definition andbg :=
    <{ \_: Bool * Bool,
           (fst #0) && (snd #0) }>. 

  Definition andg_check :=
    <[ { (1i[0]) * (1i[1]) == (1o[0]) } ]>.  

  Ltac deconj :=
    repeat match goal with
    | [H: _ /\ _ |- _ ] => invert H
    end.

  Ltac pksimpl :=
    repeat match goal with
           |[H: _ |- context[pkmul ?a 0:%p]] => rewrite Rmul_zero_l
           |[H: _ |- context[pkmul 1:%p ?a]] => rewrite (Rmul_1_l (F_R FTH))
           |[H: _ |- context[pkmul 0:%p ?a]] =>
            replace (pkmul 0:%p a) with (pkmul a 0:%p) by (apply (Rmul_comm (F_R FTH)))
           |[H: _ |- pksub 0:%p ?a = 0:%p] =>
            apply Rsub_0_0
           end.
  
  (** Second equivalence proof over r1cs *)
  Theorem and_equiv_r1cs:
    andbg <=*=> andg_check.
  Proof.    
    unfold r1cs_lambda_tequiv, andbg, andg_check.
    intros args results inps outs vars t t' HTe Hins Houts.
    cbn in vars.

    unfold cannonical in Hins, Houts;
    unfold correct, correct_lt;
    split; intros HPrem;      
      pose proof (vec2_proj inps); pose proof (vec1_proj outs);exists_inverter; deconj; subst.
    invert HTe.
    cbn in H7.
    
    pose proof (inversion_principle_bool_bool args a0 b H0 H5); invert H3.
    - deconj. pose proof (inversion_principle_bool results a H H2).
    (** Invert inps *)
    invert HTe; invert H. invert H5. invert H2; invert H5; pksimpl.
    - cbn in H7.
      pose proof (vec1_proj v); exists_inverter; subst.
      destruct (inversion_principle_bool e2 a H10 H2).
      destruct H.
      subst.
      econstructor; cbn; pksimpl.
      deconj.
      econstructor; cbn; pksimpl.
      solve_stlc.
    invert H.
    invert H9.
    
    - repeat match goal with
             |[H: Vfp 1 |- _] => pose proof (vec1_proj H); exists_inverter; subst; clear H
             |[H: Vfp 2 |- _] => pose proof (vec2_proj H); exists_inverter; subst; clear H
             |[H: exp_typ _ _ _ |- _] => invert H
             |[H: _ \/ _ |- _ ]=> invert H
             end; try solve[invert HTe];
      econstructor; cbn;
        repeat match goal with
               |[H: _ |- context[pkmul ?a 0:%p]] => rewrite Rmul_zero_l
               |[H: _ |- context[pkmul 1:%p ?a]] => rewrite (Rmul_1_l (F_R FTH))
               |[H: _ |- context[pkmul 0:%p ?a]] =>
                replace (pkmul 0:%p a) with (pkmul a 0:%p) by (apply (Rmul_comm (F_R FTH)))
               |[H: _ |- pksub 0:%p ?a = 0:%p] =>
                apply Rsub_0_0
               end.
      
      invert HTargs.


      
      invert HTargs.
      induction HTa
      
  Admitted.

End BoolGadget.     
