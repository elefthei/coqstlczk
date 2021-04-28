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
  Definition andb :=
    <{ \_: Bool * Bool,
           (fst #0) && (snd #0) }>. 

  Definition andb_check :=
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
    andb <=*=> andb_check.
  Proof.    
    unfold r1cs_lambda_tequiv, andb, andb_check.
    intros args results inps outs vars t t' HTe Hins Houts.
    cbn in vars.

    unfold cannonical in Hins, Houts;
    unfold correct, correct_lt;
    split; intros HPrem;      
      pose proof (vec2_proj inps); pose proof (vec1_proj outs);exists_inverter; deconj; subst;
        invert HTe; cbn in H7; pick fresh x for L; specialize (H7 x Fr);
          (** Invert inputs *)
          pose proof (inversion_principle_bool_bool args a0 b H0 H5);
          (** Invert outputs *)
          invert H7.
    - (** results :: Bool *)
      pose proof (inversion_principle_bool results a _ H H2); invert H3; deconj.
      + econstructor; cbn; pksimpl.
        invert H6; deconj.
        * rewrite (Rsub_def (F_R FTH)).
          rewrite (Ropp_def (F_R FTH)).
          reflexivity.
        * solve_stlc.
        * constructor.
      + econstructor; cbn; pksimpl; invert H6; invert H7; deconj.
        * solve_stlc.
        * invert H6; deconj.
          solve_stlc.
          solve_stlc.
        * pksimpl; reflexivity.
        * invert H6; deconj.
          pksimpl; reflexivity.
          pksimpl; reflexivity.
        * constructor.
        * constructor.
        * constructor.
        * constructor.
    - (** results :: Field *)
      invert H; invert H2; invert H3; deconj.
      solve_stlc.
      invert H; deconj. solve_stlc.
      invert H2; deconj; solve_stlc.

    - pose proof (inversion_principle_bool_bool args a0 b H0 H5); invert H3; invert H6; deconj.
      + econstructor.
        beta.
        cbn.
        econstructor. apply step_binop_cog_1; constructor; repeat constructor.
        econstructor. apply step_binop_cog_2; constructor; repeat constructor.
        econstructor. apply step_and_1; constructor.
        pose proof (inversion_principle_bool results a Datatypes.nil H H2).
        invert H6; deconj.
        * apply multi_refl.
        * invert HPrem; cbn in H11.
          repeat rewrite (Rmul_1_l (F_R FTH)) in H11.
          rewrite (Rsub_def (F_R FTH)) in H11.
          rewrite Ropp_0_0 in H11.
          rewrite (Radd_comm (F_R FTH)) in H11.
          rewrite (Radd_0_l (F_R FTH)) in H11.          
          destruct (FTH).
          contradiction.
      + invert H3; deconj.
        * destruct (FTH); contradiction.
        * invert H6; deconj.
          destruct (FTH); contradiction.
          destruct (FTH); contradiction.
      + invert H7; deconj.
        * destruct (FTH); contradiction.
        * invert H3; deconj; destruct (FTH); contradiction.
      + invert H3; deconj; invert H7; deconj;
        pose proof (inversion_principle_bool results a Datatypes.nil H H2).

        * invert H7; deconj.
          invert HPrem; cbn in H11.
          repeat rewrite (Rmul_1_l (F_R FTH)) in H11.
          rewrite (Rsub_def (F_R FTH)) in H11.          
          rewrite (Radd_0_l (F_R FTH)) in H11.
          apply Ropp_1_not_0 in H11.
          contradiction.
          
          econstructor.
          beta.
          cbn.
          
          econstructor. apply step_binop_cog_1; constructor; repeat constructor.
          econstructor. apply step_binop_cog_2; constructor; repeat constructor.
          econstructor. apply step_and_2; constructor.
          apply multi_refl.

        * invert H6; deconj; invert H3; deconj; try (destruct FTH; contradiction).
        * invert H3; deconj; invert H6; deconj; try (destruct FTH; contradiction).
        * invert H7; deconj; invert H3; deconj; invert H6; deconj.
          invert HPrem; cbn in H11.
          
          repeat rewrite (Rmul_1_l (F_R FTH)) in H11.
          rewrite (Rsub_def (F_R FTH)) in H11.          
          rewrite (Radd_0_l (F_R FTH)) in H11.
          apply Ropp_1_not_0 in H11.
          contradiction.

          destruct FTH; contradiction.
          destruct FTH. symmetry in H8. contradiction.

          invert HPrem; cbn in H11.
          
          repeat rewrite (Rmul_1_l (F_R FTH)) in H11.
          rewrite (Rsub_def (F_R FTH)) in H11.          
          rewrite (Radd_0_l (F_R FTH)) in H11.
          apply Ropp_1_not_0 in H11.
          contradiction.

          econstructor. beta. cbn.
          econstructor. apply step_binop_cog_1; constructor; repeat constructor.
          econstructor. apply step_binop_cog_2; constructor; repeat constructor.
          econstructor. apply step_and_4; constructor.
          apply multi_refl.

          econstructor. beta. cbn.
          econstructor. apply step_binop_cog_1; constructor; repeat constructor.
          econstructor. apply step_binop_cog_2; constructor; repeat constructor.
          econstructor. apply step_and_4; constructor.
          apply multi_refl.
          
          destruct FTH; symmetry in H8; contradiction.
          econstructor. beta. cbn.
          econstructor. apply step_binop_cog_1; constructor; repeat constructor.
          econstructor. apply step_binop_cog_2; constructor; repeat constructor.
          econstructor. apply step_and_4; constructor.
          apply multi_refl.
    - (** results :: Field *)
      invert H12.
      invert H8.
      invert H7.
      invert H6.
      invert H6.
      Unshelve.
      exact empty.
      exact empty.
      exact empty.
      exact empty.
      exact empty.
  Qed.
      
End BoolGadget.     
