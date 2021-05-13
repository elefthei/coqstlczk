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

  (** 1. Logical And  *)
  Definition andb :=
    <{ \_: Bool * Bool,
           (fst #0) && (snd #0) }>. 

  Definition andb_check :=
    <[ { (1i[0]) * (1i[1]) == (1o[0]) } ]>.  

  (** Equivalence proof over r1cs *)
  Theorem and_equiv_r1cs:
    andb <=*=> andb_check.
  Proof.    
    unfold r1cs_lambda_equiv, andb, andb_check.
    intros.
    cbn in vars, inps, outs, HcannonIn, HcannonOut.
    unfold correct, correct_lt.
    split; intros HPrem;
      invert HeT; cbn in H1; pick fresh x for L; specialize (H1 x Fr); invert H1;
        repeat invert_types; subst;
          pose proof (vec2_proj inps); exists_inverter; deconj;
            pose proof (vec1_proj outs); exists_inverter; deconj; subst;
              pose proof (cannonical_forms_bool_bool args a b HcannonIn) as HcasesIn;
              pose proof (cannonical_forms_bool result a0 HcannonOut) as HcasesOut;
              clear HcannonIn HcannonOut.
    - (** Backwards reasoning *)
      deconj; econstructor; cbn; try constructor.
      + now autorewrite with pk using trivial.
      + now repeat invert_stlc.
      + now repeat invert_stlc.
      + now repeat invert_stlc.
      + now repeat invert_stlc.
      + now autorewrite with pk using trivial.
      + now autorewrite with pk using trivial.
      + now autorewrite with pk using trivial.
    - (** Forward reasoning *)      
      invert HPrem; deconj; cbn in H2; autorewrite with pk in H2.
      + now repeat (try econstructor; try beta).
      + now invert H2; apply mod_0_neq_min_1 in H0; contradiction.
      + now invert H2; apply mod_0_neq_min_1 in H0; contradiction.
      + now invert H2; apply mod_0_neq_min_1 in H0; contradiction.
      + now invert H2; symmetry in H0; apply mod_0_neq_1 in H0; contradiction.
      + now repeat (try econstructor; try beta).
      + now repeat (try econstructor; try beta).
      + now repeat (try econstructor; try beta).
        Unshelve.        
        exact empty.
        exact empty.
        exact empty.
        exact empty.
  Qed.

  (** 2: Logical Or *)
  Definition orb :=
    <{ \_: Bool * Bool,
           (fst #0) || (snd #0) }>. 

  (** (X1 − 1) · (1 − X2) + 1 − Y1 = 0 *)
  Definition orb_check :=
    <[ { (1i[0] + [-1]) * ([1] + -1i[1]) == (1o[0] + [-1]) } ]>.

  (** Second equivalence proof over r1cs *)
  Theorem or_equiv_r1cs:
    orb <=*=> orb_check.
  Proof.    
    unfold r1cs_lambda_equiv, orb, orb_check.
    intros.
    cbn in vars, inps, outs, HcannonIn, HcannonOut.
    unfold correct, correct_lt.
    split; intros HPrem;
      invert HeT; cbn in H1; pick fresh x for L; specialize (H1 x Fr); invert H1;
        repeat invert_types; subst;
          pose proof (vec2_proj inps); exists_inverter; deconj;
            pose proof (vec1_proj outs); exists_inverter; deconj; subst;
              pose proof (cannonical_forms_bool_bool args a b HcannonIn) as HcasesIn;
              pose proof (cannonical_forms_bool result a0 HcannonOut) as HcasesOut;
              clear HcannonIn HcannonOut; destruct (F_R FTH).
    - (** Backwards reasoning *)
      deconj; econstructor; cbn; try constructor.
      + now autorewrite with pk; rewrite Rmul_zero_r; reflexivity.
      + autorewrite with pk; rewrite Rmul_zero_r; rewrite Radd_0_l;
        autorewrite with pk using trivial.
      + now autorewrite with pk; rewrite Rmul_zero_r; reflexivity.
      + now repeat invert_stlc. 
      + now repeat invert_stlc.
      + now repeat invert_stlc.
      + now repeat invert_stlc.
      + now autorewrite with pk; rewrite Rmul_zero_r; autorewrite with pk using trivial.
    - (** Forward reasoning *)
      invert HPrem; deconj; cbn in H2; autorewrite with pk in H2.
      + now repeat (try econstructor; try beta).
      + econstructor.
        apply step_beta; repeat constructor; econstructor; try intros; econstructor.
        econstructor.
        econstructor.
        econstructor.
        econstructor.
        cbn. 
        econstructor.
        apply step_binop_cog_1; repeat econstructor.        
        now econstructor; repeat constructor.
      + now repeat (try econstructor; try beta).
      + now autorewrite with pk in H2;
          rewrite Rmul_zero_r in H2;
          autorewrite with pk in H2; invert H2; apply mod_0_neq_min_1 in H0; contradiction.
      + now autorewrite with pk in H2;
          rewrite Rmul_zero_r in H2; rewrite Radd_0_l in H2;
            symmetry in H2; invert H2; apply mod_0_neq_1 in H0; contradiction.
      + now autorewrite with pk in H2;
          rewrite Rmul_zero_r in H2; rewrite Radd_0_l in H2;
            autorewrite with pk in H2; symmetry in H2; invert H2; apply mod_0_neq_1 in H0;
              contradiction.
      + now autorewrite with pk in H2;
          rewrite Rmul_zero_r in H2; rewrite Radd_0_l in H2; symmetry in H2;
            invert H2; apply mod_0_neq_1 in H0; contradiction.
      + now repeat (try econstructor; try beta).
        Unshelve.
        exact empty.
        exact empty.
        exact empty.
        exact empty.
  Qed.

End BoolGadget.     
