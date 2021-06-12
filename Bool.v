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
    <{ \_: Bool, \_: Bool,
           #0 && #1 }>. 

  Definition andb_check :=
    <[ { (1i[0]) * (1i[1]) == (1o) } ]>.  

  (** Equivalence proof over r1cs *)
  Theorem and_equiv_r1cs:
    andb <=*=> andb_check.
  Proof.
    unfold andb, andb_check.
    eapply Step. 
    - exact [].
    - econstructor.
      intros x H. 
      econstructor.
      intros; cbn. 
      econstructor; repeat econstructor; eassumption.
    - constructor.
    - (** This is the assumption that quantifies over inputs *)
      intros.
      pose proof (vec2_proj inputs); exists_inverter; invert H.
      + eapply Step. 
        * now exact [].
        * apply typing_app with (T1:=<{{ Bool }}>).
          econstructor.
          intros; cbn.
          econstructor.
          intros; cbn.
          apply typing_boolop; repeat econstructor; eassumption.
          now econstructor.
        * now econstructor.
        * intros.
          pose proof (vec1_proj inputs); exists_inverter; invert H.
          -- (** Eq_rect axiom *)
             depcbnpk.
             apply BaseTrue with (vars:=[]).
             ++ now repeat (econstructor; try beta).
             ++ unfold correct; cbn; constructor; depcbnpk.
                ** now reflexivity.
                ** now constructor.
          -- (** Eq_rect axiom *)
            depcbnpk.            
            apply BaseFalse with (vars:=[]).
            ++ now repeat (econstructor; try beta).
            ++ unfold correct; cbn; constructor; depcbnpk.
                ** now reflexivity.
                ** now constructor.
      + econstructor.
        * now exact [].
        * apply typing_app with (T1:=<{{ Bool }}>).
          econstructor.
          intros; cbn.
          econstructor.
          intros; cbn.
          apply typing_boolop; repeat econstructor; eassumption.
          now econstructor.
        * now econstructor.
        * intros.
          pose proof (vec1_proj inputs); exists_inverter; invert H.
          -- (** Eq_rect axiom *)
             depcbnpk.
             apply BaseFalse with (vars:=[]).
             ++ now repeat (econstructor; try beta).
             ++ unfold correct; cbn; constructor; depcbnpk.
                ** now reflexivity.
                ** now constructor.
          -- (** Eq_rect axiom *)
            depcbnpk.            
            apply BaseFalse with (vars:=[]).
            ++ now repeat (econstructor; try beta).
            ++ unfold correct; cbn; constructor; depcbnpk.
                ** now reflexivity.
                ** now constructor.
    Unshelve.        
    exact empty.
    exact empty.
    exact empty.
    exact empty.
    exact empty.
    exact empty.
    exact empty.
    exact empty.
    exact empty.
    exact empty.
    exact empty.
    exact empty.
  Qed.

  (** 1. Logical Or  *)
  Definition orb :=
    <{ \_: Bool, \_: Bool,
           #0 || #1 }>. 

  (** (X1 − 1) · (1 − X2) + 1 − Y1 = 0 *)
  Definition orb_check :=
    <[ { (1i[0] + [-1]) * ([1] + -1i[1]) == (1o + [-1]) } ]>.

  (** Second equivalence proof over r1cs *)
  Theorem or_equiv_r1cs:
    orb <=*=> orb_check.
  Proof.    
    unfold orb, orb_check.
    eapply Step. 
    - exact [].
    - econstructor.
      intros x H. 
      econstructor.
      intros; cbn. 
      econstructor; repeat econstructor; eassumption.
    - constructor.
    - (** This is the assumption that quantifies over inputs *)
      intros.
      pose proof (vec2_proj inputs); exists_inverter; invert H.
      + eapply Step. 
        * now exact [].
        * apply typing_app with (T1:=<{{ Bool }}>).
          econstructor.
          intros; cbn.
          econstructor.
          intros; cbn.
          apply typing_boolop; repeat econstructor; eassumption.
          now econstructor.
        * now econstructor.
        * intros.
          pose proof (vec1_proj inputs); exists_inverter; invert H.
          -- (** Eq_rect axiom *)
             depcbnpk.
             apply BaseTrue with (vars:=[]).
             ++ now repeat (econstructor; try beta).
             ++ unfold correct, correct_lt; constructor; depcbnpk.
                ** now reflexivity.
                ** now constructor.
          -- (** Eq_rect axiom *)
            depcbnpk.            
            apply BaseTrue with (vars:=[]).
            ++ now repeat (econstructor; try beta).
            ++ unfold correct, correct_lt; constructor; depcbnpk.
                ** now reflexivity.
                ** now constructor.
      + econstructor.
        * now exact [].
        * apply typing_app with (T1:=<{{ Bool }}>).
          econstructor.
          intros; cbn.
          econstructor.
          intros; cbn.
          apply typing_boolop; repeat econstructor; eassumption.
          now econstructor.
        * now econstructor.
        * intros.
          pose proof (vec1_proj inputs); exists_inverter; invert H.
          -- (** Eq_rect axiom *)
             depcbnpk.
             apply BaseTrue with (vars:=[]).
             ++ now repeat (econstructor; try beta).
             ++ unfold correct, correct_lt; constructor; depcbnpk.
                ** rewrite Rmul_zero_r.
                   now reflexivity.
                ** now constructor.
          -- (** Eq_rect axiom *)
            depcbnpk.            
            apply BaseFalse with (vars:=[]).
            ++ now repeat (econstructor; try beta).
            ++ unfold correct, correct_lt; constructor; depcbnpk.
                ** rewrite Rmul_zero_r. autorewrite with pk. now reflexivity.
                ** now constructor.
    Unshelve.        
    exact empty.
    exact empty.
    exact empty.
    exact empty.
    exact empty.
    exact empty.
    exact empty.
    exact empty.
    exact empty.
    exact empty.
    exact empty.
    exact empty.
  Qed.


End BoolGadget.     
