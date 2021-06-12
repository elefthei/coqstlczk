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
  Import ListNotations.

  (** Example 1: Division *)
  Definition ite :=
    <{ \_: Bool, \_: Field, \_: Field,
           if #2 then #1 else #0
     }>. 

  Definition ite_check :=
    <[ { (1i[0]) * (1i[2] + -1i[1]) == (1o + -1i[1]) } ]>.


  Ltac typer1 :=
    match goal with
    | [|- <{{ _ |- <{ \_ : _, _ }> :: _}}>] => eapply typing_abs; intros; cbn
    | [|- <{{ _ |- <{ if _ then _ else _ }> :: _ }}>] => eapply typing_if; constructor; cbn
    | [|- (?x, ?T) = (?x, ?T) \/ _] => left; reflexivity
    | [|- _ \/ (?x, ?T) = (?x, ?T) ] => right; reflexivity
    | [|- _ \/ (?x1, ?T1) = (?x2, ?T2) ] => left
    | [|- (?x1, ?T1) = (?x2, ?T2) \/ _ ] => right
    | [|- uniq _ ] => repeat constructor; eassumption
    end.

  (** Second equivalence proof over r1cs *)
  Theorem ite_equiv_r1cs:
    ite <=*=> ite_check.
  Proof.
    unfold ite_check, ite.
    apply Step with (t:=<{{ Bool }}>) (t':=<{{Field -> Field -> Field}}>).
    - constructor.
    - repeat typer.
    - constructor.
    - intros.
      apply Step with (t:=<{{ Field }}>) (t':=<{{Field -> Field}}>).
      + constructor.
      + apply typing_app with (T1:=<{{ Bool }}>).
        
        cbn.
        right.
        right.
        left.
        reflexivity.
        repeat constructor; eassumption.
      + constructor.
        cbn.
        
        repeat (constructor; eassumption).
    - econstructor.
      intros x H. 
      econstructor; intros; cbn.      
      econstructor; intros; cbn.
      econstructor; intros; cbn.
      econstructor; intros; cbn.
      right.
      right.
      econstructor. repeat econstructor. eassumption.
      repeat econstructor; eassumption.
    intros.
    cbn in vars, inps, outs, HcannonIn, HcannonOut.
    unfold correct, correct_lt.
    split; intros HPrem;
      invert HeT; cbn in H1; pick fresh x for L; specialize (H1 x Fr); invert H1;
        repeat invert_types; subst;
          pose proof (vec3_proj inps); exists_inverter; deconj;
            pose proof (vec1_proj outs); exists_inverter; deconj; subst;
              pose proof (cannonical_forms_bool_bool args a b HcannonIn) as HcasesIn;
              pose proof (cannonical_forms_bool result a0 HcannonOut) as HcasesOut;
              clear HcannonIn HcannonOut.
    - (** Backwards reasoning *)
      deconj; econstructor; cbn; try constructor.
      + now autorewrite with pk using trivial.
        admit.
    - (** Forward reasoning *)
  Admitted.

End IteGadget.     
