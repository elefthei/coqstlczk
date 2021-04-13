(* generated by Ott 0.31, locally-nameless from: Stlc.ott *)
Require Import Bool.
Require Import Metalib.Metatheory.
Require Import List.
Require Import Ott.ott_list_core.

(** For F_p *)
Require Import Coqprime.elliptic.ZEll.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.ZArith.BinInt.
Require Import Coqprime.elliptic.GZnZ.
Require Import Coq.ZArith.BinIntDef.
Import Z.
From Coq Require Import Ring.
From Coq Require Import Field.

From STLCZK Require Import Ltac.

Module Type GaloisField.
  (** Prime  *)
  Parameter p: Z.
  Parameter p_prime: prime p.

  Definition Fp: Set := pK p.
  Definition to_p x:Fp := GZnZ.mkznz _ _ (GZnZ.modz _  x).
  Notation "x :%p" := (to_p x) (at level 1).

  Definition p_gt0 : 0 < p.
  Proof.
    pose proof (p_prime).
    inversion H.
    apply Z.lt_gt in H0.
    apply Z.gt_lt.
    apply gt_relax.
    cbn.
    exact H0.
  Defined.

  Definition FTH := pKfth p_prime.
  Definition RTH := RZnZ _ p_gt0.    
  Add Ring RTH: RTH.
  Add Field FTH: FTH.
  
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
End GaloisField.
  
