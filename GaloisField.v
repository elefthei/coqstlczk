(** For F_p *)
Require Import Coqprime.elliptic.ZEll.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.ZArith.BinInt.
Require Import Coqprime.elliptic.GZnZ.
Require Import Coq.ZArith.BinIntDef.
Require Import Coq.micromega.Lia.
Import Z.
From Coq Require Import Ring.
From Coq Require Import Field.

Set Implicit Arguments.

From Equations Require Import Equations.

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
    apply Z.lt_lt_succ_r in H0.
    lia. 
  Defined.

  Hint Resolve p_gt0: pk.
  
  Definition p_neq0: p <> 0.
  Proof.
    pose proof (p_gt0).    
    intro.
    rewrite H0 in H.
    inversion H.
  Qed.
  Hint Resolve p_neq0: pk.

  Definition FTH := pKfth p_prime.
  Add Field FTH: FTH.

  Hint Resolve (F_1_neq_0 FTH): pk.
  Hint Rewrite (Fdiv_def FTH): pk.
  Hint Rewrite (Finv_l FTH): pk.
  Hint Rewrite (Radd_0_l (F_R FTH)): pk.
  (* Hint Rewrite (Radd_comm (F_R FTH)): pk. *)
  (* Hint Rewrite (Radd_assoc (F_R FTH)): pk. *)
  Hint Rewrite (Rmul_1_l (F_R FTH)): pk.
  (** Hint Rewrite (Rmul_comm (F_R FTH)): pk. *)
  (* Hint Rewrite (Rmul_assoc (F_R FTH)): pk. *)
  Hint Rewrite (Rdistr_l (F_R FTH)): pk.
  Hint Rewrite (Rsub_def (F_R FTH)): pk.
  Hint Rewrite (Ropp_def (F_R FTH)): pk.

  Lemma Rmod1_1: 1 mod p = 1.
  Proof.
    destruct p_prime.
    rewrite (Z.mod_1_l _ H).
    reflexivity.
  Qed.
  Hint Rewrite Rmod1_1: pk.

  Lemma Rmul_1_r: forall p,
      pkmul p 1:%p = p.
  Proof.
    intros.
    rewrite (Rmul_comm (F_R FTH)).
    simple apply (Rmul_1_l (F_R FTH)).
  Qed.
  Hint Rewrite Rmul_1_r: pk.

  #[global] Instance Fp_EqDec: EqDec Fp.
  red.
  intros.
  unfold Fp in *.
  unfold pK in *.
  destruct x as (x0, Hx_mod), y as (y0, Hy_mod).
  pose proof (Z.eq_dec x0 y0).
  inversion H.
  - left; exact (GZnZ.zirr p x0 y0 Hx_mod Hy_mod H0).
  - right; intro; inversion H1; contradiction.
    
  Lemma Ropp_pkmul: forall (a: Fp),
       pkopp a = pkmul (-1):%p a.
  Proof.
    intro.
     unfold Fp, pK, pkopp, pkmul.
     intros.
     unfold pkopp, GZnZ.opp, pkmul, GZnZ.mul.
     cbn.
     destruct a.
     cbn.
     apply zirr.
     rewrite Zdiv.Zmult_mod_idemp_l.
     replace (-1 * val) with (-val) by lia.
     reflexivity.
  Qed.
  Hint Rewrite Ropp_pkmul: pk.
  
  Lemma Rmul_inv: forall n, n <> 0:%p -> pkmul (pkdiv 1:%p n) n = 1:%p.
  Proof.
    intros.
    field.
    exact H.
  Qed.
  Hint Rewrite Rmul_inv: pk.
  
  Lemma Rmul_div : forall n w, n <> 0:%p->
                            pkdiv (pkmul w n) n = w.
  Proof.
    intros.
    field.
    exact H.
  Qed.    
  Hint Rewrite Rmul_div: pk.
  
  Lemma Rmul_zero_r: forall w, pkmul w 0:%p = 0:%p.
  Proof.    
    intros.
    apply GZnZ.zirr.
    rewrite Zmult_comm.
    pose proof (p_prime).
    inversion H; clear H; subst.
    rewrite Z.mod_0_l.
    cbn.
    reflexivity.    
    intro Hcontra.    
    rewrite Hcontra in H0.
    inversion H0.
  Qed.
  
  Lemma Rmul_zero_l: forall w, pkmul 0:%p w = 0:%p.
  Proof.
    intros.
    rewrite (Rmul_comm (F_R FTH)).
    apply Rmul_zero_r.
  Qed.
  Hint Rewrite Rmul_zero_l: pk.
  Hint Rewrite Rmul_zero_r: pk.
  
  Lemma mod_0_neq_1: 0 mod p <> 1 mod p.
   Proof.
     destruct (p_prime).
     rewrite Z.mod_0_l.
     rewrite Z.mod_1_l.
     intro.
     inversion H1.
     assumption.
     intro.
     rewrite H1 in H.
     inversion H.
   Qed.
   Hint Resolve mod_0_neq_1: pk.
   
   Lemma mod_0_neq_min_1: -1 mod p <> 0 mod p.
   Proof.
     destruct (p_prime).
     rewrite Z.mod_0_l.
     intro.
     pose proof p_gt0.
     apply Z.lt_gt in H2.
     - pose proof (Zdiv.Z_div_exact_2 (-1) p H2 H1).
       pose proof (Zdiv.Zdiv_1_l p H).
       replace (p*(-1/p)) with (-1*p*(1/p)) in H3.
       rewrite H4 in H3.
       rewrite Z.mul_0_r in H3.
       inversion H3.
       replace (-1*p) with (p*(-1)) by (apply Z.mul_comm).
       replace (-1/p) with ((-1)*(1/p)) by lia.
       rewrite Z.mul_assoc.
       reflexivity.
     - exact p_neq0.
   Qed.
   Hint Resolve mod_0_neq_min_1: pk.

   Lemma Rplus_min1_1_l: pkplus (-1):%p 1:%p = 0:%p.
   Proof.
     destruct (F_R FTH).
     replace ((-1):%p) with (pkopp 1:%p).
     rewrite Radd_comm.
     rewrite Ropp_def.
     reflexivity.
     unfold pkopp, GZnZ.opp.
     apply zirr.
     cbn.
     destruct p_prime.
     rewrite Rmod1_1.
     cbn. reflexivity.
   Qed.
   Hint Rewrite Rplus_min1_1_l: pk.
  
   Lemma Rplus_min1_1_r: pkplus 1:%p (-1):%p = 0:%p.
   Proof.
     destruct (F_R FTH).
     rewrite Radd_comm.
     apply Rplus_min1_1_l.
   Qed.
   Hint Rewrite Rplus_min1_1_r: pk.
  
   Lemma Rmul_min1_a_l: forall a, pkmul (-1):%p a = pkopp a.
   Proof.
     intros.
     destruct a.
     unfold pkmul, GZnZ.mul, pkopp, GZnZ.opp.
     cbn.
     apply zirr.
     rewrite Zdiv.Zmult_mod_idemp_l.
     rewrite Z.opp_eq_mul_m1.
     rewrite Z.opp_eq_mul_m1.
     reflexivity.
   Qed.
   Hint Rewrite Rmul_min1_a_l: pk.

   Lemma Rmul_min1_a_r: forall a, pkmul a (-1):%p = pkopp a.
   Proof.
     intros.
     destruct (F_R FTH).
     rewrite Rmul_comm.
     apply Rmul_min1_a_l.
   Qed.
   Hint Rewrite Rmul_min1_a_r: pk.
   
   Lemma Ropp_1_not_0: pkopp 1:%p <> 0:%p.
   Proof.
     rewrite Ropp_pkmul.
     destruct (pKfth p_prime).
     destruct F_R.
     rewrite Rmul_comm.
     rewrite Rmul_1_l.
     intro.
     inversion H.
     apply mod_0_neq_min_1 in H1.
     inversion H1.
   Qed.
   Hint Resolve Ropp_1_not_0: pk.
   
   Lemma Ropp_0_0: pkopp 0 :%p = 0 :%p.
     intros.
     destruct (F_R FTH).
     replace (pkopp 0:%p) with (pkplus 0:%p (pkopp 0:%p)).
     apply Ropp_def.
     apply Ropp_def.
   Qed.
   Hint Rewrite Ropp_0_0: pk.

   Lemma Radd_0_r : forall x, pkplus x (pkO p) = x.
   Proof.
     destruct (F_R FTH).
     intros.
     rewrite Radd_comm.
     apply Radd_0_l.
   Qed.
   Hint Rewrite Radd_0_r: pk.
   
   Lemma Rmul_non_0: forall a b, pkmul a b <> 0:%p -> a <> 0:%p /\ b <> 0:%p.
   Proof.
     intros.
     destruct FTH.
     inversion F_R; subst; clear F_R.

     split.
     intro Hcontra;
       rewrite Hcontra in H;
       rewrite Rmul_zero_l in H;
       contradiction.
     intro Hcontra;
     rewrite Hcontra in H;
     rewrite Rmul_zero_r in H;
     contradiction.
   Qed.
   Hint Resolve Rmul_non_0: pk.

   Lemma Rplus_opp: forall a b,
       pkopp (pkplus b a) = pkplus (pkopp b) (@pkopp p a).
   Proof.
     intros.
     ring.
   Qed.
   Hint Rewrite Rplus_opp: pk.
   
   Lemma Rsub_add_distr: forall a b c,
       pksub (pkplus b c) (pkplus b a) = @pksub p c a.
   Proof.
     intros.   
     ring.
   Qed.
   Hint Rewrite Rsub_add_distr: pk.

   Lemma Rsub_distr_l: forall x y z,
       pkmul (pksub x y) z = pksub (pkmul x z) (@pkmul p y z).
   Proof.
     intros. 
     ring.
   Qed.
   Hint Rewrite Rsub_distr_l: pk.
   
   Lemma Rmul_both_sides: forall a b c,
       a = b -> pkmul a c = @pkmul p b c.
   Proof.
     intros.     
     rewrite H.
     reflexivity.
   Qed.
   Hint Resolve Rmul_both_sides: pk.

   (** TODO *)
   Lemma Rmul_non_zero_0: forall a b,
       b <> 0:%p -> pkmul a b = 0:%p -> a = 0:%p.
   Proof.
     intros.
     destruct (eq_field a 0:%p).
     assumption.
     destruct a.
     destruct b.
     unfold pkmul, GZnZ.mul in *.
     cbn in *.
     apply zirr.
     cbn.
     inversion H0.
     cbn in H2.
   Admitted.
     
   Lemma Rsub_mul_1_inv:
     forall a b, pksub (pkmul a b) 1:%p = 0:%p -> pkinv a = b.
   Proof.
     intros.
     destruct (FTH).
     inversion F_R.
     destruct (eq_field a 0:%p).
     (** a = 0 *)
     subst.
     destruct (pKfth p_prime).
     destruct F_R.
     rewrite Rmul_zero_l in H.
     rewrite Rsub_def in H.
     rewrite Radd_0_l in H.
     apply Ropp_1_not_0 in H.
     contradiction.

     replace (1:%p) with (pkmul (pkinv a) a) in H.
     rewrite Rmul_comm in H.
     rewrite <- Rsub_distr_l in H.
     pose proof (@Rmul_non_zero_0 (pksub b (pkinv a)) a n).
     apply H0 in H.
     replace (pkinv a) with (pkplus 0:%p (pkinv a)).
     rewrite <- H.
     rewrite Rsub_def.
     rewrite <- Radd_assoc.
     replace (pkplus (pkopp (pkinv a)) (pkinv a)) with (pkplus (pkinv a) (pkopp (pkinv a))).
     
     rewrite Ropp_def.
     rewrite Radd_comm.
     rewrite Radd_0_l.
     reflexivity.
     apply Radd_comm.
     apply Radd_0_l.
     apply Finv_l.
     exact n.
   Qed.     

   Lemma Rsub_a_0: forall a, pksub a a = 0:%p.
   Proof.
     intro a.
     destruct (FTH).
     destruct F_R.
     rewrite Rsub_def.
     rewrite Ropp_def.
     reflexivity.
   Qed.
   Hint Rewrite Rsub_a_0: pk.

   Lemma Ropp_mul_l: forall x y, pkopp (pkmul x y) = @pkmul p (pkopp x) y.
   Proof.
     intros.
     destruct (F_R FTH).
     rewrite <- (Radd_0_l (pkmul (pkopp x) y)).
     rewrite Radd_comm, <-(Ropp_def (pkmul x y)).
     rewrite Radd_assoc, <- Rdistr_l.
     rewrite (Radd_comm (pkopp x)), Ropp_def.
     rewrite Rmul_zero_l, Radd_0_l. 
     reflexivity.
   Qed.
   Hint Rewrite Ropp_mul_l: pk.
   
   Lemma Ropp_opp: forall x, pkopp (@pkopp p x) = x.
   Proof.
     intros.
     destruct (F_R FTH).
     rewrite <- (Radd_0_l (pkopp (pkopp x))).
     rewrite <- (Ropp_def x).
     rewrite <- Radd_assoc, Ropp_def.
     rewrite (Radd_comm x); now apply Radd_0_l.
   Qed.
   Hint Rewrite Ropp_opp: pk.
   
   Lemma Rmul_min1_min1:
     pkmul (-1):%p (-1):%p = 1:%p.
   Proof.
     destruct (F_R FTH).
     replace ((-1):%p) with (pkmul (-1):%p 1:%p) by (apply Rmul_1_r).
     rewrite Rmul_min1_a_l.
     rewrite <- Ropp_mul_l.
     rewrite Rmul_1_l.
     rewrite Ropp_opp.
     reflexivity.
   Qed.
   Hint Rewrite Rmul_min1_min1: pk.

End GaloisField.
  
