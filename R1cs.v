Require Import Metalib.Metatheory.
From STLCZK Require Import GaloisField.
From STLCZK Require Import Ltac.
Require Import Coqprime.elliptic.ZEll.
Require Import Coq.Numbers.BinNums.
Require Import Coqprime.elliptic.GZnZ.
Require Import ExtLib.Data.Monads.StateMonad.
Require Import ExtLib.Structures.Monads.
Require Import Coq.ZArith.BinIntDef.
Import Z.
Require Import Coq.Init.Nat.
Require Import Coq.Vectors.VectorDef.
Require Import Coq.Vectors.Fin.

Set Implicit Arguments.
Set Printing Implicit.

Module R1CS(PF: GaloisField).
  Import PF.
  Import VectorNotations.
  Definition Vfp := Vector.t Fp.
  
  Inductive term: nat -> nat -> Set :=
  | input: forall (n: nat), term (S n) 0
  | output: term 0 0
  | var: forall (n: nat), term 0 (S n)
  | one: term 0 0.

  Inductive additions: nat -> nat -> Type :=
  | ahead: forall i v, Fp * term i v -> additions i v
  | atail: forall i v i' v',
      Fp * term i v ->
      additions i' v' ->
      additions (max i i') (max v v').
  
  Inductive constraint: nat -> nat -> Type :=
  | lc: forall i v i' v' i'' v''
      (A: additions i v)
      (B: additions i' v')
      (C: additions i'' v''),
      constraint (max i (max i' i'')) (max v (max v' v'')).

  Inductive r1cs: nat -> nat -> nat -> Type :=
  | rnil: r1cs 0 0 0
  | rcons: forall n i v i' v',
      constraint i v ->
      r1cs n i' v' ->
      r1cs (S n) (max i i') (max v v').
  
  Arguments additions {i} {v}.
  Arguments ahead {i} {v}.
  Arguments atail {i} {v} {i'} {v'}.
  Arguments constraint {i} {v}.
  Arguments lc {i} {v} {i'} {v'} {i''} {v''}.
  Arguments rcons {n} {i} {v} {i'} {v'}.
  Arguments r1cs {n} {i} {v}.
  
  Definition r1cs_singleton{i v}(c: @constraint i v) :=
    rcons c rnil.

  (** syntax *)
  Declare Custom Entry r1cs.
  
  Notation "<[ x ; .. ; y ]>" :=
    (rcons x .. (rcons y rnil) ..)
      (at level 1,
          x custom r1cs at level 2,
          y custom r1cs at level 2,
          left associativity).

  Notation "'{' a '*' b '==' c '}'" :=
    (lc a b c)
      (in custom r1cs at level 2,
          a custom r1cs at level 3,
          b custom r1cs at level 3,
          c custom r1cs at level 3,
          left associativity).

  Notation "( a )" :=
    (ahead a) (in custom r1cs at level 3, a custom r1cs at level 4).
  
  Notation "( a1 + .. + a2 + a3 )" :=
    (atail a1 .. (atail a2 (ahead a3)) ..)
      (in custom r1cs at level 3,
          a1 custom r1cs at level 4,
          a2 custom r1cs at level 4,
          a3 custom r1cs at level 4).
  
  Notation "z 'i[' n ']'" :=
    (to_p z, input n%nat)
      (in custom r1cs at level 4,
          n constr,
          z constr).
  
  Notation "z 'o'" :=
    (to_p z, output)
      (in custom r1cs at level 4,
          z constr).
  
  Notation "z 'v[' n ']'" :=
    (to_p z, var n%nat)
      (in custom r1cs at level 4,
          n constr,
          z constr).

  Notation "[ z ]" :=
    (to_p z, one)
      (in custom r1cs at level 4,
          z constr at level 0).

  Coercion r1cs_singleton: constraint >-> r1cs.
  Eval cbn in <[
                { (3o + 3i[1]) * (3i[0] + 2v[2]) == ([1]) };
              { (3o + 3i[1]) * (3i[0] + 2v[2]) == ([1]) }  ]>.   

  Fixpoint eval_additions{i v i' v'}
           (adds: @additions i v)
           (inputs: Vfp i')
           (output: Fp)
           (vars: Vfp v'): i <= i' -> v <= v' -> Fp.
    invert adds; intros.
    - invert H; invert H3.
      + apply le_lt_Sn_m in H0.
        exact (pkmul H2 (Vector.nth inputs (Fin.of_nat_lt H0))).  (** Fp * Input term *)
      + exact (pkmul H2 output). (** Fp * Output term *)
      + apply le_lt_Sn_m in H1.
        exact (pkmul H2 (Vector.nth vars (Fin.of_nat_lt H1))).    (** Fp * Var term *)
      + exact H2. (** Fp * 1 (One) term *)
    - specialize (eval_additions _ _ _ _ H0 inputs output vars) as Hprev.
      pose proof (Nat.max_lub_r _ _ _ H1).
      pose proof (Nat.max_lub_r _ _ _ H2).
      pose proof (Nat.max_lub_l _ _ _ H1).
      pose proof (Nat.max_lub_l _ _ _ H2).
      clear H1 H2.
      invert H; invert H2.
      + apply le_lt_Sn_m in H5.
        exact (pkplus (Hprev H3 H4) (pkmul H1 (Vector.nth inputs (Fin.of_nat_lt H5)))).
      + exact (pkplus (Hprev H3 H4) (pkmul H1 output)).
      + apply le_lt_Sn_m in H6.
        exact (pkplus (Hprev H3 H4) (pkmul H1 (Vector.nth vars (Fin.of_nat_lt H6)))).
      + exact (pkplus (Hprev H3 H4) H1).
  Defined.

  Fixpoint eval_constraint{i v i' v'}
           (ctr: @constraint i v)
           (inputs: Vfp i')
           (output: Fp)
           (vars: Vfp v') : i <= i' -> v <= v' -> Fp.
    invert ctr.
    intros.
    pose proof (Nat.max_lub_r _ _ _ H).
    pose proof (Nat.max_lub_r _ _ _ H0).
    pose proof (Nat.max_lub_r _ _ _ H1).
    pose proof (Nat.max_lub_l _ _ _ H).
    pose proof (Nat.max_lub_l _ _ _ H0).
    pose proof (Nat.max_lub_l _ _ _ H1).
    pose proof (Nat.max_lub_r _ _ _ H2).
    pose proof (Nat.max_lub_l _ _ _ H2).
    clear H H0 H1 H2.
    pose proof (eval_additions A inputs output vars H4 H5) as SumA.
    pose proof (eval_additions B inputs output vars H6 H8) as SumB.
    pose proof (eval_additions C inputs output vars H3 H7) as SumC.
    exact (pksub (pkmul SumA SumB) SumC). (** A * B - C *)
  Defined.

  Import VectorNotations.
  Fixpoint eval_fix{n i v i' v'}
           (r: @r1cs n i v)
           (inputs: Vfp i')
           (output: Fp)
           (vars: Vfp v'): i <= i' -> v <= v' -> Vfp n.
  Proof.
    intros.
    invert r.
    - exact [].
    - pose proof (Nat.max_lub_r _ _ _ H).
      pose proof (Nat.max_lub_l _ _ _ H).
      pose proof (Nat.max_lub_r _ _ _ H0).
      pose proof (Nat.max_lub_l _ _ _ H0).
      pose proof (eval_fix _ _ _ _ _ H2 inputs output vars H3 H5) as Hprev.
      pose proof (eval_constraint H1 inputs output vars H4 H6) as CtrEval.
      exact (CtrEval :: Hprev). 
  Defined.

  Definition eval{n i v i' v'}
             (r: @r1cs n i v)(inputs: Vfp i')(output: Fp)(vars: Vfp v')
             {Hi: i <= i'} {Hv: v <= v'} :=
    @eval_fix n i v i' v' r inputs output vars Hi Hv.
  
  Definition correct_lt{n i v i' v'}
             (r: @r1cs n i v)(inputs: Vfp i')(output: Fp)(vars: Vfp v')
             {Hi: i <= i'}{Hv: v <= v'}: Prop :=
    let values := @eval n i v i' v' r inputs output vars Hi Hv in
    Vector.Forall (fun v => v = 0:%p) values.

  Definition correct{n i v}(r: @r1cs n i v)(inputs: Vfp i)(output: Fp)(vars: Vfp v): Prop :=
    @correct_lt n i v i v r inputs output vars (Nat.le_refl i)(Nat.le_refl v).

  Import VectorNotations.
  Unset Printing Implicit.
  Lemma example_correct1:
    correct <[ { (1i[0]) * (1i[1]) == (1o) } ]> [1:%p; 1:%p] (1:%p) [].
  Proof.
    unfold correct, correct_lt.
    cbn.
    constructor.
    destruct FTH.
    inversion F_R.
    - autorewrite with pk using trivial.
    - constructor.
  Qed.

End R1CS.
