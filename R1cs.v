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

(**
   1. Use a state monad to compile equations to R1CS
   2. R1CS semantics: 
        For some z = vars ++ [1] ++ inputs, <A*z, B*z> = C*z
   3. Use https://apps.cs.utexas.edu/tech_reports/reports/tr/TR-2112.pdf
      for compilation
   4. Prove each rewrite rule according to circuit_equiv.
   5. Given rules: { 
              proof1: tm_eq ~ eq_check,
              proof2: tm_div ~ div_check,
              proof3: tm_ifthenelse ~ ite_check,
              ...
            }
      And (e: exp) -> e_check: R1CS and proof proof_e: e ~ e_check.
 *)
Module R1CS(PF: GaloisField).
  Import PF.
  Import VectorNotations.
  Set Printing Implicit.
  Definition Vfp := Vector.t Fp.
  
  Inductive term: nat -> nat -> nat -> Set :=
  | input: forall (n: nat), term (S n) 0 0
  | output: forall (n: nat), term 0 (S n) 0
  | var: forall (n: nat), term 0 0 (S n)
  | one: term 0 0 0.

  Inductive additions: nat -> nat -> nat -> Type :=
  | ahead: forall i o v, Fp * term i o v -> additions i o v
  | atail: forall i o v i' o' v',
      Fp * term i o v ->
      additions i' o' v' ->
      additions (max i i') (max o o') (max v v').
  
  Inductive constraint: nat -> nat -> nat -> Type :=
  | lc: forall i o v i' o' v' i'' o'' v''
      (A: additions i o v)
      (B: additions i' o' v')
      (C: additions i'' o'' v''),
      constraint (max i (max i' i'')) (max o (max o' o'')) (max v (max v' v'')).

  Inductive r1cs: nat -> nat -> nat -> nat -> Type :=
  | rnil: r1cs 0 0 0 0
  | rcons: forall n i o v i' o' v',
      constraint i o v ->
      r1cs n i' o' v' ->
      r1cs (S n) (max i i') (max o o') (max v v').

  
  Arguments additions {i} {o} {v}.
  Arguments ahead {i} {o} {v}.
  Arguments atail {i} {o} {v} {i'} {o'} {v'}.
  Arguments constraint {i} {o} {v}.
  Arguments lc {i} {o} {v} {i'} {o'} {v'} {i''} {o''} {v''}.
  Arguments rcons {n} {i} {o} {v} {i'} {o'} {v'}.
  Arguments r1cs {n} {i} {o} {v}.

  Definition r1cs_singleton{i o v}(c: @constraint i o v) :=
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
  
  Notation "z 'o[' n ']'" :=
    (to_p z, output n%nat)
      (in custom r1cs at level 4,
          n constr,
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
  Eval cbn in <[ { (3o[0] + 3i[1]) * (3i[0] + 2v[2]) == ([1]) };{ (3o[0] + 3i[1]) * (3i[0] + 2v[2]) == ([1]) }  ]>.   

  Fixpoint eval_additions{i o v i' o' v'}
           (adds: @additions i o v)
           (inputs: Vfp i')
           (outputs: Vfp o')
           (vars: Vfp v'): i <= i' -> o <= o' -> v <= v' -> Fp.
    invert adds; intros.
    - invert H; invert H4.
      + apply le_lt_Sn_m in H0; clear H1 H2.
        exact (pkmul H3 (Vector.nth inputs (Fin.of_nat_lt H0))).  (** Fp * Input term *)
      + apply le_lt_Sn_m in H1; clear H0 H2.
        exact (pkmul H3 (Vector.nth outputs (Fin.of_nat_lt H1))). (** Fp * Output term *)
      + apply le_lt_Sn_m in H2; clear H0 H1.
        exact (pkmul H3 (Vector.nth vars (Fin.of_nat_lt H2))).    (** Fp * Var term *)
      + exact H3. (** Fp * 1 (One) term *)
    - specialize (eval_additions _ _ _ _ _ _ H0 inputs outputs vars) as Hprev.
      pose proof (Nat.max_lub_r _ _ _ H1).
      pose proof (Nat.max_lub_r _ _ _ H2).
      pose proof (Nat.max_lub_r _ _ _ H3).
      pose proof (Nat.max_lub_l _ _ _ H1).
      pose proof (Nat.max_lub_l _ _ _ H2).
      pose proof (Nat.max_lub_l _ _ _ H3).
      clear H1 H2 H3.
      invert H; invert H2.
      + apply le_lt_Sn_m in H7; clear H8 H9.
        exact (pkplus (Hprev H4 H5 H6) (pkmul H1 (Vector.nth inputs (Fin.of_nat_lt H7)))).
      + apply le_lt_Sn_m in H8; clear H7 H9.
        exact (pkplus (Hprev H4 H5 H6) (pkmul H1 (Vector.nth outputs (Fin.of_nat_lt H8)))).
      + apply le_lt_Sn_m in H9; clear H7 H8.
        exact (pkplus (Hprev H4 H5 H6) (pkmul H1 (Vector.nth vars (Fin.of_nat_lt H9)))).
      + exact (pkplus (Hprev H4 H5 H6) H1).
  Defined.

  Fixpoint eval_constraint{i o v i' o' v'}
           (ctr: @constraint i o v)
           (inputs: Vfp i')
           (outputs: Vfp o')
           (vars: Vfp v') : i <= i' -> o <= o' -> v <= v' -> Fp.
    invert ctr.
    intros.
    pose proof (Nat.max_lub_r _ _ _ H).
    pose proof (Nat.max_lub_r _ _ _ H0).
    pose proof (Nat.max_lub_r _ _ _ H1).
    pose proof (Nat.max_lub_l _ _ _ H).
    pose proof (Nat.max_lub_l _ _ _ H0).
    pose proof (Nat.max_lub_l _ _ _ H1).
    pose proof (Nat.max_lub_r _ _ _ H2).
    pose proof (Nat.max_lub_r _ _ _ H3).
    pose proof (Nat.max_lub_r _ _ _ H4).
    pose proof (Nat.max_lub_l _ _ _ H2).
    pose proof (Nat.max_lub_l _ _ _ H3).
    pose proof (Nat.max_lub_l _ _ _ H4).    
    clear H H0 H1 H2 H3 H4.
    pose proof (eval_additions A inputs outputs vars H5 H6 H7) as SumA.
    pose proof (eval_additions B inputs outputs vars H11 H12 H13) as SumB.
    pose proof (eval_additions C inputs outputs vars H8 H9 H10) as SumC.
    exact (pksub (pkmul SumA SumB) SumC). (** A * B - C *)
  Defined.

  Import VectorNotations.
  Fixpoint eval_fix{n i o v i' o' v'}
           (r: @r1cs n i o v)
           (inputs: Vfp i')
           (outputs: Vfp o')
           (vars: Vfp v'): i <= i' -> o <= o' -> v <= v' -> Vfp n.
  Proof.
    intros.
    invert r.
    - exact [].
    - pose proof (Nat.max_lub_r _ _ _ H).
      pose proof (Nat.max_lub_l _ _ _ H).
      pose proof (Nat.max_lub_r _ _ _ H0).
      pose proof (Nat.max_lub_l _ _ _ H0).
      pose proof (Nat.max_lub_r _ _ _ H1).
      pose proof (Nat.max_lub_l _ _ _ H1).      
      pose proof (eval_fix _ _ _ _ _ _ _ H3 inputs outputs vars H4 H6 H8) as Hprev.
      pose proof (eval_constraint H2 inputs outputs vars H5 H7 H9) as CtrEval.
      exact (CtrEval :: Hprev). 
  Defined.

  Definition eval{n i o v i' o' v'}
             (r: @r1cs n i o v)(inputs: Vfp i')(outputs: Vfp o')(vars: Vfp v')
             {Hi: i <= i'} {Ho: o <= o'} {Hv: v <= v'} :=
    @eval_fix n i o v i' o' v' r inputs outputs vars Hi Ho Hv.
  
  Definition correct_lt{n i o v i' o' v'}
             (r: @r1cs n i o v)(inputs: Vfp i')(outputs: Vfp o')(vars: Vfp v')
             {Hi: i <= i'}{Ho: o <= o'}{Hv: v <= v'}: Prop :=
    let values := @eval n i o v i' o' v' r inputs outputs vars Hi Ho Hv in
    Vector.Forall (fun v => v = 0:%p) values.

  Definition correct{n i o v}(r: @r1cs n i o v)(inputs: Vfp i)(outputs: Vfp o)(vars: Vfp v): Prop :=
    @correct_lt n i o v i o v r inputs outputs vars (Nat.le_refl i)(Nat.le_refl o)(Nat.le_refl v).
             
End R1CS.
