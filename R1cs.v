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
Require Import Coq.micromega.Lia.

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
  
  Definition Vfp := Vector.t Fp.
  
  Inductive term: nat -> nat -> Set :=
  | input: forall (n: nat), term (S n) 0
  | var: forall (n: nat), term 0 (S n)
  | one: term 0 0.

  Inductive additions: nat -> nat -> Type :=
  | ahead: forall m n, Fp * term m n -> additions m n
  | atail: forall a b c d,
      Fp * term a b ->
      additions c d ->
      additions (max a c) (max b d).
  
  Definition max3(a b c: nat) := max a (max b c).
  Hint Unfold max3: core.

  Inductive constraint: nat -> nat -> Type :=
  | lc: forall a b c d e f
      (A: additions a b)
      (B: additions c d)
      (C: additions e f),
      constraint (max3 a c e) (max3 b d f).

  Inductive r1cs: nat -> nat -> nat -> Type :=
  | rhead: forall m n,
      constraint m n ->
      r1cs 1 m n
  | rtail: forall a b c d n,
      constraint a b ->
      r1cs n c d ->
      r1cs (S n) (max a c) (max b d).

  Arguments additions {m} {n}.
  Arguments ahead {m} {n}.
  Arguments atail {a} {b} {c} {d}.
  Arguments constraint {a} {b}.
  Arguments lc {a} {b} {c} {d} {e} {f}.
  Arguments rhead {m} {n}.
  Arguments rtail {a} {b} {c} {d} {n}.
  Arguments r1cs {a} {b} {c}.

  (** syntax *)
  Declare Custom Entry r1cs.
  Notation "<[ e ]>" := e (e custom r1cs at level 90).
  Notation "z 'i[' n ']'" :=
    (to_p z, input n%nat)
      (in custom r1cs at level 2,
          n constr at level 0,
          z constr at level 0).
  Notation "z 'v[' n ']'" :=
    (to_p z, var n%nat)
      (in custom r1cs at level 2,
          n constr at level 0,
          z constr at level 0).
  Notation "z 1" :=
    (to_p z, one)
      (in custom r1cs at level 2,
          z constr at level 0).
  Notation "{ x }" := x (in custom r1cs, x constr).
  Notation "( a )" :=
    (ahead a) (in custom r1cs at level 4, a custom r1cs at level 2).

  Notation "( a1 + .. + a2 + a3 )" :=
    (atail a1 .. (atail a2 (ahead a3)) ..)
      (in custom r1cs at level 4,
          a1 custom r1cs at level 2,
          a2 custom r1cs at level 2,
          a3 custom r1cs at level 2).

  Notation "# a * b == c" :=
    (lc a b c)
      (in custom r1cs at level 90,
          a custom r1cs at level 4,
          b custom r1cs at level 4,
          c custom r1cs at level 4,
          left associativity).

  Coercion rhead: constraint >-> r1cs.

  Lemma le_lt_Sn_m: forall n m, S n <= m -> n < m. lia. Qed.
  
  Set Printing Implicit.
  Fixpoint eval_additions{i v i' v'}
           (adds: @additions i v)
           (inputs: Vfp i')
           (vars: Vfp v'): i <= i' -> v <= v' -> Fp.
    invert adds; intros.
    - invert H; invert H3.
      + apply le_lt_Sn_m in H0; clear H1.
        exact (pkmul H2 (Vector.nth inputs (Fin.of_nat_lt H0))). (** Fp * Input term *)
      + apply le_lt_Sn_m in H1; clear H0.
        exact (pkmul H2 (Vector.nth vars (Fin.of_nat_lt H1))).   (** Fp * Var term *)
      + exact H2. (** Fp * 1 (One) term *)
    - specialize (eval_additions _ _ _ _ H0 inputs vars) as Hprev.
      pose proof (Nat.max_lub_r _ _ _ H1).
      pose proof (Nat.max_lub_r _ _ _ H2).
      pose proof (Nat.max_lub_l _ _ _ H1).
      pose proof (Nat.max_lub_l _ _ _ H2).
      clear H1 H2.
      invert H; invert H2.
      + apply le_lt_Sn_m in H5; clear H6.
        exact (pkplus (Hprev H3 H4) (pkmul H1 (Vector.nth inputs (Fin.of_nat_lt H5)))).
      + apply le_lt_Sn_m in H6; clear H5.
        exact (pkplus (Hprev H3 H4) (pkmul H1 (Vector.nth vars (Fin.of_nat_lt H6)))).
      + exact (pkplus (Hprev H3 H4) H1).
  Defined.

  Print eval_additions.
  Fixpoint eval_constraint{i v i' v'}
           (ctr: @constraint i v)
           (inputs: Vfp i')
           (vars: Vfp v') : i <= i' -> v <= v' -> Fp.
    invert ctr.
    intros.
    unfold max3 in *.
    pose proof (Nat.max_lub_r _ _ _ H).
    pose proof (Nat.max_lub_r _ _ _ H0).
    pose proof (Nat.max_lub_l _ _ _ H).
    pose proof (Nat.max_lub_l _ _ _ H0).
    pose proof (Nat.max_lub_r _ _ _ H1).
    pose proof (Nat.max_lub_r _ _ _ H2).
    pose proof (Nat.max_lub_l _ _ _ H1).
    pose proof (Nat.max_lub_l _ _ _ H2).
    clear H H0 H1 H2.
    pose proof (eval_additions A inputs vars H3 H4) as SumA.
    pose proof (eval_additions B inputs vars H7 H8) as SumB.
    pose proof (eval_additions C inputs vars H5 H6) as SumC.
    exact (pksub (pkmul SumA SumB) SumC). (** A*B - C *)
  Defined.

  Fixpoint eval_fix{n i v i' v'}
           (r: @r1cs n i v)
           (inputs: Vfp i')
           (vars: Vfp v'): i <= i' -> v <= v' -> Vfp n.
  Proof.
    intros.
    invert r.
    - pose proof (eval_constraint H1 inputs vars H H0) as CtrEval.
      exact (Vector.cons Fp CtrEval 0 (Vector.nil Fp)).
    - pose proof (Nat.max_lub_r _ _ _ H).
      pose proof (Nat.max_lub_l _ _ _ H).
      pose proof (Nat.max_lub_r _ _ _ H0).
      pose proof (Nat.max_lub_l _ _ _ H0).         
      pose proof (eval_fix _ _ _ _ _ H2 inputs vars H3 H5) as Hprev.
      pose proof (eval_constraint H1 inputs vars H4 H6) as CtrEval.
      exact (Vector.cons Fp CtrEval n0 Hprev).
  Defined.

  Definition eval{n i v i' v'}
             (r: @r1cs n i v)(inputs: Vfp i')(vars: Vfp v')
             {Hi: i <= i'} {Hv: v <= v'} :=
    @eval_fix n i v i' v' r inputs vars Hi Hv.
  
  Definition correct_lt{n i v i' v'}
             (r: @r1cs n i v)(inputs: Vfp i')(vars: Vfp v')
             {Hi: i <= i'}{Hv: v <= v'}: Prop :=
    let values := @eval n i v i' v' r inputs vars Hi Hv in
    Vector.Forall (fun v => v = 0:%p) values.

  Definition correct{n i v}(r: @r1cs n i v)(inputs: Vfp i)(vars: Vfp v): Prop :=
    @correct_lt n i v i v r inputs vars (Nat.le_refl i)(Nat.le_refl v).
             
End R1CS.
