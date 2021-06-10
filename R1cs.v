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

Set Implicit Arguments.
Set Printing Implicit.
Set Transparent Obligations.

Module R1CS(PF: GaloisField).
  Import PF.
  Import VectorNotations.
  Import ListNotations.
 
  Definition Vfp := Vector.t Fp.
  
  Class Computable a := {
    (** With more inputs/vars *)
    eval_lt{i v i' v'}(circ: a i v)(inputs: Vfp i')(vars: Vfp v')(out: Fp): i <= i' -> v <= v' -> list Fp;
    
    (** With exact inputs/vars *)
    eval{i v}(circ: a i v)(inputs: Vfp i)(vars: Vfp v)(out: Fp): list Fp :=
      eval_lt circ inputs vars out (Nat.le_refl i)(Nat.le_refl v);
    
    (** Substitute the 0th input with val *)
    substitute{i v}(circ: a i v)(val: Fp): a (i-1)%nat v;

    (** Does it sum to zero *)
    correct{i v}(circ: a i v)(inputs: Vfp i)(vars: Vfp v)(out: Fp): Prop :=
      let values := eval circ inputs vars out in
      List.Forall (fun v => v = 0:%p) values
                                       }.

  (** R1CS language definition *)
  Inductive term: nat -> nat -> Set :=
  | input(m: Fp): forall (n: nat), term (S n) 0
  | output(m: Fp): term 0 0
  | var(m: Fp): forall (n: nat), term 0 (S n)
  | one(m: Fp): term 0 0.

  Inductive additions: nat -> nat -> Type :=
  | ahead: forall i v, term i v -> additions i v
  | atail: forall i v i' v',
      term i v ->
      additions i' v' ->
      additions (max i i') (max v v').
  
  Inductive constraint: nat -> nat -> Type :=
  | lc: forall i v i' v' i'' v''
      (A: additions i v)
      (B: additions i' v')
      (C: additions i'' v''),
      constraint (max i (max i' i'')) (max v (max v' v'')).

  Inductive r1cs: nat -> nat -> Type :=
  | rhead: forall i v, constraint i v -> r1cs i v
  | rtail: forall i v i' v',
      constraint i v ->
      r1cs i' v' ->
      r1cs (max i i') (max v v').
  
  Arguments additions {i} {v}.
  Arguments ahead {i} {v}.
  Arguments atail {i} {v} {i'} {v'}.
  Arguments constraint {i} {v}.
  Arguments lc {i} {v} {i'} {v'} {i''} {v''}.
  Arguments rhead {i} {v}.
  Arguments rtail {i} {v} {i'} {v'}.
  Arguments r1cs {i} {v}.
  
  Definition r1cs_singleton{i v}(c: @constraint i v) :=
    rhead c.

  (** syntax *)
  Declare Custom Entry r1cs.

  Notation "<[ a ]>" :=
    (rhead a) (at level 1, a custom r1cs at level 2).
  
  Notation "<[ a1 ; .. ; a2 ; a3 ]>" :=
    (rtail a1 .. (rtail a2 (rhead a3)) ..)
      (at level 1,
       a1 custom r1cs at level 2,
       a2 custom r1cs at level 2,
       a3 custom r1cs at level 2).
  
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
    (input (to_p z) n%nat)
      (in custom r1cs at level 4,
          n constr,
          z constr).
  
  Notation "z 'o'" :=
    (output (to_p z))
      (in custom r1cs at level 4,
          z constr).
  
  Notation "z 'v[' n ']'" :=
    (var (to_p z) n%nat)
      (in custom r1cs at level 4,
          n constr,
          z constr).

  Notation "[ z ]" :=
    (one (to_p z))
      (in custom r1cs at level 4,
          z constr at level 0).

  Coercion r1cs_singleton: constraint >-> r1cs.
  Eval cbn in <[
                { (3o + 3i[1]) * (3i[0] + 2v[2]) == ([1]) };
              { (3o + 3i[1]) * (3i[0] + 2v[2]) == ([1]) }  ]>.   


  Fixpoint eval_additions{i v i' v'}
           (adds: @additions i v)
           (inputs: Vfp i')
           (vars: Vfp v')
           (output: Fp): i <= i' -> v <= v' -> Fp.
    invert adds; intros.
    - invert H.
      + apply le_lt_Sn_m in H0.
        exact (pkmul m (Vector.nth inputs (Fin.of_nat_lt H0))).  (** Fp * Input term *)
      + exact (pkmul m output). (** Fp * Output term *)
      + apply le_lt_Sn_m in H1.
        exact (pkmul m (Vector.nth vars (Fin.of_nat_lt H1))).    (** Fp * Var term *)
      + exact m. (** Fp * 1 (One) term *)
    - specialize (eval_additions _ _ _ _ H0 inputs vars output) as Hprev.
      pose proof (Nat.max_lub_r _ _ _ H1).
      pose proof (Nat.max_lub_r _ _ _ H2).
      pose proof (Nat.max_lub_l _ _ _ H1).
      pose proof (Nat.max_lub_l _ _ _ H2).
      clear H1 H2.
      invert H.
      + apply le_lt_Sn_m in H5.
        exact (pkplus (Hprev H3 H4) (pkmul m (Vector.nth inputs (Fin.of_nat_lt H5)))).
      + exact (pkplus (Hprev H3 H4) (pkmul m output)).
      + apply le_lt_Sn_m in H6.
        exact (pkplus (Hprev H3 H4) (pkmul m (Vector.nth vars (Fin.of_nat_lt H6)))).
      + exact (pkplus (Hprev H3 H4) m).
  Defined.

  
  Fixpoint eval_constraint{i v i' v'}
           (ctr: @constraint i v)
           (inputs: Vfp i')
           (vars: Vfp v')
           (output: Fp): i <= i' -> v <= v' -> Fp.
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
    pose proof (eval_additions A inputs vars output H4 H5) as SumA.
    pose proof (eval_additions B inputs vars output H6 H8) as SumB.
    pose proof (eval_additions C inputs vars output H3 H7) as SumC.
    exact (pksub (pkmul SumA SumB) SumC). (** A * B - C *)
  Defined.
  
  Fixpoint eval_fix{i v i' v'}
           (r: @r1cs i v)
           (inputs: Vfp i')
           (vars: Vfp v')
           (output: Fp) : i <= i' -> v <= v' -> list Fp.
  Proof.
    intros.
    invert r.
    - pose proof (eval_constraint H1 inputs vars output H H0) as Hhead.
      exact [Hhead]%list.
    - pose proof (Nat.max_lub_r _ _ _ H).
      pose proof (Nat.max_lub_l _ _ _ H).
      pose proof (Nat.max_lub_r _ _ _ H0).
      pose proof (Nat.max_lub_l _ _ _ H0).
      pose proof (eval_fix _ _ _ _ H2 inputs vars output H3 H5) as Hprev.
      pose proof (eval_constraint H1 inputs vars output H4 H6) as CtrEval.
      exact (CtrEval :: Hprev)%list.
  Defined.

  (** Substitute [v / inp[1]], and [inp[n] / inp[S n]] *)

  Definition substitute_inp{i v}(a: @term i v)(n: Fp): @term (i-1) v :=
    match a in (@term n v) return (@term (n-1) v) with
    | input m 0 => one (pkmul m n)
    | input m (S a) => input m a
    | output m => output m
    | var m n => var m n
    | one m => one m
    end.

  Program Fixpoint substitute_additions{i v}(a: @additions i v)(inp: Fp): @additions (i-1) v :=
    match a with
    | ahead h => ahead (substitute_inp h inp)
    | atail h ts => atail (substitute_inp h inp) (substitute_additions ts inp)
    end.
  Next Obligation. apply Nat.sub_max_distr_r. Defined.

  Program Fixpoint substitute_constraint{i v}(ctr: @constraint i v)(v: Fp) :=
    match ctr in @constraint i v return (@constraint (i-1) v) with
    | lc a b c =>
      lc (substitute_additions a v) (substitute_additions b v) (substitute_additions c v)
    end.
  Next Obligation. rewrite Nat.sub_max_distr_r; apply Nat.sub_max_distr_r. Defined.

  Program Fixpoint substitute_r1cs{i v}(r: @r1cs i v)(k: Fp): @r1cs (i-1) v :=
    match r with
    | rhead c => rhead (substitute_constraint c k)
    | rtail h ts => rtail (substitute_constraint h k) (substitute_r1cs ts k)
    end.
  Next Obligation. apply Nat.sub_max_distr_r. Defined.

  (** Use those as the public interface to r1cs *)
  Instance Computable_additions: Computable (@additions) :=
    {
    eval_lt{i v i' v'}(circ: @additions i v)(inputs: Vfp i')(vars: Vfp v')(out: Fp) :=
      fun Hi Hv => [ @eval_additions i v i' v' circ inputs vars out Hi Hv]%list;

    substitute := @substitute_additions
    }.

  Instance Computable_constraint: Computable (@constraint) :=
    {
    eval_lt{i v i' v'}(circ: @constraint i v)(inputs: Vfp i')(vars: Vfp v')(out: Fp) :=
      fun Hi Hv => [ @eval_constraint i v i' v' circ inputs vars out Hi Hv]%list;
    
    substitute := @substitute_constraint
    }.
  
  Instance Computable_r1cs: Computable (@r1cs) :=
    {
    eval_lt := @eval_fix;
    
    substitute := @substitute_r1cs
    }.
  
  Lemma example_correct1:
    correct <[ { (1i[0]) * (1i[1]) == (1o) } ]> [1:%p; 1:%p] [] (1:%p).
  Proof.
    unfold correct.
    cbn.
    constructor.
    destruct FTH.
    inversion F_R.
    - autorewrite with pk using trivial.
    - constructor.
  Defined.

End R1CS.
