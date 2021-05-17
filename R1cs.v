Require Import Metalib.Metatheory.
From STLCZK Require Import GaloisField.
From STLCZK Require Import Ltac.
From STLCZK Require Import NonEmpty.
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

  Class Computable(A : Type)(R: Type) :=
    {
    (** Substitute input i[0] with one, i[S n] -> i[n] *)
    subst: A -> Fp -> A;
    
    (** Get number of free inputs *)
    num_inputs: A -> nat;
    
    (** Get number of free vars *)
    num_vars: A -> nat;
    
    (** Evaluate to a number *)
    eval{i v}(a: A):
                     num_inputs a < i ->
                     num_vars a < v ->
                     Vfp i ->
                     Vfp v ->
                     Fp ->
                     R
    }.
  
  Inductive term: Set :=
  | input(f: Fp)(n: nat): term
  | var(f: Fp)(n: nat): term
  | output(f: Fp): term
  | one(f: Fp): term.


  Definition additions :=
    NonEmpty term.
  
  Inductive constraint: Set :=
  | lc (A: additions) (B: additions) (C: additions).

  Definition r1cs :=
    NonEmpty constraint.

  (** syntax *)
  Declare Custom Entry r1cs.

  Notation "<[ x ]>" :=
    (@NE_Sing constraint x) (x custom r1cs at level 99).

  Notation "x ++ y" :=
    (NE_app x y): seq_notations.
  
  Notation "'{' a '*' b '==' c '}'" :=
    (lc a b c)
      (in custom r1cs at level 80,
          a custom r1cs at level 40,
          b custom r1cs at level 40,
          c custom r1cs at level 40,
          left associativity).

  Notation "( a )" :=
    (NE_Sing a) (in custom r1cs at level 40, a custom r1cs at level 5).
  
  Notation "( a1 + .. + a2 + a3 )" :=
    (NE_Cons a1 .. (NE_Cons a2 (NE_Sing a3)) ..)
      (in custom r1cs at level 40,
          a1 custom r1cs at level 5,
          a2 custom r1cs at level 5,
          a3 custom r1cs at level 5).
  
  Notation "z 'i[' n ']'" :=
    (input (to_p z) n%nat)
      (in custom r1cs at level 5,
          n constr,
          z constr).
  
  Notation "z 'o'" :=
    (output (to_p z))
      (in custom r1cs at level 5,
          z constr).
  
  Notation "z 'v[' n ']'" :=
    (var (to_p z) n%nat)
      (in custom r1cs at level 5,
          n constr,
          z constr).

  Notation "[ z ]" :=
    (one (to_p z))
      (in custom r1cs at level 5,
          z constr at level 0).

  Definition r1cs_singleton(c: constraint): r1cs :=
    NE_Sing c.
 
  Coercion r1cs_singleton: constraint >-> r1cs.

  Local Open Scope seq_notations.
  (** An example syntax *)
  Eval cbn in
      <[ { (3o + 3i[1]) * (3i[0] + 2v[2]) == ([1]) } ]>
      ++ <[ { (3o + 3i[1]) * (3i[0] + 2v[2]) == ([1]) } ]>.
 
  #[refine] Instance term_Computable: Computable term Fp :=
    {
    subst t k :=
      match t with
      | input m 0 => one (pkmul m k)
      | input a (S n) => input a n
      | _ => t
      end;
    num_inputs t :=
      match t with
      | input f n => n
      | _ => 0%nat
      end;
    num_vars t :=
      match t with
      | var f n => n
      | _ => 0%nat
      end;
    }.
  intros i v a Hi Hv inps vars out; destruct a eqn:Ha.
  - exact (pkmul f (Vector.nth inps (Fin.of_nat_lt Hi))).
  - exact (pkmul f (Vector.nth vars (Fin.of_nat_lt Hv))).
  - exact (pkmul f out).
  - exact f.
  Defined.

  #[refine] Instance additions_Computable: Computable additions Fp :=
    {
    subst t k := NE_map (fun x => subst x k) t;
      
    num_inputs t :=
        NE_max (NE_map num_inputs t);
        
    num_vars t :=
        NE_max (NE_map num_vars t); 
    }.
  intros i v a; induction a; intros Hi Hv inps vars out.
  - rewrite NE_map_sing in Hi, Hv.
    apply NE_max_sing in Hi.
    apply NE_max_sing in Hv.
    exact (eval a Hi Hv inps vars out).
  - rewrite NE_map_cons in Hi, Hv.
    remember (num_inputs a) as ih.
    remember (NE_map num_inputs a0) as its.
    remember (num_vars a) as vh.
    remember (NE_map num_vars a0) as vts.
    apply NE_max_cons in Hv; destruct Hv.
    apply NE_max_cons in Hi; destruct Hi.
    rewrite Heqvh in H.
    rewrite Heqih in H1.
    exact (pkplus
             (IHa H2 H0 inps vars out)
             (eval a H1 H inps vars out)).
  Defined.

  #[refine] Instance constraint_Computable: Computable constraint Fp :=
    {
    subst t k :=
      match t with lc a b c => lc (subst a k) (subst b k) (subst c k) end;
                 
    num_inputs t :=
      match t with lc a b c => max (num_inputs a) (max (num_inputs b) (num_inputs c)) end;
                
    num_vars t :=
      match t with lc a b c => max (num_vars a) (max (num_vars b) (num_vars c)) end;
    }.
  intros i v a H H0 inps vars out; destruct a eqn:Ha; subst.
  apply Nat.max_lub_lt_iff in H.
  destruct H.
  apply Nat.max_lub_lt_iff in H1.
  destruct H1.
  apply Nat.max_lub_lt_iff in H0.
  destruct H0.
  apply Nat.max_lub_lt_iff in H3.
  destruct H3.
  pose proof (eval A H H0 inps vars out) as RA.
  pose proof (eval B H1 H3 inps vars out) as RB.
  pose proof (eval C H2 H4 inps vars out) as RC.
  exact (pksub (pkmul RA RB) RC).
  Defined.

  #[refine] Instance r1cs_Computable: Computable r1cs Prop :=
    {
    subst t k := NE_map (fun x => subst x k) t;
      
    num_inputs t :=
      NE_max (NE_map num_inputs t);
        
    num_vars t :=
        NE_max (NE_map num_vars t); 
    }.
  intros i v a; induction a; intros Hi Hv inps vars out.
  - rewrite NE_map_sing in Hi, Hv.
    apply NE_max_sing in Hi.
    apply NE_max_sing in Hv.
    exact (eval a Hi Hv inps vars out = 0:%p).
  - rewrite NE_map_cons in Hi, Hv.
    apply NE_max_cons in Hi.
    apply NE_max_cons in Hv.
    destruct Hi.
    destruct Hv.
    exact (IHa H0 H2 inps vars out /\ eval a H H1 inps vars out = 0:%p).
  Defined.
  
  Definition correct(r: r1cs)
             (inputs: Vfp (S (num_inputs r)))
             (output: Fp)
             (vars: Vfp (S (num_vars r))): Prop :=
    @eval r1cs Prop r1cs_Computable
     (S (@num_inputs r1cs Prop r1cs_Computable r))
     (S (@num_vars r1cs Prop r1cs_Computable r))
     r
     (Nat.lt_succ_diag_r (@num_inputs r1cs Prop r1cs_Computable r))
     (Nat.lt_succ_diag_r (@num_vars r1cs Prop r1cs_Computable r))
     inputs
     vars
     output.
     

  Import VectorNotations.
  Unset Printing Implicit.
  Lemma example_correct1:
    correct <[ { (1i[0]) * (1i[1]) == (1o) } ]> [1:%p; 1:%p] 1:%p [0:%p].
  Proof.
    unfold correct.
    
    simpl.
    Check (Nat.max_lub_lt_iff 0 1 2).
    destruct FTH.
    inversion F_R.
    - cbn. autorewrite with pk using trivial.
    - constructor.
  Qed.

End R1CS.
