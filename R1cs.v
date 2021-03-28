Require Import Metalib.Metatheory.
From STLCZK Require Import Gadgets.

Require Import Coqprime.elliptic.ZEll.
Require Import Coq.Numbers.BinNums.
Require Export FMapAVL.
Require Export Coq.Structures.OrderedTypeEx.



Module QAP.
  Include Gadgets.
  Module M := FMapAVL.Make(Nat_as_OT).  
  (** Maps *)
  Definition NMap: Type -> Type := M.t.
  Definition find k (m: NMap Fp) := M.find k m.
  Definition update (p: nat * Fp) (m: NMap Fp) :=
    match p with
    | (f, s) => M.add f s m
    end.

  Notation "k |-> v" := (pair k v) (at level 60).
  Notation "[ ]" := (M.empty Fp).
  Notation "[ p1 , .. , pn ]" := (update p1 .. (update pn (M.empty Fp)) .. ).

  (** Linear combination sum (map (\a,b -> a* find b ctx)) + const *)
  (** eval { (3, a), (2,b) }, 4 ==> 3 * find ctx a + 2 * find ctx b + 4 *)
  Record Lc : Type :=
    mkLc {
        vars: NMap Fp;
        const: Fp
      }.

  (** eval a + eval b = eval c *)
  Record BilinearConstraint: Type :=
    mkBilinearConstraint {
        a: Lc;
        b: Lc;
        c: Lc;
      }.

  Definition R1cs := list BilinearConstraint.

  Inductive Circuit :=
  | Add (a: Circuit) (b: Circuit)
  | Mul (a: Circuit) (b: Circuit)
  | In (index: nat)
  | Witness (index: nat)
  | Const (f: Fp).
  
  (** Evaluate LC like this: const + (sum . map (+) $ vars) == 0 *)
  Definition evalLc(ctx: NMap Fp)(lc: Lc): option Fp :=
    M.fold
      (fun i v acc =>
         match acc with
         | None => None
         | Some acc =>
           match find i ctx with
           | Some vv => Some (pkplus acc (pkmul vv v))
           | None => None
           end
         end) (vars lc) (Some (const lc)).

  Definition evalBilinearConstraint (ctx: NMap Fp)(bc: BilinearConstraint) : option Fp :=
    match (evalLc ctx (a bc), evalLc ctx (b bc), evalLc ctx (c bc)) with
    | (Some a, Some b, Some c) => Some (pksub (pkmul a b) c)
    | (_, _, _) => None
    end.

  (** Predicates on R1cs valuations correct *)
  Definition checkBilinearConstraint(ctx: NMap Fp) (bc: BilinearConstraint) :=
    evalBilinearConstraint ctx bc = Some fp_zero.

  Check checkBilinearConstraint.
  Definition checkR1cs(ctx: NMap Fp)(r1cs: R1cs) : Prop := Forall (checkBilinearConstraint ctx) r1cs.

  (** Helper monadic notation on options *)
  Notation "'return' e" := (Some e) (right associativity, at level 49).
  Notation "' p <- e1 ;; e2"
    := (match e1 with
        | Some p => e2
        | None => None
        end)
         (right associativity, p pattern, at level 60, e1 at next level).

 
End QAP.

Require Import ExtLib.Data.Monads.StateMonad.
Require Import ExtLib.Structures.Monads.

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
Module R1CS.
  Include Gadgets.
  Module Pair_Nats_OT := PairOrderedType Nat_as_OT Nat_as_OT.
  Module M := FMapAVL.Make(Pair_Nats_OT).

  (** Maps *)
  Definition PMap: Type -> Type := M.t.
  Definition find k (m: PMap Fp) := M.find k m.
  Definition update (p: nat * nat * Fp) (m: PMap Fp) :=
    match p with
    | (a, b, v) => M.add (a, b) m
    end.

  Notation "k |-> v" := (pair k v) (at level 60).
  Notation "[ ]" := (M.empty Fp).
  Notation "[ p1 , .. , pn ]" := (update p1 .. (update pn (M.empty Fp)) .. ).

  Record Constraints{F: Type} (f: F) :=
    mkConstraints {
        num_witness: nat;
        num_inputs: nat;
        num_constraints: nat;
        A: PMap F; (** (num constraint, index of term i) -> Fp *)
        B: PMap F;
        C: PMap F
      }.

  Definition Constraint := state (Constraints Fp).

  Set Typeclasses Debug. 
  Definition witness: Constraint nat :=
    bind get (fun x => num_witness).
    
  (** 1. We have STLC term m: [] |- m: t -> t
      2. We need R1cs r, checkR1cs r
      3. We have term m, 
         eval ctx_inp m = (r, ctx')
   *)
  (** Compilation = solving *)
  
  
End R1CS.
