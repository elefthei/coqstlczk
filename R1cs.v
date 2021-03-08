Require Import Metalib.Metatheory.
From STLCZK Require Import Stlc.

Require Import Coqprime.elliptic.ZEll.
Require Import Coq.Numbers.BinNums.
Require Export FMapAVL.
Require Export Coq.Structures.OrderedTypeEx.

Module M := FMapAVL.Make(Nat_as_OT).

Module R1CS.
  Import Stlc_Fp.


  (** Maps *)
  Definition Map: Type -> Type := M.t.
  Definition find k (m: Map Fp) := M.find k m.
  Definition update (p: nat * Fp) (m: Map Fp) :=
    M.add (fst p) (snd p) m.

  Notation "k |-> v" := (pair k v) (at level 60).
  Notation "[ ]" := (M.empty Fp).
  Notation "[ p1 , .. , pn ]" := (update p1 .. (update pn (M.empty Fp)) .. ).

  Example ex1: find 3 [1 |-> fp_one, 3 |-> fp_zero] = Some fp_zero.
  Proof. reflexivity. Qed.

  
  Record Lc : Type :=
    mkLc {
        vars: Map Fp;
        const: Fp
      }.

  Record BilinearConstraint: Type :=
    mkBilinearConstraint {
        a: Lc;
        b: Lc;
        c: Lc;
      }.

  Definition R1cs := list BilinearConstraint.

  (** Evaluate LC like this: const + (sum . map (+) $ vars) == 0 *)
  Definition evalLc(ctx: Map Fp)(lc: Lc): option Fp :=
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

  Definition evalBilinearConstraint (ctx: Map Fp)(bc: BilinearConstraint) : option Fp :=
    match (evalLc ctx (a bc), evalLc ctx (b bc), evalLc ctx (c bc)) with
    | (Some a, Some b, Some c) => Some (pkplus (pkmul a b) (pkopp c))
    | (_, _, _) => None
    end.

  (** Predicates on R1cs valuations being correct *)
  Definition checkBilinearConstraint(ctx: Map Fp) (bc: BilinearConstraint) :=
    evalBilinearConstraint ctx bc = Some fp_zero.

  Definition checkR1cs(ctx: Map Fp)(r1cs: R1cs) := Forall (checkBilinearConstraint ctx) r1cs.
  
End R1CS.
