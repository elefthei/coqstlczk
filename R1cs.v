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
  Definition NMap: Type -> Type := M.t.
  Definition find k (m: NMap Fp) := M.find k m.
  Definition update (p: nat * Fp) (m: NMap Fp) :=
    M.add (fst p) (snd p) m.

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
  Definition checkR1cs(ctx: NMap Fp)(r1cs: R1cs) := Forall (checkBilinearConstraint ctx) r1cs.

  (** Helper monadic notation on options *)
  Notation "'return' e" := (Some e) (right associativity, at level 49).
  Notation "' p <- e1 ;; e2"
    := (match e1 with
        | Some p => e2
        | None => None
        end)
         (right associativity, p pattern, at level 60, e1 at next level).

  Inductive first_order: typ -> Prop :=
  | fo_field: first_order ty_field
  | fo_bool: first_order ty_bool.
  
  (** 1. We have STLC term m: [] |- m: t -> t
      2. We need R1cs r, checkR1cs r
      3. We have term m, 
         eval ctx_inp m = (r, ctx')
   *)
  (** Compilation = solving *)

  Fixpoint interp(ctx: NMap Fp)(e: exp) (normalizes: e -->* <{ fp v }>): option (Ctx * r1cs) :=
    match e with
    | tm_var_b n => (ctx, [])
    | tm_var_f x => (ctx, [])
    | tm_abs T e =>
      (ctx2, p) <- compile ctx e (lc_trans lc) ;;
      return (ctx2, p)
    | tm_app e1 e2 =>
      (ctx2, p1) <- compile ctx e
      
    | tm_let e1 e2 =>
    | tm_binop a op_div b => 
    | tm_constant c => (ctx, 

End R1CS.
