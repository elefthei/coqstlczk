Require Import Metalib.Metatheory.
From STLCZK Require Import Stlc.
From STLCZK Require Import Gadgets.

Require Import Coqprime.elliptic.ZEll.
Require Import Coq.Numbers.BinNums.
Require Import Coqprime.elliptic.GZnZ.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.ZArith.BinIntDef.
Import Z.
Require Import Coq.ZArith.BinInt.

Module IteGadget.
  Include Gadgets.
  
  (** Example 2: Conditional *)
  Definition ite :=
    <{ \_: Bool,
           \_: Field,
               \_: Field,
                    if #0 then #1 else #2
     }>.
  
  Definition ite_check(c: constant) :=
    <{ \_: Bool,
           \_: Field,
               \_: Field,
                   \_: Field,
                       #3 == #1 + (cast #0) * (#2 - #1)
                    
     }>.

  Definition ite_uncurried :=
    <{ \_: Bool * Field * Field,
           let fst (fst #0) in (* bool *)
           let snd (fst #0) in (* field *)
           let snd (#0) in (* field *)
           if #1 then #2 else #3
     }>.

  Definition ite_check_uncurried :=
    <{ \_: Bool * Field * Field * Field,
           let fst (fst (fst #0)) in (* bool *)
           let snd (fst (fst #0)) in (* field *)
           let snd (fst #0) in       (* field *)
           let snd #0 in             (* answer *)
           #4 == #2 + #1 * (#3 - #2)
     }>.
  
  Theorem ite_equiv: ite_curried ~~ ite_check_curried.
  Proof.
    intros.
    unfold circuit_equiv, ite, ite_check.
    intros; split; intro H; solve_stlc.
  Qed.

End Gadgets.     
