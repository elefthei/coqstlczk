Require Import Metalib.Metatheory.
From STLCZK Require Import Stlc.
From STLCZK Require Import Gadgets.
From STLCZK Require Import R1cs.
From STLCZK Require Import GaloisField.
From STLCZK Require Import Ltac.
From STLCZK Require Import Bool.

Require Import Coqprime.elliptic.ZEll.
Require Import Coq.Numbers.BinNums.
Require Import Coqprime.elliptic.GZnZ.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.ZArith.BinIntDef.
Import Z.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Vectors.VectorDef.

From Coq Require Import Ring.
From Coq Require Import Field.
Require Import Coq.micromega.Lia.

Module Compose(PF: GaloisField).
  Import PF.
  Include Gadget PF.
  Import ListNotations.

  Inductive curry: exp -> exp -> Prop :=
  | Curry: forall T1 T2 e, curry <{ \_: T1 * T2, e }> <{ \_: T1, \_: T2, e }>.

  Open Scope list_scope.  
  Inductive compose: exp -> exp -> exp -> Prop :=
  | Compose: forall T T' T'' e e',
      <{{ [] |- e :: (T -> T') }}> ->
      <{{ [] |- e' :: (T' -> T'') }}> ->
      compose e e' <{ \_: T, e' (e #0) }>.

  (**
     Transform lambda terms to a form ammenable to r1cs-translation
    -------------------------------------------------------------------

  <{ \_: Bool * Bool * Bool, (fst #0) && (fst (snd #0)) || (snd (snd #0)) }> --->
  <{ \_: Bool * Bool * Bool,
         let a := fst #0 in
         let b := fst (snd #0)) in
         let c := snd (snd #0)) in
         let v := a && b in v || c }> 
  
    Now for r1cs-composition
   ----------------------------

  (** a || b && c *)

  andb_check = <[ {(1 i[ 0]) * (1 i[ 1]) == (1 v[ 0])} ]>
  orb_check = <[ {(1 v[ 0] + [(-1)]) * ([1] + -1 i[ 2]) == (1 o[ 0] + [(-1)])} ]> 
         
  (** -> a && b || c *)
  Theorem composition_lemma: forall e1 e2 e' r1 r2 r',
      e1 <=*=> r1 ->
      e2 <=*=> r2 ->
      compose e1 e2 e' <=*=> r1cs_compose r1 r2 r'.
             
  (** Here's an example algorithm *)

    a = { (3[1] + 3i[1]) * (3i[2] + 2[1]) == (o[1]) }; 2 inputs, 1 output
    b = { (3o[2] + 3i[1]) * (3i[2] + 2i[3]) == (o[1]) }; 3 inputs, 2 outputs 
    
    compose :: (a: @r1cs n i o v) (b: @r1cs n' i' v' o') 
            (wires: fin i' -> option (fin o) )
            (hide: fin o -> bool){forall k: hide k = true -> exists j, wires j = some k}:
    {j' <= i'}
    1. Parallel compose a b:  a x b: r1cs 2 5 0 3
    2. For every input j of b in [1..i'], wires j = some k, 
       - remove j from i_{axb}
       - if hide[k] then 
            append v_{axb}[k'] = k, substitute i_{axb}[j] -> v[k'] in b, o[k] -> v[k'] in a
         else
            [o_{axb}[k] / i_{ax}[j]] in b 
    3. 
    forall [1..o], hide o = ,  
    
   
    compose :: (a: @r1cs 1 2 0 1) (b: @r1cs 1 3 0 2) (cfg: fin i -> fin o -> option Bool) 
    1. a x b: r1cs 2 5 0 3
    2. a o b: 
    

    # a
    i[1] -
    i[2] -   - o[1] - v[1] (private)
 

    # b
    i[1]
    i[2] - o[2] - v[1]
    i[3] - o[1]
    
   *)
End Compose.
