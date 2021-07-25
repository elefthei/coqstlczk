Require Import Metalib.Metatheory.
Require Import Bool.


From STLCZK Require Import GaloisField.
From STLCZK Require Import Stlc.
From STLCZK Require Import R1cs.
From STLCZK Require Import Ltac.

From Coq Require Import Vectors.VectorDef.
From Coq Require Import Init.Nat.
From Coq Require Import Lists.List.

Generalizable All Variables.

Module Normalize(PF: GaloisField).
  Import PF.
  Include Stlc PF.
  Import ListNotations.
  Local Open Scope nat_scope.

  Fixpoint normalize' (e: exp): exp :=
    match e with
    | <{ if true then e else _ }> => e
    | <{ if false then _ else e }> => e
    | <{ (\_: t, e1) e2 }> => 
      open_exp_wrt_exp (normalize' e1) (normalize' e2)
    | <{ \_: _, _ }> => e (** Don't go under binders for HNF, skip heads in normalize'' *)
    | <{ (if c then \_:_, b1 else \_:_, b2) e }> =>
      let e' := normalize' e in
      <{ if {normalize' c}
         then {open_exp_wrt_exp (normalize' b1) e'}
         else {open_exp_wrt_exp (normalize' b2) e'} }>
    | <{ let e1 in e2 }> =>
      open_exp_wrt_exp (normalize' e2) (normalize' e1)
    | <{ e1 e2 }> => tm_app (normalize' e1) (normalize' e2)
    | <{ e1 == e2 }> => <{ {normalize' e1} == {normalize' e2} }>
    | <{ ! e }> => <{ ! {normalize' e} }>
    | <{ if c then e1 else e2 }> =>
      <{ if {normalize' c} then {normalize' e1} else {normalize' e2} }>
    | <{ fp f1 + fp f2 }> =>
      let s := pkplus f1 f2 in
      <{ fp s }>
    | <{ fp f1 - fp f2 }> =>
      let s := pksub f1 f2 in
      <{ fp s }>
    | <{ fp f1 * fp f2 }> =>
      let s := pkmul f1 f2 in
      <{ fp s }>
    | <{ true && true }> => <{ true }>
    | <{ false && _ }> => <{ false }>
    | <{ _ && false }> => <{ false }>
    | <{ _ || true }> => <{ true }>
    | <{ true || _ }> => <{ true }>
    | <{ false || false }> => <{ false }>
    | tm_binop e1 op e2 => tm_binop (normalize' e1) op (normalize' e2)
    | o => o
    end.

  Fixpoint normalize''(e: exp)(gas: nat): exp :=
    match gas with
    | 0%nat => e
    | S g' => normalize'' (normalize' e) g'
    end.

  Fixpoint normalize(e: exp)(gas: nat): exp :=
    match e with
    | <{ \_: t, e }> => <{ \_: t, {normalize e gas} }>
    | e => normalize'' e gas
    end.
  
  Definition foo :=
    <{ \_: Field,
           \_: Bool,
               (if #0 then
                 (\_: Field, #0 + #0)
               else
                 (\_: Field, #0 * #0)
               ) #1
     }>.

  Definition bar :=
    <{ \_: Field,
           let (\_: Field, #0 - #0) in
           #0 #1
     }>.
  Compute normalize foo 10.
  Compute normalize bar 10.

  Lemma normalize_fixpoint: forall e,
      exists g, normalize e g = e.
  Proof.
    induction e; cbn; try (exists 0; reflexivity).
    - destruct IHe.
      exists x.
      rewrite H.
      now reflexivity.
  Defined.
      
End Normalize.
      
        
                    
                             
                                                               
                                          
