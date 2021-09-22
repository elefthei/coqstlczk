Require Import Metalib.Metatheory.
Require Import Bool.


From STLCZK Require Import GaloisField.
From STLCZK Require Import Stlc.
From STLCZK Require Import R1cs.
From STLCZK Require Import Ltac.
Require Import Coqprime.elliptic.ZEll.
From Coq Require Import Vectors.VectorDef.
From Coq Require Import Init.Nat.
From Coq Require Import Lists.List.

Generalizable All Variables.

Module Normalize(PF: GaloisField).
  Import PF.
  Include Stlc PF.
  Import ListNotations.
  Local Open Scope nat_scope.

  Fixpoint normalize' (k: nat)(e: exp): exp :=
    match e with
    | <{ if true then e else _ }> => e
    | <{ if false then _ else e }> => e
    | <{ (\_: t, e1) e2 }> => 
      open_exp_wrt_exp_rec k (normalize' (S k) e1) (normalize' k e2)
    | <{ \_: _, _ }> => e (** Don't go under binders for HNF, skip heads in normalize'' *)
    | <{ (if c then \_:_, b1 else \_:_, b2) e }> =>
      let e' := normalize' k e in
      <{ if {normalize' k c}
         then {open_exp_wrt_exp_rec k (normalize' (S k) b1) e'}
         else {open_exp_wrt_exp_rec k (normalize' (S k) b2) e'} }>
    | <{ let e1 in e2 }> =>
      open_exp_wrt_exp_rec k (normalize' (S k) e2) (normalize' k e1)
    | <{ e1 e2 }> => tm_app (normalize' k e1) (normalize' k e2)
    | <{ e1 == e2 }> => <{ {normalize' k e1} == {normalize' k e2} }>
    | <{ ! e }> => <{ ! {normalize' k e} }>
    | <{ if c then e1 else e2 }> =>
      <{ if {normalize' k c} then {normalize' k e1} else {normalize' k e2} }>
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
    | tm_binop e1 op e2 => tm_binop (normalize' k e1) op (normalize' k e2)
    | o => o
    end.

  Fixpoint normalize''(e: exp)(k: nat)(gas: nat): option exp :=
    match gas with
    | 0%nat => None
    | S g' => let e' := normalize' k e in
             if eq_exp e' e then
               Some e'
             else
               normalize'' e' k  g'
    end.

  Fixpoint normalize(e: exp)(k: nat)(gas: nat): option exp :=
    match e with
    | <{ \_: t, e }> => match normalize e (S k) gas with
                       | Some e' => Some <{ \_: t, e' }>
                       | None => None
                       end
    | e => normalize'' e k gas
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

  Definition bar' :=
    <{ \_: Field,
           (\_: Field, #0 - #0) #0
     }>.
  
  Definition bar :=
    <{ \_: Field,
           let (\_: Field, #0 - #0) in
           #0 #1
     }>.
  Compute normalize foo 0 10.
  Compute normalize bar 0 10.

  Lemma normalize_fixpoint: forall e,
      exists g, g > 0 -> normalize e g = e.
  Proof.
    induction e; cbn; try (exists 1; reflexivity).
    - destruct IHe.
      exists x.
      rewrite H.
      now reflexivity.
  Defined.
      
End Normalize.
      
        
                    
                             
                                                               
                                          
