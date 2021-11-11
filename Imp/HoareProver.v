From Coq Require Import Nat.

From ExtLib Require Import
     Data.Map.FMapPositive
     Data.Set.ListSet
     Data.Positive
     Structures.Sets.

From HZK Require Import Hoare.

Set Implicit Arguments.
Set Strict Implicit.

(** The prover's computation is deterministic, 
    exceptions are just any number assignment to witnesses as this will fail in the
    verifier  *)
Inductive pcom: Type :=
| PCAsgn: forall t, var -> expr t -> pcom
| PCSkip: pcom
| PCSeq: pcom -> pcom -> pcom
| PCIf: expr <{{ Bool }}> -> pcom -> pcom -> pcom
| PCWhile: expr <{{ Bool }}> -> pcom -> pcom.

Arguments PCAsgn {t}.

(** Set of vars and number of vars *)
Fixpoint evars t (e: expr t) : list positive :=
  match e with
  | ENum _ | EBool _ => empty
  | EVar v => singleton v
  | EAdd e1 e2 | ESub e1 e2 | EMul e1 e2 | EDiv e1 e2 | EEq e1 e2  => union (evars e1)  (evars e2)
  end.

Definition envars t (e: expr t): nat := length (evars e).

Fixpoint cvars (c: com): list positive :=
  match c with
  | CAsgn v e => union (singleton v) (evars e)
  | CSkip => empty
  | CSeq c1 c2 => union (cvars c1) (cvars c2)
  | CIf a b c => union (evars a) (union (cvars b) (cvars c))
  | CWhile c b => union (evars c) (cvars b)
  | CNondet p v c => union (cvars p) (union (cvars v) (evars c))
  end.

Definition cnvars (c: com): nat := length (cvars c).

Reserved Notation "t '/' st '-e->' t'" (at level 40, st at level 39, t' at level 39).
Inductive estep: forall t, env -> expr t -> expr t -> Prop :=
| EStepVarNum: forall st k n,
    pmap_lookup k st = Some (CNum n) ->
    <{ # k }> / st -e-> <{ n }>
| EStepVarBool: forall st k b,
    pmap_lookup k st = Some (CBool b) ->
    <{ # k }> / st -e-> <{ b }>
| EStepAdd: forall st a b na nb,
    a / st -e-> (ENum na) ->
    b / st -e-> (ENum nb) ->
    <{ a + b }> / st -e-> <{ (na + nb) }>
| EStepAdd: forall st a b na nb,
    a / st -e-> (ENum na) ->
    b / st -e-> (ENum nb) ->
    <{ a + b }> / st -e-> <{ (na + nb) }>
| EStepAdd: forall st a b na nb,
    a / st -e-> (ENum na) ->
    b / st -e-> (ENum nb) ->
    <{ a + b }> / st -e-> <{ (na + nb) }>
| EStepEq: forall st a b na nb,
    a / st -e-> (ENum na) ->
    b / st -e-> (ENum nb) ->
    <{ a == b }> / st -e-> (EBool (eqb na nb))
where "t '/' st '-e->' t'" := (estep st t t').

Reserved Notation " t '/' st '-->' t' '/' st' " (at level 40, st at level 39, t' at level 39).
Inductive cstep: (env * com) -> (env * com) -> Prop :=
| CStepAsgnCong: forall x T (t t': expr T) st,
    t / st -e-> t' ->
    <{ x := t }> / st --> <{ x := t' }> / st
| CStepAsgnVal: forall x st (n: nat),
    <{ x := n }> / st --> <{ skip }> / (pmap_insert x (CNum n) st)
| CSkipSeq: forall t st,
    <{ skip; t }> / st --> <{ t }> / st
| CSkipCong: forall t1 t2 t1' st st',
    t1 / st --> t1' / st' ->
    <{ t1 ; t2 }> / st --> <{ t1' ; t2 }> / st'
| CIfTrue: forall c t1 t2 st,
    c / st -e-> <{ true }> ->
    <{ if c then t1 else t2 }> / st --> t1 / st
| CIfFalse: forall c t1 t2 st,
    c / st -e-> <{ false }> ->
    <{ if c then t1 else t2 }> / st --> t2 / st
| CIfCong: forall c c' t1 t2 st,
    c / st -e-> c' ->
    <{ if c then t1 else t2 }> / st --> <{ if c' then t1 else t2 }> / st
| CWhileStep: forall c t st,
    <{ while c do t }> / st --> <{ if c then (while c do t) else skip }> / st
where " t '/' st '-->' t' '/' st' " := (cstep (st,t) (st',t')).

Inductive trsys{A}(r: A -> A -> Prop): A -> A -> Prop :=
| Refl: forall a,
    trsys r a a
| Step: forall a b c,
    r a b ->
    trsys r b c ->
    trsys r a c.
  
Notation "t '/' st '==>' t' '/' st'" :=
  (trsys cstep (t, st) (t', st'))
  (at level 40, st at level 39, t' at level 39).

Example inverse(n: nat) :=
  <{
    X := n;
    compute [
        Y := 100 / 




