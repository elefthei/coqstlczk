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

Module Anf(PF: GaloisField).
  Import PF.
  Include Stlc PF.
  Import ListNotations.
  Local Open Scope nat_scope.
  
  Inductive anfexp : Set :=
  | Let(l: aexp)(e: anfexp)
  | Value(v: value)
  with value: Set :=
  | CField(f: Fp)
  | Var_f(s: var)
  | CBoolean(b: bool)
  | Var_b(v: nat)
  | Lambda(e: anfexp)
  with aexp: Set :=
  | App(f: value)(v: value)
  | Select(c: value)(t: value)(e: value)
  | Primop(o: op) (l: value) (r: value)
  | Eq(l: value)(r: value)
  | Not(l: value).

  Fixpoint subst_anfexp(e: anfexp)(n: nat)(val: value): anfexp :=
    match e with
    | Let l e => Let (subst_aexp l n val) (subst_anfexp e n val)
    | Value v => Value (subst_value v n val)
    end
  with subst_value(e: value)(v: nat)(val: value): value :=
         match e with
         | Var_b b => if b =? v then val else Var_b b
         | Lambda e => Lambda (subst_anfexp e v val)
         | o => o
         end
  with subst_aexp(e: aexp)(v: nat)(val: value): aexp :=
         match e with
         | App f a => App (subst_value f v val) (subst_value a v val)
         | Select c t e => Select (subst_value c v val)
                                 (subst_value t v val)
                                 (subst_value e v val)
         | Primop o l r => Primop o
                                 (subst_value l v val)
                                 (subst_value r v val)
         | Eq l r => Eq (subst_value l v val)
                       (subst_value r v val)
         | Not l => Not (subst_value l v val)
         end.

  Fixpoint shift_aexp(e: aexp)(v: nat): aexp :=
    match e with
    | App f a => App (shift_value f v) (shift_value a v)
    | Select c t e => Select (shift_value c v)
                            (shift_value t v)
                            (shift_value e v)
    | Primop o l r => Primop o
                            (shift_value l v)
                            (shift_value r v)
    | Eq l r => Eq (shift_value l v)
                  (shift_value r v)
    | Not l => Not (shift_value l v)
    end
  with shift_anfexp(e: anfexp)(n: nat): anfexp :=
    match e with
    | Let l e => Let (shift_aexp l n) (shift_anfexp e n)
    | Value v => Value (shift_value v n)
    end
  with shift_value(e: value)(v: nat): value :=
         match e with
         | Var_b b => Var_b (b + v)
         | Lambda e => Lambda (shift_anfexp e v)
         | o => o
         end.
  
  Fixpoint binders_aexp(e: aexp): list nat :=
    match e with
    | App f a => binders_value f ++ binders_value a
    | Select c t e => binders_value c ++ binders_value t ++ binders_value e
    | Primop o l r => binders_value l ++ binders_value r
    | Eq l r => binders_value l ++ binders_value r
    | Not l => binders_value l
    end
  with binders_anfexp(e: anfexp): list nat :=
    match e with
    | Let l e => binders_aexp l ++ binders_anfexp e
    | Value v => binders_value v
    end
  with binders_value(e: value): list nat :=
         match e with
         | Var_b b => [b]
         | o => []
         end.

  Definition shift(n: nat)(l: list aexp): list aexp :=
    map (fun e => shift_aexp e n) l.
  
  Definition max_binder(e: list aexp): nat :=
    list_max (flat_map binders_aexp e).

  Fixpoint substitute(n: nat)(v: value)(l: list aexp): list aexp :=
    match l with
    | [] => []
    | h :: ts => subst_aexp h n v :: substitute (S n) (shift_value v 1) ts
    end.
  
  Fixpoint anf_translate (e: exp): anfexp :=
    let fix make_lets(l: list aexp)(v: value): anfexp :=
        match l with
        | [] => Value v
        | h :: ts => Let h (make_lets ts v)
        end in
    let fix translate_helper(e: exp): (list aexp * value) :=
        match e with
        | tm_var_b n => ([], Var_b n)
        | tm_var_f x => ([], Var_f x)
        | tm_abs _ e => ([], Lambda (anf_translate e))
        | tm_app e1 e2 =>
          let (es1, v1) := translate_helper e1 in
          let (es2, v2) := translate_helper e2 in
          let n := length es1 in
          let m := length es2 in
          (es1 ++ shift n es2 ++ [App (shift_value v1 m) v2], Var_b 0)
        | tm_let e1 e2 =>
          let (es1, v1) := translate_helper e1 in
          let (es2, v2) := translate_helper e2 in
          let n := length es1 in
          let m := length es2 in
          (es1 ++ (substitute 0 v1 es2), v2)
        | tm_constant (const_field f) => ([], CField f)
        | tm_constant (const_bool b) => ([],  CBoolean b)
        | tm_binop e1 op e2 =>
          let (es1, v1) := translate_helper e1 in
          let (es2, v2) := translate_helper e2 in
          let n := length es1 in
          let m := length es2 in
          (es1 ++ shift n es2 ++ [Primop op (shift_value v1 m) v2], Var_b 0)
        | tm_eq e1 e2 =>
          let (es1, v1) := translate_helper e1 in
          let (es2, v2) := translate_helper e2 in
          let n := length es1 in
          let m := length es2 in
          (es1 ++ shift n es2 ++ [Eq (shift_value v1 m) v2], Var_b 0)
        | tm_not e =>
          let (es, v) := translate_helper e in
          (es ++ [Not v], Var_b 0)
        | tm_ifthenelse c e1 e2 =>
          let (ce, vc) := translate_helper c in
          let (es1, v1) := translate_helper e1 in
          let (es2, v2) := translate_helper e2 in
          let size_ce := length ce in
          let size_es1 := length es1 in
          let size_es2 := length es2 in
          (ce ++ shift size_ce es1 ++ shift (size_ce + size_es1) es2 ++
              [Select (
                   shift_value vc (size_es1 + size_es2)) (shift_value v1 size_es2) v2], Var_b 0)
        end in
    let (defs, ans) := translate_helper e in
    make_lets defs ans.
 
  Definition foo :=
    <{ \_: Bool,
           let #0 && #0 in
           let #0 || #1 in
           #0 || #0 }>.

  Definition bar :=
    <{ \_: Bool,
           let #0 || #0 in
           if #0 then #1 else #1 && #1
     }>.
             
    Compute anf_translate bar.
    Compute anf_translate foo.
End Anf.
      
        
                    
                             
                                                               
                                          
