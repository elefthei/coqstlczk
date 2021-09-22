Require Import Bool.
Require Import Coqprime.elliptic.ZEll.

(** For F_p *)
Require Import Coqprime.elliptic.ZEll.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.ZArith.BinInt.

From STLCZK Require Import GaloisField.
From Coq Require Import Vectors.VectorDef.
From Coq Require Import Init.Nat.

Set Implicit Arguments.

(** Use the same reified type for the whole development *)
Inductive type : Type :=
| TBool: type
| TInt: type
| TArrow : type -> type -> type.

Module Stlc_Phoas(Import PF: GaloisField.GaloisField).
  Import PF.

  Section vars.
  Variable var : type -> Type.

  Inductive fop : Set := 
  | op_add : fop
  | op_sub : fop
  | op_mul : fop.

  Inductive bop: Set :=
  | op_and : bop
  | op_or : bop.
  
  Inductive term : type -> Type :=
  | ECField : Fp -> term TInt
  | ECBool: bool -> term TBool
         
  | EVar : forall t,
      var t
      -> term t
             
  | EApp : forall t1 t2,
      term (TArrow t1 t2)
      -> term t1
      -> term t2
  | EAbs : forall t1 t2,
      (var t1 -> term t2)
      -> term (TArrow t1 t2)

  (** Control flow *)
  | EIf: forall t, term TBool ->
         term t ->
         term t ->
         term t

  (** Prim ops *)
  | EFop: fop ->
          term TInt ->
          term TInt ->
          term TInt
  | EBop: bop ->
          term TBool ->
          term TBool ->
          term TBool
  | EFeq: term TInt ->
          term TInt ->
          term TBool
  | ENot: term TBool ->
          term TBool.
End vars.
  
Arguments EVar [var t].
Arguments ECField {var}.
Arguments ECBool {var}.
Arguments EApp [var t1 t2].
Arguments EAbs [var t1 t2].
Arguments EIf [var t].
Arguments EFop {var}.
Arguments EBop {var}.
Arguments EFeq {var}.
Arguments ENot {var}.

Fixpoint typeDenote (t : type) : Set :=
  match t with
  | TBool => bool
  | TInt => Fp
  | TArrow t1 t2 => typeDenote t1 -> typeDenote t2
  end.

Fixpoint termDenote t (e : term typeDenote t) {struct e} : typeDenote t :=
  match e in (term _ t) return (typeDenote t) with
    | EVar v => v

    | ECBool t => t
    | ECField f => f

    | EApp e1 e2 => (termDenote e1) (termDenote e2)
    | EAbs e' => fun x => termDenote (e' x)

    | EIf c e1 e2 => if (termDenote c) then (termDenote e1) else (termDenote e2)

    | EFop op_add e1 e2 => pkplus (termDenote e1) (termDenote e2)
    | EFop op_sub e1 e2 => pksub (termDenote e1) (termDenote e2)
    | EFop op_mul e1 e2 => pkmul (termDenote e1) (termDenote e2)
    | EBop op_and e1 e2 => andb (termDenote e1) (termDenote e2)
    | EBop op_or e1 e2 => orb (termDenote e1) (termDenote e2)
    | EFeq e1 e2 => if eq_field (termDenote e1) (termDenote e2) then true else false
    | ENot e1 => negb (termDenote e1)
  end.
End Stlc_Phoas.

Module DanvyOriginal.

  Definition Int := nat.

  (** The forbidden flag *)
  Unset Positivity Checking.

  Inductive Term: Type :=
  | INT: Int -> Term 
  | ADD: Term -> Term -> Term
  | APP: Term -> Term -> Term
  | LAM: (Term -> Term) -> Term.

   Inductive Exp (t: Type) :=
  | EXP: Term -> Exp t.

  Arguments EXP {t}.
  Definition int(i: Int): Exp Int :=
    EXP (INT i).
  
  Definition add(a b: Exp Int): Exp Int :=
    match a, b with
    | EXP e1, EXP e2 => EXP (ADD e1 e2)
    end.
  
  Definition app a b (f: Exp (a -> b))(o: Exp a) : Exp b :=
    match f, o with
    | EXP e1, EXP e2 => EXP (APP e1 e2)
    end.

  Definition lam a b (f: Exp a -> Exp b): Exp (a -> b) :=
    EXP (LAM (fun (x: Term) => match f (EXP x) with
                  | EXP b => b
                            end)).
   Definition coerce a (e: Exp (Exp a)): Exp a :=
    match e with
    | EXP b => EXP b
    end.

  Definition uncoerce a (e: Exp a): Exp (Exp a) :=
    match e with
    | EXP b => EXP b
    end.
      
  Class Nbe a := {
    reify: a -> Term;
    reflect: Term-> a
                }.

  Instance Nbe_lam a b {na: Nbe a} {nb: Nbe b}: Nbe (a -> b) := {
    reify v := 
      LAM (fun x => reify (v (reflect x)));
    reflect e :=
      fun x => reflect (APP e (reify x))
                                                              }.

  Unset Positivity Checking.
End DanvyOriginal.

Module DanvyPhoas(Import PF: GaloisField.GaloisField).
  Import PF.
  
  Section vars.
    Variable var : type -> Type.

    Inductive Term: type -> Type :=
    | INT: Fp -> Term TInt
    | BOOL: bool -> Term TBool
    | ADD: Term TInt -> Term TInt -> Term TInt
    | APP: forall a b, Term (TArrow a b) -> Term a -> Term b
    | VAR: forall a, var a -> Term a
    | LAM: forall a b, (var a -> Term b) -> Term (TArrow a b).
  
  Fixpoint typeDenote (t : type) : Set :=
    match t with
    | TBool => bool
    | TInt => Fp
    | TArrow t1 t2 => typeDenote t1 -> typeDenote t2
    end.

  Class Nbe (t: type) := {
    reify: typeDenote t -> Term t;
    reflect: Term t -> typeDenote t
                }.

  Instance Nbe_lam {a b: type} {na: Nbe a} {nb: Nbe b}: Nbe (TArrow a b) := {
    reify v := 
      LAM (fun x => reify (v (reflect (VAR x))));
    reflect e :=
      fun x => reflect (APP e (reify x))
                                                                   }.
  End vars.

  Arguments VAR [var a].
  Arguments INT {var}.
  Arguments BOOL {var}.
  Arguments ADD {var}.
  Arguments APP [var a b].
  Arguments LAM [var a b].
  (** Maximally insert types in class as well *)
  Arguments Nbe [var].
  Arguments Nbe_lam [var a b].
  
  Fixpoint termDenote t (e : Term typeDenote t) {struct e} : typeDenote t :=
    match e in (Term _ t) return (typeDenote t) with
    | VAR v => v
    | INT f => f
    | BOOL v => v
    | ADD f1 f2 => pkplus (termDenote f1) (termDenote f2)
    | APP e1 e2 => (termDenote e1) (termDenote e2)
    | LAM e' => fun x => termDenote (e' x)
    end.

  Instance Nbe_int : Nbe TInt := {
    reify v := INT v;

    reflect v := termDenote v;
                                }.
  Instance Nbe_bool : Nbe TBool := {
    reify v := BOOL v;
    
    reflect v := termDenote v;
                                }.
End DanvyPhoas.

Module DanvyPhoasNf(Import PF: GaloisField.GaloisField).
  Import PF.

  Section vars.
    Variable var : type -> Type.

    Fixpoint typeDenote (t : type) : Set :=
      match t with
      | TBool => bool
      | TInt => Fp
      | TArrow t1 t2 => typeDenote t1 -> typeDenote t2
      end.

    (** Danvy paper:
        data NfTerm = COERCE AtTerm | LAM (AtTerm → NfTerm)
        data AtTerm = APP AtTerm NfTerm
      + PHOAS
     *)
    Inductive NfTerm: type -> Type :=
    | NCOERCE: forall t, AtTerm t -> NfTerm t
    | LAM: forall a b, (var a -> NfTerm b) -> NfTerm (TArrow a b)
    with AtTerm: type -> Type :=
    | VAR: forall a, var a -> AtTerm a (** Is var correctly an AtTerm ? *)
    | APP: forall a b, AtTerm (TArrow a b) -> NfTerm a -> AtTerm b
    | PCOERCE: forall t, PrTerm t -> AtTerm t
    | ADD: AtTerm TInt -> AtTerm TInt -> AtTerm TInt
    with PrTerm: type -> Type :=
    | INT: Fp -> PrTerm TInt
    | BOOL: bool -> PrTerm TBool.

    Class Nbe (t: type) := {
      reify: typeDenote t -> NfTerm t;
      reflect: AtTerm t -> typeDenote t
                          }.

    Instance Nbe_lam {a b: type} {na: Nbe a} {nb: Nbe b}: Nbe (TArrow a b) := {
      reify v := 
        LAM (fun x => reify (v (reflect (VAR x))));
      reflect e :=
        fun x => reflect (APP e (reify x))
                                                                   }.
  End vars.

  Arguments VAR [var a].
  Arguments INT {var}.
  Arguments BOOL {var}.
  Arguments ADD {var}.
  Arguments NCOERCE [var t].
  Arguments APP [var a b].
  Arguments PCOERCE [var t].
  Arguments LAM [var a b].
  (** Maximally insert types in class as well *)
  Arguments Nbe [var].
  Arguments Nbe_lam [var a b].

  (** Danvy's nf and at + primitive terms Int and Bool *)
  Fixpoint nfTermDenote t (e : NfTerm typeDenote t) {struct e} : typeDenote t :=
    match e in (NfTerm _ t) return (typeDenote t) with
    | NCOERCE a => atTermDenote a
    | LAM f => fun x => nfTermDenote (f x)
    end
  with atTermDenote t (e: AtTerm typeDenote t) {struct e}: typeDenote t :=
    match e in (AtTerm _ t) return (typeDenote t) with
    | APP e1 e2 => (atTermDenote e1) (nfTermDenote e2)
    | VAR v => v
    | PCOERCE p => prTermDenote p
    | ADD f1 f2 => pkplus (atTermDenote f1) (atTermDenote f2)
    end
  with prTermDenote t (e: PrTerm typeDenote t) {struct e}: typeDenote t :=
    match e in (PrTerm _ t) return (typeDenote t) with
    | INT v => v
    | BOOL v => v
    end.

  Instance Nbe_int : Nbe TInt := {
    reify v := NCOERCE (PCOERCE (INT v));

    reflect v := atTermDenote v;
                                }.

  Instance Nbe_bool : Nbe TBool := {
    reify v := NCOERCE (PCOERCE (BOOL v));
    
    reflect v := atTermDenote v;
                                }.
End DanvyPhoasNf.

(** ScratchPAD *)         
Fixpoint termDenoteReify t (x : typeDenote t) : term typeDenote t :=
  match t return (_ = _ -> term typeDenote t) with
  | TBool => (fun _: t = x => ECBool x)
  | TField => ECField x
  | TArrow t1 t2 => EAbs (fun v => x (termDenote t1 (EVar v)))
  end.

Definition Term t := forall var, term var t.
Definition TermDenote t (e : Term t) := termDenote (e _).

Fixpoint closed_value(t: type): Term t :=
  match t with
  | TField => fun _ => ECField (0:%p)
  | TBool => fun _ => ECBool true
  | TArrow _ t2 => fun _ => EAbs (fun _ => @closed_value t2 _)
  end.

Definition input_type(t: type): type :=
  match t with
  | TArrow t1 t2 => t1
  | _ => t
  end.

Fixpoint closed t (e: term _ t): bool :=
  match e with
  | EVar v => true
  | ECBool _ => false
  | ECField _ => false
  | EApp e1 e2 => andb (closed e1) (closed e2)
  | EIf c e1 e2 => andb (closed c) (andb (closed e1) (closed e2))
  | EFop _ e1 e2 => andb (closed e1) (closed e2)
  | EBop _ e1 e2 => andb (closed e1) (closed e2)
  | EFeq e1 e2 => andb (closed e1) (closed e2)
  | ENot e => closed e
  | EAbs e' => closed (e' (closed_value ))
  end.

Definition value(t: type): Term t -> Prop :=
  match t with
  | TField => fun u => exists f: Fp, forall v, u v = ECField f
  | TBool => fun u => exists b: bool, forall v, u v = ECBool b
  | TArrow t1 t2 => fun u => forall v, exists f: v t1 -> term v t2, u v = EAbs f
  end.

Fixpoint computation(t: type): Term t -> Prop :=
  fun m => exists v, termDenote m = v

                    

Inductive fot: type -> Prop :=
| FotB: fot TBool
| FotF: fot TField.

Definition fo_term(t: type) := { e: Term t | fot t }.

End Stlc_Phoas.

Module Stlc(Import PF: GaloisField.GaloisField).
  Import PF.
  Include Stlc_Phoas PF.
  
  Declare Custom Entry stlc_ty.
  Declare Custom Entry stlc.
  
  Notation "'fp' n" := (ECField n) (in custom stlc at level 0).
  Notation "'true'"  := true (at level 1).
  Notation "'true'" := (ECBool true) (in custom stlc at level 0).
  Notation "'false'"  := false (at level 1).
  Notation "'false'" := (ECBool false) (in custom stlc at level 0).
  Notation "<{ e }>" := e (e custom stlc at level 99).
  Notation "<{{ e }}>" := e (e custom stlc_ty at level 99).
  Notation "( x )" := x (in custom stlc, x at level 99).
  Notation "( x )" := x (in custom stlc_ty, x at level 99).
  Notation "x" := x (in custom stlc at level 0, x constr at level 0).
  Notation "x" := x (in custom stlc_ty at level 0, x constr at level 0).  
  Notation "x y" := (EApp x y) (in custom stlc at level 1, left associativity).
  
  Notation "\ x , y" :=
    (EAbs (fun x => y)) (in custom stlc at level 90,
                 y custom stlc at level 80,
                 left associativity).
  Notation "\_ , y" :=
    (EAbs (fun _ => y)) (in custom stlc at level 90,
                 y custom stlc at level 80,
                 left associativity).
  
  Notation "# n" := (EVar n) (in custom stlc at level 0).
  Notation "{ x }" := x (in custom stlc at level 1, x constr).
  Notation "S -> T" := (TArrow S T) (in custom stlc_ty at level 2, right associativity).
  Notation "'Field'" := TField (in custom stlc_ty at level 0).
  Notation "'Bool'" := TBool (in custom stlc_ty at level 0).
  
  Notation "x + y" := (EFop op_add x y) (in custom stlc at level 2,
                                            left associativity).
  Notation "x - y" := (EFop op_sub x y) (in custom stlc at level 2,
                                            left associativity).
  Notation "x * y" := (EFop op_mul x y) (in custom stlc at level 1,
                                            left associativity).
  Notation "x && y" := (EBop op_and x y) (in custom stlc at level 4,
                                             left associativity).
  Notation "x || y" := (EBop op_or x  y) (in custom stlc at level 4,
                                             left associativity).
  Notation "x == y" := (EFeq x y) (in custom stlc at level 3,
                                      left associativity).
  Notation "! x " := (ENot x) (in custom stlc at level 3).

  Notation "'if' x 'then' y 'else' z" :=
    (EIf x y z) (in custom stlc at level 89,
                    x custom stlc at level 99,
                    y custom stlc at level 99,
                    z custom stlc at level 99,
                    left associativity).

Definition fals : Term <{{ Bool }}> := fun _ => <{ false }>.
Eval compute in TermDenote fals.

Definition tru : Term <{{ Bool }}> := fun _ => <{ true }>.
Eval compute in TermDenote tru.

Definition ident : Term <{{ Bool -> Bool }}> := fun _ => <{ \x , #x }>.
Eval compute in (TermDenote ident).

Definition fals_again : Term Bool := fun _ => ident _ @ fals _.
Eval compute in TermDenote fals_again.

Definition first : Term (Bool --> Bool --> Bool) := fun _ => \x, \y, #x.
Eval compute in TermDenote first.

Definition second : Term (Bool --> Bool --> Bool) := fun _ => \x, \y, #y.
Eval compute in TermDenote second.

Definition test_first : Term Bool := fun _ => first _ @ fals _ @ tru _.
Eval compute in TermDenote test_first.

Definition test_second : Term Bool := fun _ => second _ @ fals _ @ tru _.
Eval compute in TermDenote test_second.

Definition app : Term ((Bool --> Bool) --> Bool --> Bool) :=
  fun _ => \f, \x, #f @ #x.
Eval compute in TermDenote app.

Definition fals_again2 : Term Bool := fun _ => app _ @ ident _ @ fals _.
Eval compute in TermDenote fals_again2.        

Section normalize.
  Definition fo: Type -> Prop :=
    | FoBool bool_scope
  Fixpoint normalize a Term a -> 

(** CPS *)
Inductive ptype : Type :=
| PBool : ptype
| PCont : ptype -> ptype
| PUnit : ptype
| PProd : ptype -> ptype -> ptype.

Notation "'Bool'" := PBool : cps_scope.
Notation "t --->" := (PCont t) (at level 61) : cps_scope.
Notation "'Unit'" := PUnit : cps_scope.
Infix "**" := PProd (right associativity, at level 60) : cps_scope.

Bind Scope cps_scope with ptype.
Delimit Scope cps_scope with cps.

Section vars.
  Variable var : ptype -> Type.

  Variable result : ptype.

  Inductive pterm : Type :=
  | PHalt :
    var result
    -> pterm
  | PApp : forall t,
    var (t --->)
    -> var t
    -> pterm
  | PBind : forall t,
    pprimop t
    -> (var t -> pterm)
    -> pterm

  with pprimop : ptype -> Type :=
  | PVar : forall t,
    var t
    -> pprimop t
    
  | PTrue : pprimop Bool
  | PFalse : pprimop Bool
    
  | PAbs : forall t,
    (var t -> pterm)
    -> pprimop (t --->)

  | PPair : forall t1 t2,
    var t1
    -> var t2
    -> pprimop (t1 ** t2)
  | PFst : forall t1 t2,
    var (t1 ** t2)
    -> pprimop t1
  | PSnd : forall t1 t2,
    var (t1 ** t2)
    -> pprimop t2.
  Check pterm_ind.
End vars.

Arguments PHalt [var result].
Arguments PApp [var result t].
Arguments PBind [var result t].

Arguments PVar [var result t].
Arguments PTrue {var result}.
Arguments PFalse {var result}.
Arguments PAbs [var result t].
Arguments PPair [var result t1 t2].
Arguments PFst [var result t1 t2].
Arguments PSnd [var result t1 t2].

Notation "'Halt' x" := (PHalt x) (no associativity, at level 75) : cps_scope.
Infix "@@" := PApp (no associativity, at level 75) : cps_scope.
Notation "x <- p ; e" := (PBind p (fun x => e))
  (right associativity, at level 76, p at next level) : cps_scope.
Notation "! <- p ; e" := (PBind p (fun _ => e))
  (right associativity, at level 76, p at next level) : cps_scope.

Notation "# v" := (PVar v) (at level 70) : cps_scope.

Notation "'Tru'" := PTrue : cps_scope.
Notation "'Fals'" := PFalse : cps_scope.

Notation "\ x , e" := (PAbs (fun x => e)) (at level 78) : cps_scope.
Notation "\ ! , e" := (PAbs (fun _ => e)) (at level 78) : cps_scope.

Notation "[ x1 , x2 ]" := (PPair x1 x2) (at level 73) : cps_scope.
Notation "#1 x" := (PFst x) (at level 72) : cps_scope.
Notation "#2 x" := (PSnd x) (at level 72) : cps_scope.

Bind Scope cps_scope with pterm pprimop.

Local Open Scope cps_scope.

Fixpoint ptypeDenote (t : ptype) : Set :=
  match t with
    | Bool => bool
    | t' ---> => ptypeDenote t' -> bool
    | Unit => unit
    | t1 ** t2 => (ptypeDenote t1 * ptypeDenote t2)%type
  end.

Fixpoint ptermDenote result (e : pterm ptypeDenote result) (k : ptypeDenote result -> bool)
  {struct e} : bool :=
  match e with
    | PHalt v => k v
    | PApp f x => f x
    | PBind p x => ptermDenote (x (pprimopDenote p k)) k
  end

with pprimopDenote result t (p : pprimop ptypeDenote result t) (k : ptypeDenote result -> bool)
  {struct p} : ptypeDenote t :=
  match p in (pprimop _ _ t) return (ptypeDenote t) with
    | PVar v => v

    | PTrue => true
    | PFalse => false

    | PAbs e => fun x => ptermDenote (e x) k

    | PPair v1 v2 => (v1, v2)
    | PFst v => fst v
    | PSnd v => snd v
  end.

Definition Pterm result := forall var, pterm var result.
Definition Pprimop result t := forall var, pprimop var result t.
Definition PtermDenote result (e : Pterm result) := ptermDenote (e _).
Definition PprimopDenote result t (p : Pprimop result t) := pprimopDenote (p _).
                                                               
(** * CPS translation *)

(** ** Translating types *)

Fixpoint cpsType (t : type) : ptype :=
  match t with
    | Bool => Bool%cps
    | t1 --> t2 => (cpsType t1 ** (cpsType t2 --->) --->)%cps
  end%source.

(** ** Translating terms *)

Section splice.
  Local Open Scope cps_scope.

  Fixpoint splice (var : ptype -> Type) (result1 result2 : ptype) (e1 : pterm var result1) (e2 : var result1 -> pterm var result2) {struct e1} : pterm var result2 :=
    match e1 with
      | PHalt v => e2 v
      | PApp f x => f @@ x
      | PBind p e' => x <- splicePrim p e2; splice (e' x) e2
    end

  with splicePrim (var : ptype -> Type) (result1 result2 : ptype) t (p : pprimop var result1 t) (e2 : var result1 -> pterm var result2) {struct p} : pprimop var result2 t :=
    match p in (pprimop _ _ t) return (pprimop var result2 t) with
      | PVar v => #v

      | PTrue => Tru
      | PFalse => Fals

      | PAbs e => \x, splice (e x) e2

      | PPair v1 v2 => [v1, v2]

      | PFst v => #1 v
      | PSnd v => #2 v
    end.
End splice.

Notation "x <-- e1 ; e2" := (splice e1 (fun x => e2))
  (right associativity, at level 76, e1 at next level) : cps_scope.
Notation "! <-- e1 ; e2" := (splice e1 (fun _ => e2))
  (right associativity, at level 76, e1 at next level) : cps_scope.

Section cpsTerm.
  Variable var : ptype -> Type.

  Notation var' := (fun t => var (cpsType t)).

  Local Open Scope cps_scope.

  Fixpoint cpsTerm t (e : term var' t) {struct e} : pterm var (cpsType t) :=
    match e in (term _ t) return (pterm var (cpsType t)) with
      | EVar v => PHalt (var := var) v

      | ETrue => x <- Tru; Halt x
      | EFalse => x <- Fals; Halt x

      | EApp e1 e2 =>
        f <-- cpsTerm e1;
        x <-- cpsTerm e2;
        k <- \r, PHalt (var := var) r;
        p <- [x, k];
        f @@ p
      | EAbs e' =>
        f <- PAbs (var := var) (fun p =>
          x <- #1 p;
          k <- #2 p;
          r <-- cpsTerm (e' x);
          k @@ r);
        Halt f
    end.
End cpsTerm.

Arguments cpsTerm [var t].
Definition CpsTerm t (E : Term t) : Pterm (cpsType t) := fun _ => cpsTerm (E _).

(** * Correctness *)

(**
pterm_ind
     : forall P : pterm -> Prop,
       (forall v : var result, P (PHalt v)) ->
       (forall (t : ptype) (v : var (t --->)) (v0 : var t), P (PApp v v0)) ->
       (forall (t : ptype) (p : pprimop t) (p0 : var t -> pterm),
        (forall v : var t, P (p0 v)) -> P (PBind p p0)) -> forall p : pterm, P p
*)
Scheme pterm_mut := Induction for pterm Sort Prop
with pprimop_mut := Induction for pprimop Sort Prop.

Section splice_correct.
  Variables result1 result2 : ptype.

  Variable e2 : ptypeDenote result1 -> pterm ptypeDenote result2.  

  Theorem splice_correct : forall e1 k,
    ptermDenote (splice e1 e2) k
    = ptermDenote e1 (fun r => ptermDenote (e2 r) k).
    apply (pterm_mut
      (fun e1 => forall k,
        ptermDenote (splice e1 e2) k
        = ptermDenote e1 (fun r => ptermDenote (e2 r) k))
      (fun t p => forall k,
        pprimopDenote (splicePrim p e2) k
        = pprimopDenote p (fun r => ptermDenote (e2 r) k))); auto.
    equation.
  Qed.
End splice_correct.

Fixpoint lr (t : type) : typeDenote t -> ptypeDenote (cpsType t) -> Prop :=
  match t return (typeDenote t -> ptypeDenote (cpsType t) -> Prop) with
    | TBool => fun n1 n2 => n1 = n2
    | TArrow t1 t2 => fun f1 f2 =>
      forall x1 x2, lr _ x1 x2
        -> forall k, exists r,
          f2 (x2, k) = k r
          /\ lr _ (f1 x1) r
  end.

Lemma cpsTerm_correct : forall G t (e1 : term _ t) (e2 : term _ t),
  term_equiv G e1 e2
  -> (forall t v1 v2, In (vars (v1, v2)) G -> lr t v1 v2)
  -> forall k, exists r,
    ptermDenote (cpsTerm e2) k = k r
    /\ lr t (termDenote e1) r.
  Hint Rewrite splice_correct : ltamer.

  Ltac my_changer :=
    match goal with
      [ H : (forall (t : _) (v1 : _) (v2 : _), vars _ = vars _ \/ In _ _ -> _) -> _ |- _ ] =>
      match typeof H with
        | ?P -> _ =>
          assert P; [intros; push_vars; intuition; fail 2
            | idtac]
      end
    end.

  Ltac my_simpler := repeat progress (equation; fold ptypeDenote in *;
    fold cpsType in *; try my_changer).

  Ltac my_chooser T k :=
    match T with
      | bool => fail 1
      | type => fail 1
      | ctxt _ _ => fail 1
      | _ => default_chooser T k
    end.

  induction 1; matching my_simpler my_chooser; eauto.
Qed.

Theorem CpsTerm_correct : forall t (E : Term t),
  forall k, exists r,
    PtermDenote (CpsTerm E) k = k r
    /\ lr t (TermDenote E) r.
  unfold PtermDenote, TermDenote, CpsTerm; simpl; intros.
  eapply (cpsTerm_correct (G := nil)); simpl; intuition.
  apply Term_equiv.
Qed.

Theorem CpsTerm_correct_bool : forall (E : Term TBool),
  forall k, PtermDenote (CpsTerm E) k = k (TermDenote E).
  intros.
  generalize (CpsTerm_correct E k); firstorder congruence.
Qed.
                                          
