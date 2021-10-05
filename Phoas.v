Require Import Bool.
Require Import Coqprime.elliptic.ZEll.
Require Import Coqprime.elliptic.ZEll.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.ZArith.BinInt.

From STLCZK Require Import GaloisField.
From STLCZK Require Import Ltac.
From Coq Require Import Vectors.VectorDef.
From Coq Require Import Init.Nat.
From Coq  Require Import Program.Equality.

Set Implicit Arguments.
Set Maximal Implicit Insertion.

Module Stlc(Import PF: GaloisField.GaloisField).
  Import PF.

  (** Use the same reified type for the whole development *)
  Inductive type : Type :=
  | TBool: type
  | TNum: type
  | TArrow : type -> type -> type.

  Declare Custom Entry stlc_ty.
  Notation "<{{ e }}>" := e (e custom stlc_ty at level 99).
  Notation "( x )" := x (in custom stlc_ty, x at level 99).
  Notation "x" := x (in custom stlc_ty at level 0, x constr at level 0).  
  Notation "S -> T" := (TArrow S T) (in custom stlc_ty at level 2, right associativity).
  Notation "'Num'" := TNum (in custom stlc_ty at level 0).
  Notation "'Bool'" := TBool (in custom stlc_ty at level 0).

  Section vars.
    Variable var : type -> Type.

    Inductive Term: type -> Type :=
    (* Constants *)
    | NUM: Fp -> Term <{{ Num }}>
    | BOOL: bool -> Term <{{ Bool }}>
    (* Finite field arithmetic *)
    | ADD: Term <{{ Num }}> -> Term <{{ Num }}> -> Term <{{ Num }}>
    | SUB: Term <{{ Num }}> -> Term <{{ Num }}> -> Term <{{ Num }}>
    | MUL: Term <{{ Num }}> -> Term <{{ Num }}> -> Term <{{ Num }}>
    | DIV: Term <{{ Num }}> -> Term <{{ Num }}> -> Term <{{ Num }}>
    (* Logical formulas *)
    | EQ: Term <{{ Num }}> -> Term <{{ Num }}> -> Term <{{ Bool }}>
    | AND: Term <{{ Bool }}> -> Term <{{ Bool }}> -> Term <{{ Bool }}>
    | OR: Term <{{ Bool }}> -> Term <{{ Bool }}> -> Term <{{ Bool }}>
    | NOT: Term <{{ Bool }}> -> Term <{{ Bool }}>
    (* Control flow *)
    | ITE: forall t, Term <{{ Bool }}> -> Term t -> Term t -> Term t
    (* Lambda *)
    | APP: forall a b, Term <{{ a -> b }}> -> Term a -> Term b
    | VAR: forall a, var a -> Term a
    | LAM: forall a b, (var a -> Term b) -> Term <{{ a ->  b }}>.

    Fixpoint typeDenote (t : type) : Set :=
      match t with
      | <{{ Bool }}> => bool
      | <{{ Num }}> => Fp
      | <{{ t1 -> t2 }}> => typeDenote t1 -> typeDenote t2
      end.

    (* Normalization via reify/reflect Danvy et al. *)
    Class Nbe (t: type) := {
      reify: typeDenote t -> Term t;
      reflect: Term t -> typeDenote t
                          }.

    Instance Nbe_lam {a b: type} `{Nbe a} `{Nbe b}: Nbe <{{ a -> b }}> := {
      reify v := 
        LAM (fun x => reify (v (reflect (VAR x))));
      reflect e :=
        fun x => reflect (APP e (reify x))
                                                                        }.
  End vars.

  Arguments VAR [var a].
  Arguments NUM {var}.
  Arguments BOOL {var}.
  Arguments ADD {var}.
  Arguments SUB {var}.
  Arguments MUL {var}.
  Arguments DIV {var}.
  Arguments EQ {var}.
  Arguments AND {var}.
  Arguments OR {var}.
  Arguments APP [var a b].
  Arguments LAM [var a b].
  (** Maximally insert types in class *)
  Arguments Nbe {var}.
  Arguments Nbe_lam {var} {a} {b}.
  Arguments reify {var} {t}.
  Arguments reflect {var} {t}.

  Declare Custom Entry stlc.
  Notation "'fp' n" := (NUM n) (in custom stlc at level 0).
  Notation "'true'"  := true (at level 1).
  Notation "'true'" := (BOOL true) (in custom stlc at level 0).
  Notation "'false'"  := false (at level 1).
  Notation "'false'" := (BOOL false) (in custom stlc at level 0).
  Notation "<{ e }>" := e (e custom stlc at level 99).
  Notation "( x )" := x (in custom stlc, x at level 99).
  Notation "x" := x (in custom stlc at level 0, x constr at level 0).
  Notation "x y" := (APP x y) (in custom stlc at level 1, left associativity).
  Notation "\ x , y" :=
    (LAM (fun x => y)) (in custom stlc at level 90,
                        x constr,
                        y custom stlc at level 80,
                        left associativity).
  Notation "\_ , y" :=
    (LAM (fun _ => y)) (in custom stlc at level 90,
                        y custom stlc at level 80,
                        left associativity).
  Notation "# n" := (VAR n) (in custom stlc at level 0).
  Notation "{ x }" := x (in custom stlc at level 1, x constr).  
  Notation "x + y" := (ADD x y) (in custom stlc at level 2,
                                            left associativity).
  Notation "x - y" := (SUB x y) (in custom stlc at level 2,
                                            left associativity).
  Notation "x * y" := (MUL x y) (in custom stlc at level 1,
                                            left associativity).
  Notation "x && y" := (AND x y) (in custom stlc at level 4,
                                             left associativity).
  Notation "x || y" := (OR x y) (in custom stlc at level 4,
                                             left associativity).
  Notation "x == y" := (EQ x y) (in custom stlc at level 3,
                                      left associativity).
  Notation "! x " := (NOT x) (in custom stlc at level 3).
  Notation "'if' x 'then' y 'else' z" :=
    (ITE x y z) (in custom stlc at level 89,
                    x custom stlc at level 99,
                    y custom stlc at level 99,
                    z custom stlc at level 99,
                    left associativity).
  
  Fixpoint termDenote t (e : Term typeDenote t) {struct e} : typeDenote t :=
    match e in (Term _ t) return (typeDenote t) with
    | VAR v => v
    | NUM f => f
    | BOOL v => v
    | ADD f1 f2 => pkplus (termDenote f1) (termDenote f2)
    | SUB f1 f2 => pksub (termDenote f1) (termDenote f2)
    | MUL f1 f2 => pkmul (termDenote f1) (termDenote f2)
    | DIV f1 f2 => pkdiv (termDenote f1) (termDenote f2)
    | EQ f1 f2 => if eq_field (termDenote f1) (termDenote f2) then true else false
    | ITE c t e => if (termDenote c) then termDenote t else termDenote e
    | AND b1 b2 => andb (termDenote b1) (termDenote b2)
    | OR b1 b2 => orb (termDenote b1) (termDenote b2)
    | NOT b => negb (termDenote b)
    | APP e1 e2 => (termDenote e1) (termDenote e2)
    | LAM e' => fun x => termDenote (e' x)
    end.

  Instance Nbe_int : Nbe <{{ Num }}> := {
    reify v := NUM v;
    reflect v := termDenote v;
                                }.

  Instance Nbe_bool : Nbe <{{ Bool }}> := {
    reify v := BOOL v;
    reflect v := termDenote v;
                                  }.

  Compute reify _ true.
  Compute reify (Nbe_lam _ _) (fun x => x).
  Compute reify (Nbe_lam _ _) (fun x => (fun y => y) true).
  Compute reflect (Nbe_lam _ _) <{ \_, true }>.
  Compute reify (Nbe_lam _ _ ) (fun x => (fun y => y) true).
  Compute reflect (Nbe_lam _ _)
          (reify (Nbe_lam _ _ ) (fun x => (fun y => y) true)).  
  Compute reflect (Nbe_lam _ _ )
          <{ (\x, \y, # x) true }>.

  Fixpoint resolver(t: type): Nbe t :=
    match t with
    | <{{ Bool }}> => Nbe_bool
    | <{{ Num }}> => Nbe_int
    | <{{ a -> b }}> => Nbe_lam (resolver a) (resolver b)
    end.
    
  Definition normalize {t: type} (e: Term typeDenote t) : Term typeDenote t :=
    reify (resolver t) (reflect (resolver t) e).
                                       
  Inductive fof: type -> Prop :=
  | fo_bool: fof <{{ Bool }}>
  | fo_num: fof <{{ Num }}>
  | fof_bool: forall a,
      fof <{{ a }}> ->
      fof <{{ Bool -> a }}>
  | fof_num: forall a,
      fof <{{ a }}> ->
      fof <{{ Num -> a }}>.

  Inductive hnff: forall (t: type), Term typeDenote t -> Prop :=
  | HNF_bool_ar: forall a f (arg: typeDenote <{{ Bool }}>),
      @hnff <{{ a }}> (f arg) ->
      @hnff <{{ Bool -> a }}> (LAM f)
  | HNF_num_ar: forall a f (arg: typeDenote <{{ Num }}>),
      @hnff <{{ a }}> (f arg) ->
      @hnff <{{ Num -> a }}> (LAM f)
  | HNF_bool: forall e,
      @hnff <{{ Bool }}> (BOOL e)
  | HNF_num: forall e,
      @hnff <{{ Num }}> (NUM e).

  (** Provide default witnesses for hnff *)
  Hint Extern 3 (typeDenote <{{ Bool }}>) => exact (true).
  Hint Extern 3 (typeDenote <{{ Num }}>) => exact (0:%p).

  Theorem normalize_correct: forall (t: type) (e: Term typeDenote t),
      fof t  -> 
      @hnff t (@normalize t e).
  Proof with eauto.
    intros.
    generalize dependent e.
    generalize dependent H.
    induction t; intros; dependent destruction e; cbn; try constructor;
      invert H; cbn; unshelve (econstructor; eauto)...
  Defined.

End Stlc.

  (** * Correctness *)

  (**
pterm_ind
     : forall P : pterm -> Prop,
       (forall v : var result, P (PHalt v)) ->
       (forall (t : ptype) (v : var (t --->)) (v0 : var t), P (PApp v v0)) ->
       (forall (t : ptype) (p : pprimop t) (p0 : var t -> pterm),
        (forall v : var t, P (p0 v)) -> P (PBind p p0)) -> forall p : pterm, P p
   *)


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
                                          
