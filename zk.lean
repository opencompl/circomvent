-- https://github.com/Veridise/llzk-lib/blob/5680d910854e71b1b92b02e4f69271c4345caedf/test/FrontendLang/Circom/circomlib.llzk
-- import Mathlib.RingTheory.Polynomial.Quotient
-- import Mathlib.RingTheory.Ideal.Defs
-- import Mathlib.RingTheory.Ideal.Basic
-- import Mathlib.Data.ZMod.Defs
-- import Mathlib.Data.ZMod.Basic
-- import Mathlib.Data.Nat.Prime.Defs
-- import Mathlib.Algebra.MonoidAlgebra.Basic
-- import Mathlib.Algebra.Polynomial.RingDivision
-- import Mathlib.Data.Finset.Sort
-- import Mathlib.Data.List.ToFinsupp
-- import Mathlib.Data.List.Basic
import Mathlib

/-# Example IsZero Program

```c
// Constraint := MvPolynomial (Var (Fin 1) (Fin 1) (Fin 1)) (ZMod p)
// ConstraintSystem := List (MvPolynomial (Var (Fin 1) (Fin 1) (Fin 1)) (ZMod p))
template IsZero() {
    signal input in; -- one input ~= Fin 1
    signal output out; -- one output ~= Fin 1

    signal inv; -- existential ~= Fin 1

    inv <-- in!=0 ? 1/in : 0; // for now, consider this full line the semantics of `felt.inv`

    out <== -in*inv +1;
    in*out === 0;
}
```
-/

/-# Exercises for the reader

- Switch to `CompPoly.CMvPolynomial`, which has already been imported.
  The proofs will need to change; They will use the `RingEquiv` between a
  `CompPoly.CMvPolynomial` and a `MvPolynomial`.
  Since `MPolynomial` contains all the reasoning principles,
  our proofs about `CompPoly.CMvPolynomial` will need to use the `RingEquiv` to
  convert to an `MvPolynomial`, do the reasoning there, and convert back.

-/

namespace Circomvent

open Polynomial

inductive Var (ι ε ω : Type)
| input (i : ι)
| output (o : ω)
| existential (e : ε)
deriving DecidableEq, Inhabited, Repr, BEq, Hashable

/-- Map the variables in a Var to another Var. -/
@[simp]
def Var.map (f : ι₁ → ι₂) (g : ε₁ → ε₂) (h : ω₁ → ω₂) :
    Var ι₁ ε₁ ω₁ → Var ι₂ ε₂ ω₂
| Var.input i => Var.input (f i)
| Var.existential e => Var.existential (g e)
| Var.output o => Var.output (h o)

@[simp]
def Var.mapInput (f : ι₁ → ι₂) : Var ι₁ ε ω → Var ι₂ ε ω :=
    Var.map f id id

/-- A constraint is a multivariate polynomial
over the variables in the Var with coefficients in ZMod p -/
abbrev Constraint (α : Type) (p : Nat) :=
  MvPolynomial α (ZMod p)

abbrev ConstraintSystem (α : Type) (p : Nat) :=
   List (Constraint α p)

/-- Check that `c ⊧ env` -/
def ConstraintSystem.IsSat {α : Type} {p : Nat}
   (cs : ConstraintSystem α p)
   /- env assigns values to each variable. -/
   (env : α → ZMod p) : Prop :=
   ∀ poly ∈ cs, poly.eval env = 0

/-- Minimal embedding of Circom syntax.
Can eventually be moved to the `lean-mlir` syntax embedding.
-/
inductive PolyExpr (α : Type) (p : Nat) : Type
| const (c : ZMod p) -- TODO: do we want to have this be `Z`, and choose `p` later?
| var (v : α)
| add (e1 e2 : PolyExpr α p)
| mul (e1 e2 : PolyExpr α p)
deriving DecidableEq, Inhabited, Repr


instance : OfNat (PolyExpr α p) n where
  ofNat := PolyExpr.const (n : ZMod p)

instance : Add (PolyExpr α p) where
  add e1 e2 := PolyExpr.add e1 e2

instance : Mul (PolyExpr α p) where
  mul e1 e2 := PolyExpr.mul e1 e2

/-- Coerce variables in `α` into a `PolyExpr`.

-- "x" = 0 : Fin 1
-- (add (PolyExpr.var 0) (PolyExpr.var 1) : PolyExpr (Fin 2) p)
-- (add 0 1) : PolyExpr (Fin 2) p
-/
instance : Coe α (PolyExpr α p) where
  coe v := PolyExpr.var v

namespace PolyExpr

variable {α : Type} {p : Nat}

/-- The coercion is well-formed, and injects values `v : α` as a `PolyExpr.var`. -/
@[simp] theorem coe_var (v : α) : (v : PolyExpr α p) = PolyExpr.var v := rfl

/-- Denotation from syntax to semantics. -/
noncomputable def toPolynomial : PolyExpr α p → MvPolynomial α (ZMod p)
| const c => MvPolynomial.C c
| var v => MvPolynomial.X v
| add e1 e2 => toPolynomial e1 + toPolynomial e2
| mul e1 e2 => toPolynomial e1 * toPolynomial e2

/-- Evaluate a `PolyExpr` in an environment `env : α → ZMod p`. -/
noncomputable def aeval (e : PolyExpr α p)
    (env : α → ZMod p) : ZMod p :=
    (e.toPolynomial).aeval env

/-- Evaluate a `PolyExpr` in an environment `env : α → ZMod p`. -/
@[simp]
def eval (e : PolyExpr α p) (env : α → ZMod p) : ZMod p :=
  match e with
  | PolyExpr.const c => c
  | PolyExpr.var v => env v
  | PolyExpr.add e1 e2 => e1.eval env + e2.eval env
  | PolyExpr.mul e1 e2 => e1.eval env * e2.eval env

def neg {α : Type} {p : Nat}
    (e : PolyExpr α p) : PolyExpr α p :=
  PolyExpr.mul (PolyExpr.const (-1)) e

instance : Neg (PolyExpr α p) where
  neg e := neg e

@[simp] theorem neg_def {α : Type} {p : Nat}
    (e : PolyExpr α p) :
    (neg e) = (- e) := rfl

@[simp]
theorem eval_neg {α : Type} {p : Nat}
    (e : PolyExpr α p) :
    (- e).eval = fun env => -(e.eval env) := by
  ext a
  rw [← neg_def]
  simp only [neg, eval]
  ring

@[simp]
theorem toPolynomial_neg {α : Type} {p : Nat}
    (e : PolyExpr α p) :
    (- e).toPolynomial = - (e.toPolynomial) := by
  ext
  rw [← neg_def]
  simp [neg, toPolynomial]

def sub {α : Type} {p : Nat}
    (e1 e2 : PolyExpr α p) : PolyExpr α p :=
  e1 + (-e2)

instance : Sub (PolyExpr α p) where
  sub e1 e2 := e1 + (-e2)

@[simp] theorem sub_def {α : Type} {p : Nat}
    (e1 e2 : PolyExpr α p) :
    e1.sub e2 = e1 - e2 := by rfl

@[simp]
theorem eval_sub {α : Type} {p : Nat}
    (e1 e2 : PolyExpr α p) :
    (e1 - e2).eval = fun env => (e1.eval env) - (e2.eval env) := by
  ext a
  simp [eval]
  ring

@[simp]
theorem toPolynomial_sub {α : Type} {p : Nat}
    (e1 e2 : PolyExpr α p) :
    (e1 - e2).toPolynomial = (e1.toPolynomial) - (e2.toPolynomial) := by
  ext
  simp [toPolynomial]
  ring

end PolyExpr

/-- ## Syntax of Boolean expressions.

# Exercise to the reader:
- extend to <=, <, not equals, and so on.
-/
inductive BoolExpr (α : Type) (p : Nat) : Type
| eq (e1 e2 : PolyExpr α p)
| bnot (b : BoolExpr α p)
deriving DecidableEq, Inhabited, Repr

noncomputable def BoolExpr.eval
    (env : α → ZMod p)
    (b : BoolExpr α p) : Bool :=
  match b with
  | BoolExpr.eq e1 e2 => e1.eval env = e2.eval env
  | BoolExpr.bnot b => not (b.eval env)

/-- Define not-equals in terms of equals and not. -/
def BoolExpr.ne {α : Type} {p : Nat}
    (e1 e2 : PolyExpr α p) : BoolExpr α p :=
  BoolExpr.bnot (BoolExpr.eq e1 e2)

@[simp]
theorem BoolExpr.eval_ne {α : Type} {p : Nat}
    (e1 e2 : PolyExpr α p) :
    (BoolExpr.ne e1 e2).eval = fun env => (e1.eval env ≠ e2.eval env) := by
  ext a
  simp [BoolExpr.ne, BoolExpr.eval]

/-- ## Syntax of top-level expressions.

These are either polynomials,
or a top-level ternary select `cond ? etrue : efalse`.
-/

inductive FieldExpr (α : Type) (p : Nat) : Type
| const (c : ZMod p) -- TODO: do we want to have this be `Z`, and choose `p` later?
| var (v : α)
| add (e1 e2 : FieldExpr α p)
| mul (e1 e2 : FieldExpr α p)
| mulinv (e : FieldExpr α p) -- multiplicative inverse
deriving DecidableEq, Inhabited, Repr

instance : OfNat (FieldExpr α p) n where
  ofNat := FieldExpr.const (n : ZMod p)

instance : Add (FieldExpr α p) where
  add e1 e2 := FieldExpr.add e1 e2

instance : Mul (FieldExpr α p) where
  mul e1 e2 := FieldExpr.mul e1 e2

instance : Inv (FieldExpr α p) where
  inv e := FieldExpr.mulinv e

@[simp]
def FieldExpr.eval
    (env : α → ZMod p)
    (e : FieldExpr α p) : ZMod p :=
  match e with
  | FieldExpr.const c => c
  | FieldExpr.var v => env v
  | FieldExpr.add e1 e2 => e1.eval env + e2.eval env
  | FieldExpr.mul e1 e2 => e1.eval env * e2.eval env
  | FieldExpr.mulinv e => (e.eval env)⁻¹

def FieldExpr.div {α : Type} {p : Nat}
    (e1 e2 : FieldExpr α p) : FieldExpr α p :=
  FieldExpr.mul e1 (FieldExpr.mulinv e2)

@[simp]
theorem FieldExpr.eval_div {α : Type} {p : Nat}
    (e1 e2 : FieldExpr α p) :
    (FieldExpr.div e1 e2).eval = fun env => (e1.eval env) * (e2.eval env)⁻¹ := by
  ext a
  simp [FieldExpr.div, FieldExpr.eval]

inductive WitnessExpr (α: Type) (p : Nat) : Type
| field : FieldExpr α p → WitnessExpr α p
| select (cond : BoolExpr α p) (thenBranch elseBranch : PolyExpr α p)

@[simp]
noncomputable def WitnessExpr.eval
    (env : α → ZMod p)
    (t : WitnessExpr α p) : ZMod p :=
  match t with
  | WitnessExpr.field e => e.eval env
  | WitnessExpr.select cond thenBranch elseBranch =>
      if cond.eval env then thenBranch.eval env else elseBranch.eval env

/-## Statement expressions.

## Exercise for the reader:

- Add a `lhs? : Option Var` to `Constraint`,
  which will treat the constraint also as an assignment to the variable `Var`.
-/
inductive Stmt (ι ε ω : Type) (p : Nat)
| assign (v : Var Empty ε ω) (e : WitnessExpr (Var ι ε ω) p)
| constraint (lhs? : Option (Var Empty ε ω)) (c : PolyExpr (Var ι ε ω) p)

noncomputable def Stmt.toConstraint
    (s : Stmt ι ε ω p) : Option (Constraint (Var ι ε ω) p) :=
  match s with
  | Stmt.constraint _lhs c => some c.toPolynomial
  | Stmt.assign .. => none

/-- ## Circom Programs. -/
structure Program (ι ε ω : Type) (p : Nat) where
   stmts : List (Stmt ι ε ω p)

/-- Create a constraint system from 'Program',
by converting each `Stmt.constraint` into a `Constraint`. -/
noncomputable def Program.toConstraintSystem_go (stmts : List (Stmt ι ε ω p)) :
   ConstraintSystem (Var ι ε ω) p :=
   -- TODO: why does `List.foldl` not work here? Think if we need a different fold.
    match stmts with
    | [] => []
    | stmt :: stmts' =>
        match stmt with
        | Stmt.constraint lhs? c =>
          let lhsPoly : PolyExpr (Var ι ε ω) p :=
            match lhs? with
            | none => 0
            | some lhs => (PolyExpr.var (lhs.mapInput Empty.elim))
          (c - lhsPoly).toPolynomial :: Program.toConstraintSystem_go stmts'
        | Stmt.assign .. => Program.toConstraintSystem_go stmts'

@[simp]
noncomputable def Program.toConstraintSystem (prog : Program ι ε ω p) :
    ConstraintSystem (Var ι ε ω) p :=
    (Program.toConstraintSystem_go prog.stmts)

@[simp]
theorem Program.toConstraintSystem_go_nil_eq :
    Program.toConstraintSystem_go ([] : List (Stmt ι ε ω p)) = [] := by
  rfl

@[simp]
theorem Program.toConstraintSystem_go_cons_eq
    (stmts : List (Stmt ι ε ω p))
    (v : Var Empty ε ω) (e : WitnessExpr (Var ι ε ω) p)
    :
    Program.toConstraintSystem_go ((Stmt.assign v e) :: stmts) =
    (Program.toConstraintSystem_go stmts) := by rfl

@[simp]
theorem Program.toConstraintSystem_constraint_none_cons_eq
    (stmts : List (Stmt ι ε ω p))  (e : PolyExpr (Var ι ε ω) p)
    :
    Program.toConstraintSystem_go ((Stmt.constraint none e) :: stmts) =
    (e.toPolynomial :: Program.toConstraintSystem_go stmts) := by
  simp [toConstraintSystem_go]
  simp [PolyExpr.toPolynomial]

@[simp]
theorem Program.toConstraintSystem_constraint_cons_eq
    (stmts : List (Stmt ι ε ω p))
    (v : (Var Empty ε ω)) (e : PolyExpr (Var ι ε ω) p)
    :
    Program.toConstraintSystem_go ((Stmt.constraint (some v) e) :: stmts) =
    ((e - (PolyExpr.var (v.mapInput Empty.elim))).toPolynomial :: Program.toConstraintSystem_go stmts) := by
  simp [toConstraintSystem_go]


def envUpdate
    [DecidableEq α]
    (env : α → β)
    (var : α)
    (o : β) :
    α → β := fun vnew => if vnew = var then o else env vnew

noncomputable def Stmt.execute_go
    [DecidableEq ι] [DecidableEq ε] [DecidableEq ω]
    {p : Nat}
    (env : (Var ι ε ω) → (ZMod p))
    (stmt : Stmt ι ε ω p) :
    (Var ι ε ω) → (ZMod p) :=
    match stmt with
    | Stmt.assign var rhs =>
      let o := rhs.eval env
      -- env' := env [var := o]
      let env' := envUpdate env (var.mapInput Empty.elim) o
      env'
    | Stmt.constraint lhs? rhs =>
      match lhs? with
      | none => env
      | some lhs =>
        let o := rhs.eval env
        let env' := envUpdate env (lhs.mapInput Empty.elim) o
        env'

@[simp]
theorem Stmt.execute_go_assign_eq
    [DecidableEq ι] [DecidableEq ε] [DecidableEq ω]
    {p : Nat}
    (env : (Var ι ε ω) → (ZMod p))
    (var : Var Empty ε ω)
    (rhs : WitnessExpr (Var ι ε ω) p) :
    Stmt.execute_go env (Stmt.assign var rhs) =
    envUpdate env (var.mapInput Empty.elim) (rhs.eval env) := by
  rfl

@[simp]
theorem Stmt.execute_go_constraint_none_eq
    [DecidableEq ι] [DecidableEq ε] [DecidableEq ω]
    {p : Nat}
    (env : (Var ι ε ω) → (ZMod p))
    (rhs : PolyExpr (Var ι ε ω) p) :
    Stmt.execute_go env (Stmt.constraint none rhs) = env := by
  rfl

@[simp]
theorem Stmt.execute_go_constraint_some_eq
    [DecidableEq ι] [DecidableEq ε] [DecidableEq ω]
    {p : Nat}
    (env : (Var ι ε ω) → (ZMod p))
    (var : Var Empty ε ω)
    (rhs : PolyExpr (Var ι ε ω) p) :
    Stmt.execute_go env (Stmt.constraint (some var) rhs) =
    envUpdate env (var.mapInput Empty.elim) (rhs.eval env) := by
  rfl

/-- Run the witness generation semantics of the program. -/
noncomputable def Program.execute_go
    [DecidableEq ι] [DecidableEq ε] [DecidableEq ω]
    (env : (Var ι ε ω) → (ZMod p))
    (stmts : List (Stmt ι ε ω p)) :
    (Var ι ε ω) → (ZMod p) :=
      stmts.foldl (init := env) (fun env stmt => Stmt.execute_go env stmt)

@[simp]
theorem Program.execute_go_nil_eq
    [DecidableEq ι] [DecidableEq ε] [DecidableEq ω]
    (env : (Var ι ε ω) → (ZMod p)) :
    Program.execute_go env ([] : List (Stmt ι ε ω p)) = env := by
  rfl

@[simp]
theorem Program.execute_go_cons_eq
    [DecidableEq ι] [DecidableEq ε] [DecidableEq ω]
    (env : (Var ι ε ω) → (ZMod p))
    (s : Stmt ι ε ω p) (ss : List (Stmt ι ε ω p)) :
    Program.execute_go env (s :: ss) = Program.execute_go (Stmt.execute_go env s) ss := by
  rfl


@[simp]
noncomputable def Program.execute
    [DecidableEq ι] [DecidableEq ε] [DecidableEq ω]
    (envIn : ι → (ZMod p))
    (prog : Program ι ε ω p) :
    (ω → (ZMod p)) :=
  let env' := Program.execute_go (fun var =>
    match var with
    | Var.input i => envIn i
    | _ => 0) prog.stmts
  fun o => env' (Var.output o)

def Env (envIn : ι → ZMod p) (envExists : ε → ZMod p) (envOut : ω → ZMod p)
  := fun var => match var with
      | Var.input i => envIn i
      | Var.existential e => envExists e
      | Var.output o => envOut o

structure Program.WellFormed
  [DecidableEq ι] [DecidableEq ε] [DecidableEq ω]
  (program : Program ι ε ω p) : Prop where
  hcomplete : ∀ (envIn : ι → ZMod p), ∃ (envExists : ε → ZMod p),
      (Program.toConstraintSystem program).IsSat (Env envIn envExists (program.execute envIn))
  hsound :
    ∀ (envIn : ι → ZMod p) (envExists : ε → ZMod p) (envOut : ω → ZMod p),
      (Program.toConstraintSystem program).IsSat (Env envIn envExists envOut) →
      (envOut = program.execute envIn)

-- A program is "determinstic" if for exists at most one witness for any given (input, output) pair
-- This property is sometimes useful to show, in particular when it is difficult to show soundness wrt
-- a particular determinstic witness calculator.
structure Program.Determinstic
  [DecidableEq ι] [DecidableEq ε] [DecidableEq ω]
  (program : Program ι ε ω p) : Prop where
  hdeterministic : ∀ (envIn : ι → ZMod p) (envExists : ε → ZMod p) (envExists' : ε → ZMod p) (envOut : ω → ZMod p),
    (Program.toConstraintSystem program).IsSat (Env envIn envExists envOut)
    ∧ (Program.toConstraintSystem program).IsSat (Env envIn envExists' envOut)
    → envExists = envExists'

namespace IsZeroCircuit

notation "in(" i ")" => Var.input i
notation "out(" o ")" => Var.output o
notation "inv(" e ")" => Var.existential e
notation var "<<=" e => Stmt.constraint (some var) e
notation var "<<-" e => Stmt.assign var e
notation e1 "===" e2 => Stmt.constraint none (e1 - e2)

variable (p : Nat) [Fact p.Prime]

def program : Program (Fin 1) (Fin 1) (Fin 1) p :=
  { stmts := [
    inv(0) <<- .field (.var in(0))⁻¹,
    (out(0)) <<= -(.var (in(0))) * (.var (inv(0))) + 1,
    (((.var (in(0))) * (.var (out(0))))) === 0,
    ]}

theorem program_WellFormed : (program p).WellFormed := by
  constructor
  · intros envIn
    let envExists : Fin 1 → ZMod p := fun _ => (envIn 0)⁻¹
    exists envExists
    simp only [Program.toConstraintSystem, program, Fin.isValue,
      Program.toConstraintSystem_go_cons_eq, Program.toConstraintSystem_constraint_cons_eq,
      Var.mapInput, Var.map, id_eq, PolyExpr.toPolynomial_sub,
      Program.toConstraintSystem_constraint_none_cons_eq, Program.toConstraintSystem_go_nil_eq,
      Program.execute, Program.execute_go_cons_eq, Stmt.execute_go_assign_eq,
      Stmt.execute_go_constraint_some_eq, Stmt.execute_go_constraint_none_eq,
      Program.execute_go_nil_eq]
    simp only [ConstraintSystem.IsSat, Fin.isValue, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, map_sub, forall_eq]
    constructor <;> simp [PolyExpr.toPolynomial, Env, envUpdate] <;> grind
  · intros envIn envExists envOut
    simp [Program.toConstraintSystem, program, ConstraintSystem.IsSat,
      PolyExpr.toPolynomial, Env, envUpdate,
      Program.toConstraintSystem_go_cons_eq, Program.toConstraintSystem_constraint_cons_eq,
      Var.mapInput, Var.map, id_eq,
      Program.toConstraintSystem_constraint_none_cons_eq, Program.toConstraintSystem_go_nil_eq,
      Program.execute, Program.execute_go_cons_eq, Stmt.execute_go_assign_eq,
      Stmt.execute_go_constraint_some_eq, Stmt.execute_go_constraint_none_eq,
      Program.execute_go_nil_eq]
    grind

/--
info: 'Circomvent.IsZeroCircuit.program_WellFormed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms program_WellFormed

-- The IsZero program above is not Determinstic, since when in = 0, inv can be anything.
-- This is a variation that is determinstic.
def program_det : Program (Fin 1) (Fin 1) (Fin 1) p :=
  { stmts := [
    inv(0) <<- .field (.var in(0))⁻¹,
    (out(0)) <<= -(.var (in(0))) * (.var (inv(0))) + 1,
    (((.var (in(0))) * (.var (out(0))))) === 0,
    (((.var (out(0))) * (.var (inv(0))))) === 0,
    ]}

theorem program_det_Deterministic : (program_det p).Determinstic := by
  constructor
  · intros envIn envExists envExists' envOut
    simp [program_det, ConstraintSystem.IsSat, PolyExpr.toPolynomial, Env]
    intros h1 _ h3 h1' _ h3'
    have heq := h1
    rw [←h1'] at heq
    simp at heq
    by_cases hx : envIn 0 = 0
    · have hOutNe0 : ¬(envOut 0 = 0) := by grind
      simp [hOutNe0] at h3 h3' ⊢
      rw [←h3'] at h3
      ext i
      have i0 : i = 0 := by omega
      simp [i0, h3]
    · simp [hx] at heq
      ext i
      have i0 : i = 0 := by omega
      simp [i0, heq]

-- A direct, and application-specific definition of soundness.
-- TODO, this does not include the case that envIn != 0
theorem program_IsZero_Semantics :
    ∀ (envIn : (Fin 1) → ZMod p) (envExists : (Fin 1) → ZMod p) (envOut : (Fin 1) → ZMod p),
    (program p).toConstraintSystem.IsSat (Env envIn envExists envOut) →
    (envIn 0 = 0 ↔ envOut 0 = 1)
    := by
  intros envIn envExists envOut
  simp [program, ConstraintSystem.IsSat, PolyExpr.toPolynomial, Env]
  grind


end IsZeroCircuit

-- 1. define computable MvPolynomial from Nethermind.
-- 2. define 'Program.WellFormed' : witness (x) = y <->
--    (∃ σ, constraintsystem x σ y)
-- 3. Define 'isZero' program.
-- 4. Prove that 'isZero.WellFormed'.
end Circomvent
