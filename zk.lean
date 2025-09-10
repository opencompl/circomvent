-- https://github.com/Veridise/llzk-lib/blob/5680d910854e71b1b92b02e4f69271c4345caedf/test/FrontendLang/Circom/circomlib.llzk
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.ToFinsupp
import Mathlib.Data.List.Basic
import CompPoly.CMvPolynomial

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

open CPoly
open Polynomial

inductive Var (ι ε ω : Type)
| input (i : ι)
| output (o : ω)
| existential (e : ε)
deriving DecidableEq, Inhabited, Repr, BEq, Hashable


/-- Map the variables in a Var to another Var. -/
def Var.map (f : ι₁ → ι₂) (g : ε₁ → ε₂) (h : ω₁ → ω₂) :
    Var ι₁ ε₁ ω₁ → Var ι₂ ε₂ ω₂
| Var.input i => Var.input (f i)
| Var.existential e => Var.existential (g e)
| Var.output o => Var.output (h o)

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
   ∀ poly ∈ cs, poly.aeval env = 0

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

def sub {α : Type} {p : Nat}
    (e1 e2 : PolyExpr α p) : PolyExpr α p :=
  e1 + (-e2)

instance : Sub (PolyExpr α p) where
  sub e1 e2 := e1 + (-e2)

@[simp] theorem sub_def {α : Type} {p : Nat}
    (e1 e2 : PolyExpr α p) :
    (e1 - e2) = e1.sub e2 := by rfl

@[simp]
theorem eval_sub {α : Type} {p : Nat}
    (e1 e2 : PolyExpr α p) :
    (e1 - e2).eval = fun env => (e1.eval env) - (e2.eval env) := by
  ext a
  simp [sub, eval]
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
noncomputable def Program.toConstraintSystem (prog : Program ι ε ω p) :
   ConstraintSystem (Var ι ε ω) p :=
    prog.stmts.foldl (init := [])
      (fun acc stmt =>
        match stmt.toConstraint with
        | .some c => c :: acc
        | none => acc)

/-- Run the witness generation semantics of the program. -/
noncomputable def Program.toWitness_go
    [DecidableEq ι] [DecidableEq ε] [DecidableEq ω]
    (env : (Var ι ε ω) → (ZMod p))
    (prog : Program ι ε ω p) :
    (Var ι ε ω) → (ZMod p) :=
    prog.stmts.foldl (init := env)
      (fun env stmt =>
        match stmt with
        | Stmt.assign var rhs =>
          let o := rhs.eval env
          -- env' := env [var := o]
          let env' := (fun vnew => if vnew = (var.mapInput Empty.elim) then o else env vnew)
          env'
        | Stmt.constraint lhs? rhs =>
          match lhs? with
          | none => env
          | some lhs =>
            let o := rhs.eval env
            let env' := (fun vnew => if vnew = (lhs.mapInput Empty.elim) then o else env vnew)
            env')

noncomputable def Program.toWitness
    [DecidableEq ι] [DecidableEq ε] [DecidableEq ω]
    (envIn : ι → (ZMod p))
    (prog : Program ι ε ω p) :
    (ω → (ZMod p)) :=
  let env' := prog.toWitness_go fun var =>
    match var with
    | Var.input i => envIn i
    | _ => 0
  fun o => env' (Var.output o)

structure Program.WellFormed
  [DecidableEq ι] [DecidableEq ε] [DecidableEq ω]
  (program : Program ι ε ω p) : Prop where
  hcomplete : ∀ (envIn : ι → ZMod p), ∃ (envExists : ε → ZMod p),
      (Program.toConstraintSystem program).IsSat fun var =>
        match var with
        | Var.input i => envIn i
        | Var.existential e => envExists e
        | Var.output o => program.toWitness envIn o

  hsound :
    ∀ (envIn : ι → ZMod p) (envExists : ε → ZMod p) (envOut : ω → ZMod p),
      (hModel : (Program.toConstraintSystem program).IsSat (fun var =>
        match var with
        | Var.input i => envIn i
        | Var.existential e => envExists e
        | Var.output o => envOut o)) →
      (envOut = program.toWitness envIn)

namespace IsZeroCircuit

infix : 20 " e≠ " => BoolExpr.ne
notation "in(" i ")" => Var.input i
notation "out(" o ")" => Var.output o
notation "inv(" e ")" => Var.existential e
notation var "<<=" e => Stmt.constraint (some var) e
notation var "<<-" e => Stmt.assign var e
notation e1 "===" e2 => Stmt.constraint none (e1 - e2)

variable (p : Nat) (hp : Nat.Prime p)
def program : Program (Fin 1) (Fin 1) (Fin 1) p :=
  { stmts := [
    inv(0) <<- .field (.var in(0))⁻¹,
    (out(0)) <<= -(.var (in(0))) * (.var (inv(0))) + 1,
    (((.var (in(0))) * (.var (out(0))))) === 0
    ]}

theorem program_WellFormed : (program p).WellFormed := by
  constructor
  · sorry
  · sorry

end IsZeroCircuit

-- 1. define computable MvPolynomial from Nethermind.
-- 2. define 'Program.WellFormed' : witness (x) = y <->
--    (∃ σ, constraintsystem x σ y)
-- 3. Define 'isZero' program.
-- 4. Prove that 'isZero.WellFormed'.
end Circomvent
