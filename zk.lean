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
-- Grind
import CompPoly.CMvPolynomial


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
def ConstraintSystem.IsModel {α : Type} {p : Nat} 
   (cs : ConstraintSystem α p) 
   (env : α → ZMod p) : Prop :=
   ∀ poly ∈ cs, poly.aeval env = 0

inductive PolyExpr (α: Type) (p : Nat) : Type
| const (c : ZMod p)
| var (v : α)
| add (e1 e2 : PolyExpr α p)
| mul (e1 e2 : PolyExpr α p)
deriving DecidableEq, Inhabited, Repr

instance : Coe α (PolyExpr α p) where
  coe v := PolyExpr.var v

namespace PolyExpr
variable {α : Type} {p : Nat}

@[simp]
theorem coe_var (v : α) : (v : PolyExpr α p) = PolyExpr.var v := rfl

noncomputable def toPolynomial : PolyExpr α p → MvPolynomial α (ZMod p)
| const c => MvPolynomial.C c
| var v => MvPolynomial.X v
| add e1 e2 => toPolynomial e1 + toPolynomial e2
| mul e1 e2 => toPolynomial e1 * toPolynomial e2
end PolyExpr

noncomputable def PolyExpr.eval 
    (env : α → ZMod p) 
    (e : PolyExpr α p) : ZMod p :=
    (e.toPolynomial).aeval env

inductive BoolExpr (α : Type) (p : Nat) : Type
| eq (e1 e2 : PolyExpr α p)
deriving DecidableEq, Inhabited, Repr

noncomputable def BoolExpr.eval 
    (env : α → ZMod p) 
    (b : BoolExpr α p) : Bool :=
  match b with 
  | BoolExpr.eq e1 e2 => e1.eval env = e2.eval env

inductive ToplevelExpr (α: Type) (p : Nat) : Type
| poly : PolyExpr α p → ToplevelExpr α p
| select (cond : BoolExpr α p) (thenBranch elseBranch : PolyExpr α p)

noncomputable def ToplevelExpr.eval
    (env : α → ZMod p) 
    (t : ToplevelExpr α p) : ZMod p :=
  match t with
  | ToplevelExpr.poly e => e.eval env
  | ToplevelExpr.select cond thenBranch elseBranch =>
      if cond.eval env then thenBranch.eval env else elseBranch.eval env

inductive Stmt (ι ε ω : Type) (p : Nat) 
-- | this a bit annoying, as we cannot have 'isConstaint', as it will
-- need a proof that the ToplevelExpr is a real polynomial.
| assign (v : Var Empty ε ω) (e : ToplevelExpr (Var ι ε ω) p)
| constraint (c : PolyExpr (Var ι ε ω) p)

noncomputable def Stmt.toConstraint
    (s : Stmt ι ε ω p) : Option (Constraint (Var ι ε ω) p) :=
  match s with
  | Stmt.constraint c => some c.toPolynomial
  | Stmt.assign .. => none

structure Program (ι ε ω : Type) (p : Nat) where
   stmts : List (Stmt ι ε ω p)

/-- Create a constraint system from 'Program'. -/
noncomputable def Program.toConstraintSystem (prog : Program ι ε ω p) : 
   ConstraintSystem (Var ι ε ω) p := 
    prog.stmts.foldl (init := [])
      (fun acc stmt => 
        match stmt.toConstraint with
        | .some c => c :: acc
        | none => acc)

/-- Run the witness generation semantics of the program. -/
noncomputable def Program.toWitness
    [DecidableEq ι] [DecidableEq ε] [DecidableEq ω]
    (env : (Var ι ε ω) → (ZMod p)) 
    (prog : Program ι ε ω p) : 
    (Var ι ε ω) → (ZMod p) :=
    prog.stmts.foldl (init := env)
      (fun env stmt => 
        match stmt with
        | Stmt.assign var rhs =>
          let o := rhs.eval env
          (fun vnew => if vnew = (var.mapInput Empty.elim) then o else env vnew)
        | Stmt.constraint .. => env)

structure Program.WellFormed 
  [DecidableEq ι] [DecidableEq ε] [DecidableEq ω]
  (program : Program ι ε ω p) : Prop where
  hsound : ∀
    (envIn : ι → ZMod p) {envOut : (Var ι ε ω) → ZMod p}, 
    (hout : envOut = 
      program.toWitness fun var =>
        match var with
        | Var.input i => envIn i
        | _ => 0) →
    ∃ (envExists : ε → ZMod p),
      (Program.toConstraintSystem program).IsModel fun var =>
        match var with
        | Var.input i => envIn i
        | Var.existential e => envExists e
        | Var.output o => envOut (Var.output o)

  hcomplete :
    ∀ (envIn : ι → ZMod p) (envExists : ε → ZMod p) (envOut : ω → ZMod p), 
      (hModel : (Program.toConstraintSystem program).IsModel (fun var =>
        match var with
        | Var.input i => envIn i
        | Var.existential e => envExists e
        | Var.output o => envOut o)) →
      (henvOut : env' = program.toWitness fun var =>
        match var with
        | Var.input i => envIn i
        | Var.existential e => envExists e
        | Var.output o => envOut o) →
      (∀ o : ω, envOut o = env' (Var.output o))
      -- (∀ e : ε, envExists e = env' (Var.existential e))
-- 1. define computable MvPolynomial from Nethermind.
-- 2. define 'Program.WellFormed' : witness (x) = y <-> 
--    (∃ σ, constraintsystem x σ y)
-- 3. Define 'isZero' program.
-- 4. Prove that 'isZero.WellFormed'.

-- inv <--
-- out <== 

namespace ZK 

structure ConstraintSystem (σ : Type) (p : Nat) where
  polys : List <| MvPolynomial σ (ZMod p)

namespace ConstraintSystem
variable {σ : Type} {p : Nat} (c : ConstraintSystem σ p)


def Sat (cs : ConstraintSystem σ p) (assign : σ → ZMod p) : Prop :=
    ∀ poly ∈ cs.polys, poly.aeval assign = 0
end ConstraintSystem

end ZK

