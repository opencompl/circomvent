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

open Polynomial

inductive Var (ι ε ω : Type) 
| input (i : ι)
| output (o : ω)
| existential (e : ε)
deriving DecidableEq, Inhabited, Repr

/-- A constraint is a multivariate polynomial over the variables in the Var with coefficients in ZMod p -/
abbrev Constraint (α : Type) (p : Nat) := 
  MvPolynomial α (ZMod p)

abbrev ConstraintSystem (α : Type) (p : Nat) := 
   List (Constraint α p)


inductive Expr (ι ε ω : Type) (p : Nat) 
| const (c : ZMod p)
| var (v : Var ι ε ω)
| add (e1 e2 : Expr ι ε ω p)
| mul (e1 e2 : Expr ι ε ω p)
| select (cond : Expr ι ε ω p)
   (thenBranch elseBranch : Expr ι ε ω p)

inductive Stmt (ι ε ω : Type) (p : Nat) 
| assign (v : Var Empty ε ω) (e : Expr ι ε ω p)
    (isConstraint : Bool)
| constraint (c : Constraint (Var ι ε ω) p)

structure Program (ι ε ω : Type) (p : Nat) where
   stmts : List (Stmt ι ε ω p)

def Program.toConstraintSystem
  {ι ε ω : Type} (p : Nat) (prog : Program ι ε ω p) : 
   ConstraintSystem (Var ι ε ω) p := 
    prog.stmts.foldl 
      (fun acc stmt => 
        match stmt with
        | Stmt.constraint c => c :: acc
        | Stmt.assign v e isConstraint => 
            if isConstraint then
              let poly := Expr.toPolynomial e - MvPolynomial.X v
              poly :: acc
            else
              acc)
      []

def Program.toWitness 
  {ι ε ω : Type} (p : Nat) (prog : Program ι ε ω p) : 
   σ → ZMod p := Id.run do
    fun input => 
      let mut env : Var ι ε ω → ZMod p := 
        fun v => 
          match v with
          | Var.input i => input i
          | _ => 0
      for stmt in prog.stmts do
        match stmt with
        | Stmt.assign v e isConstraint => 
            if !isConstraint then
              let val := Expr.eval e env
              env := fun x => if x = v then val else env x
        | _ => ()
      env

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

