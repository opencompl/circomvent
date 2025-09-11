import Mathlib.Lean.Expr.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic

/-- An expression representing a polynomial. -/
inductive Expr (p ι : Nat)
  /-- A free variable -/
  | var (x : Fin ι)
  /- A constant value -/
  | const (val : ZMod p)
  /-- Multiplication -/
  | mul (e₁ e₂ : Expr p ι)
  /-- Addition -/
  | add (e₁ e₂ : Expr p ι)
  /-- Subtraction -/
  | sub (e₁ e₂ : Expr p ι)

instance : Add (Expr p ι) where
  add := Expr.add
instance : Mul (Expr p ι) where
  mul := Expr.mul
instance : Sub (Expr p ι) where
  sub := Expr.sub
instance : OfNat (Expr p ι) n where
  ofNat := Expr.const n

abbrev Constraints (p ι : Nat) :=
  List (Expr p ι)

/-!
## Environment
-/

/-- An environment is a map from variables to values -/
def Environment (p ι : Nat) := Fin ι → ZMod p

/--
Restrict an environment to a subset of the variables, effectively forgetting
the values for any variables that fall outside of the restricted domain.
-/
def Environment.restrict {p ι₁ ι₂} (h : ι₂ ≤ ι₁ := by grind) :
    Environment p ι₁ → Environment p ι₂ :=
  fun env i => env <| i.castLE h



/--
Append an enviroment `env₁` in `n` variables to an environment `env₂` in `m`
variables, written `env₁ ++ env₂`, resulting in an environment in `n + m`
variables.

This treats all variables in either environment as distinct, hence, it shifts
the variables in `env₂` by `n` indices.
-/
def Environment.append : Environment p n → Environment p m → Environment p (n + m) :=
  fun env₁ env₂ i => i.addCases env₁ env₂

instance : HAppend (Environment p n) (Environment p m) (Environment p <| n + m) where
  hAppend := Environment.append


/-!
## Denotation
-/

def Expr.eval (env : Environment p ι) : Expr p ι → ZMod p
  | var x => env x
  | const val => val
  | mul e₁ e₂ => e₁.eval env * e₂.eval env
  | add e₁ e₂ => e₁.eval env + e₂.eval env
  | sub e₁ e₂ => e₁.eval env - e₂.eval env

def Constraints.eval (env : Environment p ι) (c : Constraints p ι) : Bool :=
  c.all (·.eval env == 0)

/-!
## Refinment of Constraints
-/

/--
We say that some constraint systems `c₁` in `ι` variables is refined by a system
`c₂` with `κ` variables, written as `c₁ ⊑ c₂`, when:

* `ι ≤ k`, that is, `c₂` has more variables than `c₁`, and
* For any (large) environment `env` that satisfies `c₂`, we can forget the extra
    variables and obtain a smaller environment which satisfies `c₁`
* For any (small) environment `env` that satisfies `c₁`, we can extend with new
    values to obtain a larger environment which satisfied `c₂`
-/
inductive Constraint.IsRefinedBy : Constraints p ι → Constraints p κ → Prop
  | intro {c₁ : Constraints p ι} {c₂ : Constraints p κ}
      (h_le : ι ≤ κ)
      (h₁ : ∀ (env : Environment p κ), c₂.eval env → c₁.eval env.restrict)
      (h₂ : ∀ (env : Environment p ι), c₁.eval env →
          ∃ (env' : Environment p κ), env = env'.restrict ∧ c₂.eval env')
          -- ------------------------ ^^^^^^^^^^^^^^^^^^^
          -- This expresses that `env'` is an extension of `env`
          --

          -- TODO: this should also say that `env'` is the *unique* extension
          --       that satisfies `c₂`
      : IsRefinedBy c₁ c₂

infixl:67 " ⊑ " => Constraint.IsRefinedBy

/-!
## Simp Automation
-/
section Simproc

theorem exists_env_iff {P : Environment _ _ → Prop} :
    (∃ (env : Environment p (ι + 1)), P env)
    ↔ (∃ (x : ZMod p) (env : Environment p ι), P (env.append [x].get)) := by
  sorry

end Simproc

/-!
## Example
-/
namespace Examples
def p := 101

def HigherOrder : Constraints p 1 := [
  let x := Expr.var 0
  x * x * x * x * x + 1 -- x^5 + 1 === 0
]

def LowerOrder : Constraints p 3 :=
  let x := Expr.var 0
  let y := Expr.var 1
  let z := Expr.var 2
[
  x * x - y, -- x^2 === y
  y * y - z, -- y^2 === z
  x * z + 1  -- x * z + 1 === 0
]

example : HigherOrder ⊑ LowerOrder := by
  unfold HigherOrder LowerOrder
  apply Constraint.IsRefinedBy.intro (by decide)
  · intro env
    simp [Constraints.eval, Expr.eval, Environment.restrict]
    grind

  · intro env
    simp [Constraints.eval, Expr.eval]
    intro h

    -- The below simplifies the existential quantifier to talk about values `y`
    -- and `z` rather than abstract environments. For now, we manually copied
    -- the rest of the statement, but this should be automatically generatable.
    suffices ∃ (y z : ZMod p),
      env 0 * env 0 - y = 0 ∧ y * y - z = 0 ∧ env 0 * z + 1 = 0
    by
      rcases this with ⟨y, z, this⟩
      use env.append [y, z].get
      apply And.intro
      · funext i
        -- ^^ The environemnts are equal iff they agree on the values for an
        --    arbitrary variable identified by index `i`.
        fin_cases i
        -- ^^ Since `i` is of type `Fin 1`, it can have only finitely many values
        --    (in particular, only index `0`), `fin_cases` does a case analasis on
        --    all value for `i`.
        rfl
      · -- The following rewrites should just follow from simp-lemmas, but
        -- the API seems to be missing at the moment.
        have : env.append [y, z].get 0 = env 0 := rfl
        have : env.append [y, z].get 1 = y := rfl
        have : env.append [y, z].get 2 = z := rfl
        simp [*]

    -- It's a bit surprising we need to rewrite along this have manually
    have (x y : ZMod p) : x - y = 0 ↔ x = y := by grind
    simp only [this]
    grind

end Examples

/-!
## Degree Lowering Pass
-/

/-!
### Compute Max Degree
-/

/-- The maximum degree of a polynomial expression. -/
def Expr.maxDegree : Expr p ι → Nat
  | .const _ => 0
  | .var _ => 1
  | .sub e₁ e₂ | .add e₁ e₂ => max e₁.maxDegree e₂.maxDegree
  | .mul e₁ e₂ => e₁.maxDegree + e₂.maxDegree

/-- The maximum degree of a collection of polynomial expressions. -/
def Constraints.maxDegree (c : Constraints p ι) : Nat :=
  c.map Expr.maxDegree |>.max? |>.getD 0

/-!
### Extra Expr API
-/
namespace Expr

/--
Loosen the bounds on the number of free variables in the expression.
-/
def castLE (h : ι ≤ κ := by grind) : Expr p ι → Expr p κ
  | .var i      => .var <| i.castLE h
  | .const x    => .const x
  | .add e₁ e₂  => .add e₁.castLE e₂.castLE
  | .sub e₁ e₂  => .sub e₁.castLE e₂.castLE
  | .mul e₁ e₂  => .mul e₁.castLE e₂.castLE

@[simp] theorem castLE_rfl (e : Expr p ι) (h : ι ≤ ι) :
    e.castLE h = e := by
  sorry

@[simp] theorem sizeOf_castLE (e : Expr p ι) (h : ι ≤ κ) :
    sizeOf (e.castLE h) = sizeOf e := by
  induction e <;> simp [castLE, *]

@[simp] theorem maxDegree_castLE (e : Expr p ι) (h : ι ≤ κ) :
    maxDegree (e.castLE h) = e.maxDegree := by
  induction e <;> simp [castLE, maxDegree, *]

end Expr

/-!
### Extra Constraints API
-/
namespace Constraints

/-- Add a new constraints to a set of constraints -/
def add : Constraints p ι → Expr p ι → Constraints p ι :=
  fun c e => c ++ [e]

/-- Loosen the bounds on the free variables of all constraints in a set -/
def castLE (h : ι ≤ κ := by grind) : Constraints p ι → Constraints p κ :=
  List.map (Expr.castLE h)

@[simp] theorem maxDegree_castLE (c : Constraints p ι) (h : ι ≤ κ) :
    maxDegree (c.castLE h) = maxDegree c := by
  simp [maxDegree, castLE, Function.comp_def]

@[simp] theorem maxDegree_add (cs : Constraints p ι) (c : Expr p ι) :
    (cs.add c).maxDegree = Nat.max cs.maxDegree c.maxDegree := by
  sorry

end Constraints

/-!
### Assignments
-/

/--
`Assignments` is a store for the fresh variables introduced in the degree lowering.
Each element of the list represents a fresh variable, where the element of the list
is the defining expression for the fresh variable.
-/
def Assignments (p ι : Nat) :=
  List (Expr p ι)

namespace Assignments

def castLE (h : ι ≤ κ := by grind) : Assignments p ι → Assignments p κ :=
  List.map (Expr.castLE h)

/--
Convert a set of fresh variable assignments into a set of constraints.

NOTE: this assumes that `ι` is large enough to contain all new fresh variables.

ACTUALLY: **the current code is broken**, as we've lost the starting point of the
fresh variables. Oops. That is, when we run `lowerDegreeToTwo`, we start the
computation with `ι` free variables, and the process will add some `κ` fresh
variables and return an Assignment set in `ι+κ` variables. We assume that
`κ` is equal to the length of the assignments, but that is not quite what we do
here. Currently, we just assume that the first assignment in `v` is variable `0`,
but actually, it should be variable `ι`!
-/
def toConstraints (v : Assignments p ι) : Constraints p ι :=
  if h : ι = 0 then
    [] -- This should never happen!
  else
    letI : NeZero ι := by constructor; exact h
    v.mapIdx fun i expr =>
      expr.sub (.var <| Fin.ofNat _ i)

def maxDegree (v : Assignments p ι) : Nat :=
  v.toConstraints.maxDegree
  -- v.map Expr.maxDegree |>.max? |>.getD 0

@[simp] theorem maxDegree_castLE (v : Assignments p ι) (h : ι ≤ κ) :
    (v.castLE h).maxDegree = v.maxDegree := by
  sorry

end Assignments

/-!
### LowerDegreeToTwo
-/

def Expr.lowerDegreeToTwo (vars : Assignments p ι) :
    Expr p ι →
      (κ : Nat) × Assignments p (ι + κ) × Expr p (ι + κ)
  | e@(.var _) | e@(.const _) => ⟨0, vars, e⟩
  | .add e₁ e₂ =>
      let ⟨κ₁, v₁, e₁⟩ := e₁.lowerDegreeToTwo vars
      let ⟨κ₂, v₂, e₂⟩ := e₂.castLE.lowerDegreeToTwo v₁

      ⟨κ₁ + κ₂, v₂.castLE, .add e₁.castLE e₂.castLE⟩
  | .sub e₁ e₂ =>
      let ⟨κ₁, v₁, e₁⟩ := e₁.lowerDegreeToTwo vars
      let ⟨κ₂, v₂, e₂⟩ := e₂.castLE.lowerDegreeToTwo v₁

      ⟨κ₁ + κ₂, v₂.castLE, .sub e₁.castLE e₂.castLE⟩
  | .mul e₁ e₂ =>
      let ⟨κ₁, v₁, e₁⟩ := e₁.lowerDegreeToTwo vars

      let ⟨ω₁, w₁, e₁⟩ :
          Σ (κ : Nat) (newVars : Assignments p (ι + κ)), Expr p (ι + κ) :=
        if e₁.maxDegree ≥ 2 then
          let w₁ : Assignments .. := v₁.append [e₁]
          -- introduce fresh variable y = e₁
          ⟨κ₁ + 1, w₁.castLE, Expr.var (Fin.last _)⟩
          -- TODO: this could check whether e₂ already has a variable in Assigments
        else
          ⟨_, v₁, e₁⟩

      let ⟨κ₂, v₂, e₂⟩ := e₂.castLE.lowerDegreeToTwo w₁

      let ⟨ω₂, w₂, e₂⟩ :
          Σ (κ : Nat) (newVars : Assignments p (ι + ω₁ + κ)), Expr p (ι + ω₁ + κ) :=
        if e₁.maxDegree + e₂.maxDegree > 2 then
          let w₂ : Assignments .. := v₂.append [e₂]
          -- introduce fresh variable z = e₂
          ⟨κ₂ + 1, w₂.castLE, Expr.var (Fin.last _)⟩
          -- TODO: this could check whether e₂ already has a variable in Assigments
        else
          ⟨κ₂, v₂.castLE, e₂.castLE⟩

      ⟨ω₁ + ω₂, w₂.castLE, .mul e₁.castLE e₂.castLE⟩
  termination_by e => sizeOf e

def Constraints.lowerDegreeToTwo (c : Constraints p ι) :
      Σ (κ : Nat), Constraints p (ι + κ) :=
  let ⟨κ, vars, c⟩ := go ⟨0, [], []⟩ c
  let c := c ++ vars.toConstraints
  ⟨κ, c⟩
where
  go : (κ : Nat) × Assignments p (ι + κ) × (Constraints p (ι + κ))
      → Constraints p ι
      → (κ : Nat) × Assignments p (ι + κ) × (Constraints p (ι + κ)) :=
    List.foldl fun ⟨κ, vars, c⟩ expr =>
      let ⟨κ', vars', expr'⟩ := expr.castLE.lowerDegreeToTwo vars
      let c : Constraints p (ι + (κ + κ')) := c.castLE
      ⟨κ + κ', vars'.castLE, c.add expr'.castLE⟩


@[simp]
theorem Constraints.lowerDegreeToTwo.go_nil
    (κ : Nat) (as : Assignments p (ι + κ)) (csNew : Constraints p (ι + κ)):
    Constraints.lowerDegreeToTwo.go ⟨κ, as, csNew⟩ [] = ⟨κ, as, csNew⟩ := rfl

@[simp]
theorem Constraints.lowerDegreeToTwo.go_cons
    (κ : Nat) (as : Assignments p (ι + κ)) (csNew : Constraints p (ι + κ))
    (c : Expr p ι) (cs : Constraints p ι) :
    Constraints.lowerDegreeToTwo.go ⟨κ, as, csNew⟩ (c :: cs) =
      let ⟨κ', as', expr'⟩ := (c.castLE.lowerDegreeToTwo as)
      let res :=  Constraints.lowerDegreeToTwo.go ⟨κ + κ', as'.castLE, csNew.castLE.add expr'.castLE⟩ cs
      res
      := by rfl


-- lemma:
-- at any point in the fold, if the accumulator has all stuff of degree <= 2,
-- and kappa is well formed (whatever that means), then the result of the
-- fold will also have all stuff of degree <= 2.


theorem isRefinedBy_lowerDegreeby
    (c : Constraints p ι) {κ c'} (h : c.lowerDegreeToTwo = ⟨κ, c'⟩) :
    c ⊑ c' := by
  sorry


theorem Constraints.lowerDegreeToTwo_cons (c : Expr p ι) (cs : Constraints p ι) :
    Constraints.lowerDegreeToTwo.go ⟨k, vars, newCs⟩ (c :: cs) = ⟨k', vars', cs'⟩
    ↔ ∃ d ds,
        cs' = d :: ds := by
  simp only [lowerDegreeToTwo.go_cons]
  sorry

theorem Expr.maxDegree_lowerDegree {e : Expr p ι}
    (h_vars : vars.maxDegree ≤ 2) :
    e.lowerDegreeToTwo vars = ⟨κ', vars', e'⟩
    → vars'.maxDegree ≤ 2 ∧ e'.maxDegree ≤ 2 := by
  -- suffices ∀ {ι'} {e : Expr p ι'} {h : ι' ≤ ι},
  --   (e.castLE h).lowerDegreeToTwo vars = ⟨κ', vars', e'⟩
  --   → vars'.maxDegree ≤ 2 ∧ e'.maxDegree ≤ 2
  -- by
  --   intro h
  --   apply @this ι e (by rfl)
  --   simpa using h

  -- let k := sizeOf e
  -- induction k using Nat.strong_induction_on

  -- intro ι' e h_le h

  intro h
  fun_induction lowerDegreeToTwo vars e
    <;> simp only [Sigma.mk.injEq] at h
  case case1 =>
    rcases h with ⟨rfl, h⟩
    simp only [Nat.add_zero, heq_eq_eq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    simp [maxDegree, h_vars]
  case case2 =>
    rcases h with ⟨rfl, h⟩
    simp only [Nat.add_zero, heq_eq_eq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    simp [maxDegree, h_vars]
  case case3 v₁ e₁' he₁ _ v₂ e₂' he₂ ih₁ ih₂ =>
    rcases h with ⟨rfl, h⟩
    simp only [heq_eq_eq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    simp only [Assignments.maxDegree_castLE, maxDegree, maxDegree_castLE, sup_le_iff]

    specialize @ih₁ v₁.castLE ?e h_vars
    specialize @ih₂ v₂

    · sorry
    · sorry
  case case4 =>
    rcases h with ⟨rfl, h⟩
    simp only [heq_eq_eq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    simp only [Assignments.maxDegree_castLE, maxDegree, maxDegree_castLE, sup_le_iff]

    sorry
  case case5 =>
    sorry

theorem Expr.maxDegree_lowerDegree₁ {e : Expr p ι}
    (h_vars : vars.maxDegree ≤ 2) :
    (e.lowerDegreeToTwo vars).2.1.maxDegree ≤ 2 := by
  generalize hr : e.lowerDegreeToTwo vars = res
  apply (maxDegree_lowerDegree h_vars hr).1

theorem Expr.maxDegree_lowerDegree₂ (e : Expr p ι)
    (h_vars : vars.maxDegree ≤ 2) :
    (e.lowerDegreeToTwo vars).2.2.maxDegree ≤ 2 := by
  generalize hr : e.lowerDegreeToTwo vars = res
  apply (maxDegree_lowerDegree h_vars hr).2

open Assignments in
theorem Constraints.maxDegree_lowerDegree
    (cs : Constraints p ι) (h : cs.lowerDegreeToTwo = ⟨κ, cs'⟩) :
    cs'.maxDegree ≤ 2 := by
  suffices ∀ {κ₀ vars₀ cs₀ κ' vars' cs'},
    lowerDegreeToTwo.go ⟨κ₀, vars₀, cs₀⟩ cs = ⟨κ', vars', cs'⟩
    → vars₀.maxDegree ≤ 2
    → cs₀.maxDegree ≤ 2
    → vars'.maxDegree ≤ 2 ∧ cs'.maxDegree ≤ 2
  by
    simp only [lowerDegreeToTwo] at h
    generalize hr : (lowerDegreeToTwo.go ⟨0, ([], [])⟩ cs) = res at h
    rcases h with ⟨rfl, rfl⟩
    stop
    apply this 0 [] [] κ _ cs' h
  clear h
  intro κ₀ vars₀ cs₀ κ' vars' cs' h_eq h_degree_vars₀ h_degree_cs₀
  induction cs generalizing κ₀
  case nil =>
    simp only [lowerDegreeToTwo.go_nil, Sigma.mk.injEq] at h_eq
    rcases h_eq with ⟨rfl, h_eq⟩
    simp only [heq_eq_eq, Prod.mk.injEq] at h_eq
    rcases h_eq with ⟨rfl, rfl⟩
    and_intros <;> assumption
  case cons c cs ih =>
    simp only [lowerDegreeToTwo.go_cons] at h_eq
    apply ih h_eq
    · simpa using Expr.maxDegree_lowerDegree₁ (by assumption)
    · simp only [maxDegree_add, maxDegree_castLE, Expr.maxDegree_castLE, sup_le_iff]
      and_intros
      · assumption
      · apply Expr.maxDegree_lowerDegree₂
        assumption
