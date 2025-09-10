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

def Constraints (p ι : Nat) :=
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
      : IsRefinedBy c₁ c₂

infixl:67 " ⊑ " => Constraint.IsRefinedBy

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
      · have : env.append [y, z].get 0 = env 0 := rfl
        have : env.append [y, z].get 1 = y := rfl
        have : env.append [y, z].get 2 = z := rfl
        simp [*]

    -- It's a bit surprising we need to rewrite along this have manually
    have (x y : ZMod p) : x - y = 0 ↔ x = y := by grind
    simp only [this]
    grind



example (env : Environment p 3) :
    LowerOrder.eval env → HigherOrder.eval env.restrict := by
  unfold LowerOrder HigherOrder
  simp only [Constraints.eval, Fin.isValue, List.all_cons, Expr.eval, Nat.cast_one, List.all_nil,
    Bool.and_true, Bool.and_eq_true, beq_iff_eq, Environment.restrict, Fin.castLE_zero]
  grind
