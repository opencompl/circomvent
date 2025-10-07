/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Qq
import Lean
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Ring
import Mathlib

import LeanMLIR
import SSA.Projects.SLLVM.Tactic
-- import SSA.Core.MLIRSyntax.Transform.Utils

open BitVec
open Ctxt(Var)

@[simp]
theorem BitVec.ofInt_zero (w : ℕ) :
    BitVec.ofInt w 0 = 0 :=
  rfl

namespace ToyNoRegion

inductive Ty
  | int
  | felt
  deriving DecidableEq, Repr, Lean.ToExpr

@[grind=]
def BabyBear := 2^31 - 2^27 + 1

instance : Fact (BabyBear.Prime) := by
  native_decide

@[reducible]
instance : TyDenote Ty where
  toType
    | .int => BitVec 32
    | .felt => ZMod BabyBear

deriving instance Lean.ToExpr for (ZMod BabyBear)

inductive Op : Type
  | add : Op
  | addFelt : Op
  | mulFelt : Op
  | negFelt : Op
  | invFelt : Op
  | const : (val : ℤ) → Op
  | constFelt : (val : ℤ) → Op
  | constrainEq : Op
  deriving DecidableEq, Repr, Lean.ToExpr

instance (a : Ty) : Repr ⟦a⟧ :=
  match a with
  | .int => by simp [toType]; infer_instance
  | .felt => by simp [toType]; infer_instance

/-- `Simple` is a very basic example dialect -/
abbrev Simple : Dialect where
  Op := Op
  Ty := Ty
  m := PoisonOr

instance : ToString Ty where
  toString t := repr t |>.pretty

instance : DialectToExpr Simple where
  toExprM := .const ``Id [0]
  toExprDialect := .const ``Simple []

def_signature for Simple
  | .add      => (.int, .int) → .int
  | .addFelt
  | .mulFelt  => (.felt, .felt) → .felt
  | .negFelt  => (.felt) → .felt
  | .invFelt  => (.felt) → .felt
  | .const _  => () → .int
  | .constFelt _  => () → .felt
  | .constrainEq => (.felt, .felt) -[.impure]-> []

def Poison.assert (c : Prop) [Decidable c] : PoisonOr Unit :=
  if c then .value () else .poison

@[simp, simp_denote]
theorem Poison.assert_bind_isPoison {c} [Decidable c]  :
    ((assert c >>= f).isPoison) = (!decide c || (f ()).isPoison) := by
  by_cases hc : c <;> simp [assert, hc]

def_denote for Simple
  | .add     => fun a b => a + b ::ₕ .nil
  | .addFelt => fun a b => [a + b]ₕ
  | .mulFelt => fun a b => [a * b]ₕ
  | .negFelt => fun a => [-a]ₕ
  | .invFelt => fun a => [(a⁻¹ : ZMod _)]ₕ
  | .const n => BitVec.ofInt 32 n ::ₕ .nil
  | .constFelt n => (n : ZMod BabyBear) ::ₕ .nil
  | .constrainEq => fun a b => do
      Poison.assert (a = b)
      return []ₕ

example : (0 : ZMod BabyBear)⁻¹ = 0 := by
  exact ZMod.inv_zero BabyBear

def cst {Γ : Ctxt _} (n : ℤ) : Expr Simple Γ .pure [.int]  :=
  Expr.mk
    (op := .const n)
    (eff_le := by constructor)
    (ty_eq := rfl)
    (args := .nil)
    (regArgs := .nil)

def cstFelt {Γ : Ctxt _} (n : ℤ) : Expr Simple Γ .pure [.felt]  :=
  Expr.mk
    (op := .constFelt n)
    (eff_le := by constructor)
    (ty_eq := rfl)
    (args := .nil)
    (regArgs := .nil)

def add {Γ : Ctxt _} (e₁ e₂ : Var Γ .int) : Expr Simple Γ .pure [.int] :=
  Expr.mk
    (op := .add)
    (eff_le := by constructor)
    (ty_eq := rfl)
    (args := .cons e₁ <| .cons e₂ .nil)
    (regArgs := .nil)

def addFelt {Γ : Ctxt _} (e₁ e₂ : Var Γ .felt) : Expr Simple Γ .pure [.felt] :=
  Expr.mk
    (op := .addFelt)
    (eff_le := by constructor)
    (ty_eq := rfl)
    (args := .cons e₁ <| .cons e₂ .nil)
    (regArgs := .nil)

attribute [local simp] Ctxt.snoc

namespace MLIR2Simple

def mkTy : MLIR.AST.MLIRType φ → MLIR.AST.ExceptM Simple Ty
  | MLIR.AST.MLIRType.int MLIR.AST.Signedness.Signless _ => do
    return .int
  | MLIR.AST.MLIRType.undefined "felt.type" => return .felt
  | _ => throw .unsupportedType

instance instTransformTy : MLIR.AST.TransformTy Simple 0 where
  mkTy := mkTy

def mkExpr (Γ : Ctxt _) (opStx : MLIR.AST.Op 0) :
    MLIR.AST.ReaderM Simple (Σ eff ty, Expr Simple Γ eff ty) := do
  match opStx.name with
  | "const" =>
    match opStx.attrs.find_int "value" with
    | .some (v, _ty) => return ⟨.pure, [.int], cst v⟩
    | .none => throw <| .generic s!"expected 'const' to have int attr 'value', found: {repr opStx}"
  | "felt.const" =>
    match opStx.attrs.find_int "value" with
    | .some (v, _ty) => return ⟨.pure, [.felt], cstFelt v⟩
    | .none => throw <| .generic s!"expected 'const' to have int attr 'value', found: {repr opStx}"
  | "felt.add" => opStx.mkExprOf Γ Op.addFelt
  | "felt.mul" => opStx.mkExprOf Γ Op.mulFelt
  | "felt.neg" => opStx.mkExprOf Γ Op.negFelt
  | "felt.inv" => opStx.mkExprOf Γ Op.invFelt
  | "constrain.eq" => opStx.mkExprOf Γ Op.constrainEq
  | "add" =>
    match opStx.args with
    | v₁Stx::v₂Stx::[] =>
      let ⟨argty1, v₁⟩ ← MLIR.AST.TypedSSAVal.mkVal Γ v₁Stx
      let ⟨argty2, v₂⟩ ← MLIR.AST.TypedSSAVal.mkVal Γ v₂Stx
      match argty1, argty2 with
      | .int, .int => return ⟨.pure, [.int], add v₁ v₂⟩
      | .felt, .felt => return ⟨.pure, [.felt], addFelt v₁ v₂⟩
      | _, _ => throw <| .generic (
        s!"left and right operands do not have the same type")
    | _ => throw <| .generic (
        s!"expected two operands for `add`, found #'{opStx.args.length}' in '{repr opStx.args}'")
  | _ => throw <| .unsupportedOp s!"unsupported operation {repr opStx}"

instance : MLIR.AST.TransformExpr Simple 0 where
  mkExpr := mkExpr

def mkReturn (Γ : Ctxt _) (opStx : MLIR.AST.Op 0) :
    MLIR.AST.ReaderM Simple (Σ eff ty, Com Simple Γ eff ty) := do
  if opStx.name == "return" then
    let args ← opStx.parseArgs Γ
    return ⟨.pure, args.types, Com.rets args.toHVector⟩
  else throw <| .generic s!"Tried to build return out of non-return statement {opStx.name}"

instance : MLIR.AST.TransformReturn Simple 0 where
  mkReturn := mkReturn

open Qq in
elab "[simple_com| " reg:mlir_region "]" : term => SSA.elabIntoCom' reg (Simple)

instance : DialectPrint Simple where
  printOpName
    | .add      => "add"
    | .const _  => "const"
    | .addFelt  => "felt.add"
    | .mulFelt  => "felt.mul"
    | .negFelt  => "felt.neg"
    | .invFelt  => "felt.inv"
    | .constFelt _ => "felt.const"
    | .constrainEq => "constrain.eq"
  printAttributes
    | .const val
    | .constFelt val => s!"\{value = {val}}"
    | _ => ""
  printTy
    | .felt => "!felt.type"
    | .int => "i32"
  dialectName := "felt"
  printReturn _ := "return"

end MLIR2Simple

open MLIR AST MLIR2Simple in
def eg₀ : Com Simple (Ctxt.ofList []) .pure [.int] :=
  [simple_com| {
    %c2 = "const"() {value = 2} : () -> i32
    %c4 = "const"() {value = 4} : () -> i32
    %c6 = "add"(%c2, %c4) : (i32, i32) -> i32
    %c8 = "add"(%c6, %c2) : (i32, i32) -> i32
    "return"(%c8) : (i32) -> ()
  }]

def eg₀val := Com.denote eg₀ Ctxt.Valuation.nil

/-- info: [8] -/
#guard_msgs in #eval eg₀val

open MLIR AST MLIR2Simple in
/-- x + 0 -/
def lhs : Com Simple (Ctxt.ofList [.int]) .pure [.int] :=
  [simple_com| {
    ^bb0(%x : i32):
      %c0 = "const" () { value = 0 : i32 } : () -> i32
      %out = "add" (%x, %c0) : (i32, i32) -> i32
      "return" (%out) : (i32) -> ()
  }]

/--
info: {
  ^entry(%0 : i32):
    %1 = "const"(){value = 0} : () -> (i32)
    %2 = "add"(%0, %1) : (i32, i32) -> (i32)
    "return"(%2) : (i32) -> ()
}
-/
#guard_msgs in #eval lhs

open MLIR AST MLIR2Simple in
/-- x -/
def rhs : Com Simple (Ctxt.ofList [.int]) .pure [.int] :=
  [simple_com| {
    ^bb0(%x : i32):
      "return" (%x) : (i32) -> ()
  }]


/--
info: {
  ^entry(%0 : i32):
    "return"(%0) : (i32) -> ()
}
-/
#guard_msgs in #eval rhs

open MLIR AST MLIR2Simple in
def p1 : PeepholeRewrite Simple [.int] [.int] :=
  { lhs := lhs, rhs := rhs, correct :=
    by
      rw [lhs, rhs]
      /-:
      Com.denote
        (Com.var (cst 0)
        (Com.var (add { val := 1, property := _ } { val := 0, property := _ })
        (Com.rets { val := 0, property := ex1.proof_3 }))) =
      Com.denote (Com.rets { val := 0, property := _ })
      -/
      simp_peephole
      /- ⊢ ∀ (a : BitVec 32), a + BitVec.ofInt 32 0 = a -/
      intros a
      simp only [ofInt_zero, ofNat_eq_ofNat, BitVec.add_zero]
      /- goals accomplished 🎉 -/
    }

/--
info: {
  ^entry(%0 : i32):
    %1 = "const"(){value = 0} : () -> (i32)
    %2 = "add"(%0, %1) : (i32, i32) -> (i32)
    "return"(%0) : (i32) -> ()
}
-/
#guard_msgs (whitespace := lax) in #eval rewritePeepholeAt p1 1 lhs
example : rewritePeephole (fuel := 100) p1 lhs = rewritePeepholeAt p1 1 lhs := by
  native_decide

open MLIR AST MLIR2Simple in
def eg1 : Com Simple (Ctxt.ofList []) .pure [.felt] :=
  [simple_com| {
    %c2 = "felt.const"() {value = 2} : () -> !felt.type
    %c4 = "felt.const"() {value = 4} : () -> !felt.type
    %c6 = "felt.add"(%c2, %c4) : (!felt.type, !felt.type) -> !felt.type
    %c8 = "felt.add"(%c6, %c2) : (!felt.type, !felt.type) -> !felt.type
    "return"(%c8) : (!felt.type) -> ()
  }]

def eg1val := Com.denote eg1 Ctxt.Valuation.nil

/-- info: [8] -/
#guard_msgs in #eval eg1val


/-!
## Program Wellformedness
-/
open Ctxt (Valuation)

structure Program (inputs : List Simple.Ty) (existentials : List Simple.Ty) (outputs : List Simple.Ty) where
  compute   : Com Simple inputs .pure (outputs ++ existentials)
  constrain : Com Simple ((outputs ++ existentials) ++ inputs) .impure []

/-!
### isZero Program
-/

def isZero : Program [.felt] [.felt] [.felt] where
  compute := [simple_com| {
    ^entry(%input : !felt.type) :
      %const_0 = "felt.const"() { value = 0 } : () -> !felt.type
      %const_1 = "felt.const"() { value = 1 } : () -> !felt.type
      %inv = "felt.inv"(%input) : (!felt.type) -> !felt.type
      %4 = "felt.neg" (%input) : (!felt.type) -> (!felt.type)
      %5 = "felt.mul" (%4, %inv) : (!felt.type, !felt.type) -> (!felt.type)
      %out = "felt.add" (%5, %const_1) : (!felt.type, !felt.type) -> (!felt.type)
      "return"(%out, %inv) : (!felt.type, !felt.type) -> ()
  }]
  constrain := [simple_com| {
    ^bb0(%arg1: !felt.type, %inv: !felt.type, %out: !felt.type):
      %0 = "felt.const"() <{value = 0 : !felt.type}> : () -> !felt.type
      %1 = "felt.const"() <{value = 1 : !felt.type}> : () -> !felt.type
      %4 = "felt.neg"(%arg1) : (!felt.type) -> !felt.type
      %5 = "felt.mul"(%4, %inv) : (!felt.type, !felt.type) -> !felt.type
      %6 = "felt.add"(%5, %1) : (!felt.type, !felt.type) -> !felt.type
      "constrain.eq"(%out, %6) : (!felt.type, !felt.type) -> ()
      %7 = "felt.mul"(%arg1, %out) : (!felt.type, !felt.type) -> !felt.type
      "constrain.eq"(%7, %0) : (!felt.type, !felt.type) -> ()
      "return"() : () -> ()
}]

/-!
## Checks
-/
open Ctxt (Valuation)

/-- info: [1, 0] -/
#guard_msgs in
#eval isZero.compute.denote (Ctxt.Valuation.nil.cons <| (0 : ZMod _))

/-- info: [0, 1] -/
#guard_msgs in
#eval isZero.compute.denote (Ctxt.Valuation.nil.cons <| (1 : ZMod _))

/-- info: { toOption := some [] } -/
#guard_msgs in
#eval isZero.constrain.denote (Valuation.ofHVector [(1 : ZMod _), (0 : ZMod _), (0 : ZMod _)]ₕ)

/-- info: { toOption := none } -/
#guard_msgs in
#eval isZero.constrain.denote (Valuation.ofHVector [(1 : ZMod _), (0 : ZMod _), (1 : ZMod _)]ₕ)

-- When input is `0` and output is `1` then `inv` is unconstrained!
/-- info: { toOption := some [] } -/
#guard_msgs in
#eval isZero.constrain.denote (Valuation.ofHVector [(1 : ZMod _), (10 : ZMod _), (0 : ZMod _)]ₕ)



def Program.Complete (p : Program ι ε ω) : Prop :=
  ∀ (is : Valuation ⟨ι⟩),
    let oes : HVector _ _ := p.compute.denote is
    !(p.constrain.denote (oes ++ is)).isPoison

def Program.Sound (p : Program ι ε ω) : Prop :=
  ∀ (is : HVector toType ι) (es : HVector toType ε) (os : HVector toType ω),
    !(p.constrain.denote (.ofHVector <| (os ++ es) ++ is)).isPoison
    → ∃ (es' : HVector toType ε),
        let oes : HVector _ _ := p.compute.denote (.ofHVector is)
        oes = os ++ es'

attribute [simp_denote]
  Valuation.ofHVector_cons Valuation.ofHVector_nil
  decide_true decide_false decide_eq_true_iff
  Bool.not_true Bool.not_false Bool.not_not
  Bool.true_or Bool.or_true Bool.false_or Bool.or_false
  Bool.true_and Bool.and_true Bool.false_and Bool.and_false

@[simp_denote, simp]
theorem PoisonOr.isPoison_pure (x : α) :
  PoisonOr.isPoison (pure x) = false := rfl

@[simp_denote, simp]
theorem toType_felt : toType Ty.felt = ZMod BabyBear := rfl

theorem complete_isZero : isZero.Complete := by
  unfold isZero
  simp_peephole
  intro i
  by_cases hi : i = 0
  <;> grind

/--
info: 'ToyNoRegion.complete_isZero' depends on axioms: [propext,
 Classical.choice,
 Lean.ofReduceBool,
 Lean.trustCompiler,
 Quot.sound]
-/
#guard_msgs in #print axioms complete_isZero


-- theorem sound_isZero : isZero.Sound := by
--   unfold isZero Program.Sound
--   simp_peephole
--   -- intro (i : ZMod _)
--   simp
--   repeat rw [Valuation.append_cons]
--   simp_peephole
--   have : Fact BabyBear.Prime := by
--     native_decide
--   by_cases hi : i = 0
--   · grind
--   · grind



/-!
## Degree Lowering
-/

-- def HigherOrder : Com Simple [Ty.felt] .impure [] :=
--   [simple_com| {
--     ^bb0(%x: !felt.type):
--       -- x * x * x * x * x + 1 -- x^5 + 1 === 0
--       %x2 = "felt.mul" (%x, %x) : (!felt.type, !felt.type) -> !felt.type
--       "return" () : () -> ()
-- }]

-- def LowerOrder : Constraints p 3 :=
--   let x := Expr.var 0
--   let y := Expr.var 1
--   let z := Expr.var 2
-- [
--   x * x - y, -- x^2 === y
--   y * y - z, -- y^2 === z
--   x * z + 1  -- x * z + 1 === 0
-- ]
