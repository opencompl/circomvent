/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Qq
import Lean
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Ring
import Mathlib

import SSA.Core

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

def BabyBear := 2^31 - 2^27 + 1

@[reducible]
instance : TyDenote Ty where
  toType
    | .int => BitVec 32
    | .felt => ZMod BabyBear

deriving instance Lean.ToExpr for (ZMod BabyBear)

inductive Op : Type
  | add : Op
  | addFelt : Op
  | const : (val : ℤ) → Op
  | constFelt : (val : ℤ) → Op
  deriving DecidableEq, Repr, Lean.ToExpr

instance (a : Ty) : Repr ⟦a⟧ :=
  match a with
  | .int => by simp [toType]; infer_instance
  | .felt => by simp [toType]; infer_instance

/-- `Simple` is a very basic example dialect -/
abbrev Simple : Dialect where
  Op := Op
  Ty := Ty

instance : ToString Ty where
  toString t := repr t |>.pretty

instance : DialectToExpr Simple where
  toExprM := .const ``Id [0]
  toExprDialect := .const ``Simple []

def_signature for Simple
  | .add      => (.int, .int) → .int
  | .addFelt  => (.felt, .felt) → .felt
  | .const _  => () → .int
  | .constFelt _  => () → .felt

def_denote for Simple
  | .add     => fun a b => a + b ::ₕ .nil
  | .addFelt => fun a b => a + b ::ₕ .nil
  | .const n => BitVec.ofInt 32 n ::ₕ .nil
  | .constFelt n => (n : ZMod BabyBear) ::ₕ .nil

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
  | "felt.add" =>
    mkExpr Γ opStx (Op.addFelt)
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
    MLIR.AST.ReaderM Simple (Σ eff ty, Com Simple Γ eff ty) :=
  if opStx.name == "return"
  then match opStx.args with
  | vStx::[] => do
    let ⟨ty, v⟩ ← MLIR.AST.TypedSSAVal.mkVal Γ vStx
    return ⟨.pure, [ty], Com.ret v⟩
  | _ => throw <| .generic (
      s!"Ill-formed return statement (wrong arity, expected 1, got {opStx.args.length})")
  else throw <| .generic s!"Tried to build return out of non-return statement {opStx.name}"

instance : MLIR.AST.TransformReturn Simple 0 where
  mkReturn := mkReturn

open Qq in
elab "[simple_com| " reg:mlir_region "]" : term => SSA.elabIntoCom' reg (Simple)

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

/-- info: [0x00000008#32] -/
#guard_msgs in #eval eg₀val

open MLIR AST MLIR2Simple in
/-- x + 0 -/
def lhs : Com Simple (Ctxt.ofList [.int]) .pure [.int] :=
  [simple_com| {
    ^bb0(%x : i32):
      %c0 = "const" () { value = 0 : i32 } : () -> i32
      %out = "add" (%x, %c0) : (i32, i32) -> i32
      "return" (%out) : (i32) -> (i32)
  }]

/--
info: {
  ^entry(%0 : ToyNoRegion.Ty.int):
    %1 = ToyNoRegion.Op.const 0 : () → (ToyNoRegion.Ty.int)
    %2 = ToyNoRegion.Op.add(%0, %1) : (ToyNoRegion.Ty.int, ToyNoRegion.Ty.int) → (ToyNoRegion.Ty.int)
    return %2 : (ToyNoRegion.Ty.int) → ()
}
-/
#guard_msgs in #eval lhs

open MLIR AST MLIR2Simple in
/-- x -/
def rhs : Com Simple (Ctxt.ofList [.int]) .pure [.int] :=
  [simple_com| {
    ^bb0(%x : i32):
      "return" (%x) : (i32) -> (i32)
  }]


/--
info: {
  ^entry(%0 : ToyNoRegion.Ty.int):
    return %0 : (ToyNoRegion.Ty.int) → ()
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
  ^entry(%0 : ToyNoRegion.Ty.int):
    %1 = ToyNoRegion.Op.const 0 : () → (ToyNoRegion.Ty.int)
    %2 = ToyNoRegion.Op.add(%0, %1) : (ToyNoRegion.Ty.int, ToyNoRegion.Ty.int) → (ToyNoRegion.Ty.int)
    return %0 : (ToyNoRegion.Ty.int) → ()
}
-/
#guard_msgs (whitespace := lax) in #eval rewritePeepholeAt p1 1 lhs
example : rewritePeephole (fuel := 100) p1 lhs = rewritePeepholeAt p1 1 lhs := by
  native_decide

open MLIR AST MLIR2Simple in
def eg1 : Com Simple (Ctxt.ofList []) .pure [.felt] :=
  [simple_com| {
    %c2 = "constFelt"() {value = 2} : () -> !felt.type
    %c4 = "constFelt"() {value = 4} : () -> !felt.type
    %c6 = "add"(%c2, %c4) : (!felt.type, !felt.type) -> !felt.type
    %c8 = "add"(%c6, %c2) : (!felt.type, !felt.type) -> !felt.type
    "return"(%c8) : (!felt.type) -> ()
  }]

def eg1val := Com.denote eg1 Ctxt.Valuation.nil

/-- info: [8] -/
#guard_msgs in #eval eg1val


def compute : Com Simple (⟨[.felt]⟩) .pure [.felt, .felt] :=
  [simple_com| {
       %const_0 = "felt.const"() { value = 0 } : () -> !felt.type
       %const_1 = felt.const 1
       %1 = bool.cmp ne(%in, %const_0)
       %inv = felt.inv %in
       %4 = felt.neg %in
       %5 = felt.mul %4, %inv
       %out = felt.add %5, %const_1
       function.return %out, %inv
  }]

/-!

  //   function.def @compute(%in: !felt.type) -> (!felt.type, !felt.type) {
  //     %const_0 = felt.const 0
  //     %const_1 = felt.const 1
  //     %1 = bool.cmp ne(%in, %const_0)
  //     %inv = felt.inv %in
  //     %4 = felt.neg %in
  //     %5 = felt.mul %4, %inv
  //     %out = felt.add %5, %const_1
  //     function.return %out, %inv
  //   }

-/

end ToyNoRegion
