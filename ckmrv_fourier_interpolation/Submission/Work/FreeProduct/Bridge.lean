import Mathlib
import Submission.Work.FreeProduct.Basic
import Submission.Work.FreeProduct.Length
import Submission.Work.FreeProduct.T_zpow_injective
import Submission.Work.FreeProduct.Tools
import Submission.Work.FreeProduct.orbit_corollary

/-!
# The group algebra `ℂ[ℤ/2 ∗ ℤ/3]` and the two "first letter" predicates

This file sets up the group algebra `RR = ℂ[FP]` with the elements

`X` (the involution), `Y` (order three), `Y2 = Y²`, `T = X * Y` and the two idempotent-like
elements `MU = 1 + Y + Y²` and `MUp = Y² - Y + 1` appearing in the CKMRV right ideals.

It also defines the two predicates on group elements that drive every reduction argument:

* `XF γ`  : the reduced word of `γ` does **not** start with the letter `y` or `y²`
  (so `γ = 1` or `γ` starts with `x`),
* `NX γ`  : the reduced word of `γ` does **not** start with `x` (so `γ = 1` or `γ` starts with
  `y` or `y²`).
-/

namespace Work.FreeProduct

open Work.Modular.PresGroup
open scoped MonoidAlgebra

noncomputable section

/-- The group algebra of `FP = ℤ/2 ∗ ℤ/3`. -/
abbrev RR : Type := MonoidAlgebra ℂ FP

/-- The involution `x = gC2`, as an element of the group algebra. -/
def X : RR := MonoidAlgebra.of ℂ FP x

/-- The element `y = gC3` of order three, as an element of the group algebra. -/
def Y : RR := MonoidAlgebra.of ℂ FP y

/-- `y²` as an element of the group algebra. -/
def Y2 : RR := MonoidAlgebra.of ℂ FP y2

/-- `T = x * y` as an element of the group algebra. -/
def TT : RR := MonoidAlgebra.of ℂ FP T

theorem X_mul_Y : X * Y = TT := by
  rw [X, Y, TT, ← map_mul]; rfl

theorem X_mul_X : X * X = 1 := by rw [X, ← map_mul, x_sq, map_one]

theorem Y_mul_Y : Y * Y = Y2 := by rw [Y, Y2, ← map_mul, y_mul_y]

theorem Y_mul_Y2 : Y * Y2 = 1 := by rw [Y, Y2, ← map_mul, y_mul_y2, map_one]

theorem Y2_mul_Y : Y2 * Y = 1 := by rw [Y, Y2, ← map_mul, y2_mul_y, map_one]

theorem y2_mul_y2 : y2 * y2 = y := by
  have h2 : y2 = y ^ 2 := by rw [y2, pow_two]
  rw [h2, ← pow_add]
  norm_num
  rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_add, y_cube, one_mul, pow_one]

theorem Y2_mul_Y2 : Y2 * Y2 = Y := by
  rw [Y, Y2, ← map_mul, y2_mul_y2]

/-- `μ = 1 + y + y²`. -/
def MU : RR := 1 + Y + Y2

/-- `μ' = y² - y + 1`. -/
def MUp : RR := Y2 - Y + 1

theorem MU_mul_Y : MU * Y = MU := by
  rw [MU, add_mul, add_mul, one_mul, Y_mul_Y, Y2_mul_Y]
  abel

theorem MU_mul_Y2 : MU * Y2 = MU := by
  rw [MU, add_mul, add_mul, one_mul, Y_mul_Y2, Y2_mul_Y2]
  abel

theorem MUp_mul_Y : MUp * Y = Y - Y2 + 1 := by
  rw [MUp, add_mul, sub_mul, one_mul, Y2_mul_Y, Y_mul_Y]
  abel

/-- The reduced word of `γ` does not start with a `ℤ/3`-letter. -/
def XF (γ : FP) : Prop := (Monoid.CoprodI.Word.equiv γ).fstIdx ≠ some true

/-- The reduced word of `γ` does not start with `x`. -/
def NX (γ : FP) : Prop := (Monoid.CoprodI.Word.equiv γ).fstIdx ≠ some false

theorem XF_one : XF (1 : FP) := by
  rw [XF, equiv_one, fstIdx_empty]; exact fun h => nomatch h

end

end Work.FreeProduct
