import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.dict13Aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.dict13Aux3` — the two functionals of `dict13_L1` and the value truncation

`dict13_L1` states `((ℓ^3)⁻¹) * (rowShape13 … (qmqKernel ℓ k) p).re = ∫_{abox} … k (x p.1) (x p.2)`.
The two sides are bundled here as the functionals `lhsFun` and `rhsFun` of the pair kernel, so that
the pieces of the proof (a.e. invariance, `L¹`-continuity, linearity) can be stated about them; the
target is then the single identity `lhsFun ℓ Ψ c p k = rhsFun ℓ Ψ p k`.

`trunc N φ` is the level truncation `φ` killed where `‖φ‖ > N`; it is measurable, bounded by `N`,
symmetric whenever `φ` is, and converges to `φ` pointwise with `‖φ - trunc N φ‖ ≤ ‖φ‖`.

Everything here is `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Submission.BoseGases.X

set_option autoImplicit false

/-- The `Q M Q` box dictionary left-hand side at a pair kernel `e` (the `(ℓ³)⁻¹·re` of the block-I
row). -/
noncomputable def lhsFun {n : ℕ} (ℓ : ℝ) (Ψ : Xn n → ℝ) (c : ℂ) (p : Fin n × Fin n)
    (e : E3 → E3 → ℝ) : ℝ :=
  ((ℓ ^ 3)⁻¹ : ℝ) * (rowShape13 (boxRestrictC ℓ Ψ)
    (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y)
    (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y) (qmqKernel ℓ e) p).re

/-- The `Q M Q` box dictionary right-hand side at a pair kernel `e` (the position-space pair word
of `qmqDefs.q1WordK`). -/
noncomputable def rhsFun {n : ℕ} (ℓ : ℝ) (Ψ : Xn n → ℝ) (p : Fin n × Fin n)
    (e : E3 → E3 → ℝ) : ℝ :=
  ∫ x in Submission.BoseGases.abox n ℓ,
    Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aQ ℓ p.2 Ψ) x
      * Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Ψ) x * e (x p.1) (x p.2)

/-- The value truncation of a pair kernel: `φ` killed where `‖φ‖ > N`. -/
noncomputable def trunc (N : ℕ) (φ : E3 → E3 → ℝ) : E3 → E3 → ℝ :=
  fun a b => if ‖φ a b‖ ≤ (N : ℝ) then φ a b else 0

@[simp] theorem trunc_apply (N : ℕ) (φ : E3 → E3 → ℝ) (a b : E3) :
    trunc N φ a b = if ‖φ a b‖ ≤ (N : ℝ) then φ a b else 0 := rfl

theorem trunc_abs_le (N : ℕ) (φ : E3 → E3 → ℝ) (a b : E3) : ‖trunc N φ a b‖ ≤ (N : ℝ) := by
  rw [trunc_apply]
  by_cases h : ‖φ a b‖ ≤ (N : ℝ)
  · rw [if_pos h]; exact h
  · rw [if_neg h, norm_zero]; positivity

theorem trunc_symm {φ : E3 → E3 → ℝ} (hφ : ∀ a b, φ a b = φ b a) (N : ℕ) (a b : E3) :
    trunc N φ a b = trunc N φ b a := by
  rw [trunc_apply, trunc_apply, hφ a b]

theorem trunc_sub_abs (N : ℕ) (φ : E3 → E3 → ℝ) (a b : E3) :
    ‖φ a b - trunc N φ a b‖ = if ‖φ a b‖ ≤ (N : ℝ) then 0 else ‖φ a b‖ := by
  rw [trunc_apply]
  by_cases h : ‖φ a b‖ ≤ (N : ℝ)
  · rw [if_pos h, sub_self, norm_zero, if_pos h]
  · rw [if_neg h, sub_zero, if_neg h]

end Work.BoseBoxFock
