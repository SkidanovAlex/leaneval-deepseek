/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The Cauchy potential and the Beurling transform on `ℂ`

This file sets up the one variable `∂̄`-operators used to solve the `∂̄`-equation on
discs, in the flat (standard) case.

## Conventions

We identify `ℂ` with `ℝ²`, so that `volume` on `ℂ` is Lebesgue measure and
`∂̄u = (1/2)(∂_x u + i ∂_y u)`.

* `cauchyTransform ρ f z = -(1/π) ∫_{‖w‖<ρ} (f (z+w) - f z)/w` is the Cauchy
  potential of `f`.  The subtraction is what makes the integral absolutely
  convergent for `f` Hölder near `z`; the value differs from the "unsubtracted"
  integral by `f z ∫_{‖w‖<ρ} 1/w = 0`, see `integral_inv_ball`.
* `cauchyTransformUnsub ρ f z = -(1/π) ∫_{‖w‖<ρ} f (z+w)/w` is the same quantity
  whenever the integral converges absolutely (e.g. `f` bounded).
* `beurlingTransform ρ f z = -(1/π) ∫_{‖w‖<ρ} (f (z+w) - f z)/w^2` is the
  Beurling transform, i.e. the `z`-derivative of `T f`.

The constants are normalised so that `∂̄ (T f) = f` and `∂_z (T f) = S f`; the
normalisation is the standard one and is stable: callers should use the
definitions rather than reproduce the constants.
-/
import Mathlib
import Submission.Work.CR.Flat.Holder

noncomputable section

open scoped NNReal ENNReal
open MeasureTheory Set

namespace Work.CR.Flat

/-- The Cauchy kernel `w ↦ 1/w` on `ℂ`. -/
def cauchyKernel (w : ℂ) : ℂ := w⁻¹

@[simp] lemma cauchyKernel_apply (w : ℂ) : cauchyKernel w = w⁻¹ := rfl

/-- The Cauchy potential of `f` on the disc of radius `ρ`:
`T f z = -(1/π) ∫_{‖w‖ < ρ} (f (z + w) - f z)/w`. -/
noncomputable def cauchyTransform (ρ : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  -((Real.pi : ℂ))⁻¹ * ∫ w in Metric.ball 0 ρ, (f (z + w) - f z) / w

/-- The same potential without the subtraction.  For bounded `f` the integral
converges absolutely and equals `cauchyTransform`: the difference is
`f z ∫_{‖w‖<ρ} 1/w = 0`. -/
noncomputable def cauchyTransformUnsub (ρ : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  -((Real.pi : ℂ))⁻¹ * ∫ w in Metric.ball 0 ρ, f (z + w) / w

/-- The Beurling transform of `f`: the `z`-derivative of the Cauchy potential. -/
noncomputable def beurlingTransform (ρ : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  -((Real.pi : ℂ))⁻¹ * ∫ w in Metric.ball 0 ρ, (f (z + w) - f z) / w ^ 2

/-- `f` vanishes outside the closed ball of radius `R` around the origin. -/
def SupportedInBall (R : ℝ) (f : ℂ → ℂ) : Prop := ∀ z : ℂ, R ≤ ‖z‖ → f z = 0

/-- The flat `∂̄`-operator on `ℂ`: `∂̄u = (1/2)(∂_x u + i ∂_y u)`. -/
noncomputable def dbarC (u : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ u z 1 + Complex.I * fderiv ℝ u z Complex.I)

/-- The `z`-derivative `∂_z u = (1/2)(∂_x u - i ∂_y u)` on `ℂ`. -/
noncomputable def dzC (u : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ u z 1 - Complex.I * fderiv ℝ u z Complex.I)

/-- The Cauchy kernel has mean zero on discs centred at the origin:
`∫_{‖w‖<ρ} 1/w = 0`.  This is the basic cancellation behind both the absolute
convergence of the Cauchy potential and the estimates for the Beurling
transform. -/
lemma integral_inv_ball (ρ : ℝ) : ∫ w in Metric.ball (0 : ℂ) ρ, w⁻¹ = 0 := by
  have h := MeasurableEmbedding.setIntegral_map (μ := (volume : Measure ℂ)) measurableEmbedding_neg
    (fun w : ℂ => w⁻¹) (Metric.ball (0 : ℂ) ρ)
  rw [Measure.map_neg_eq_self (volume : Measure ℂ)] at h
  have hball : (Neg.neg ⁻¹' Metric.ball (0 : ℂ) ρ : Set ℂ) = Metric.ball 0 ρ := by
    ext x; simp [Metric.mem_ball]
  rw [hball] at h
  simp only [inv_neg] at h
  rw [MeasureTheory.integral_neg] at h
  have h3 : (∫ w in Metric.ball (0 : ℂ) ρ, w⁻¹) + (∫ w in Metric.ball (0 : ℂ) ρ, w⁻¹) = 0 := by
    nth_rewrite 1 [h]; abel
  have h2 : (∫ w in Metric.ball (0 : ℂ) ρ, w⁻¹) * 2 = 0 := by
    have : (∫ w in Metric.ball (0 : ℂ) ρ, w⁻¹) * 2
        = (∫ w in Metric.ball (0 : ℂ) ρ, w⁻¹) + (∫ w in Metric.ball (0 : ℂ) ρ, w⁻¹) := by
      ring
    rw [this]; exact h3
  exact (mul_eq_zero.mp h2).resolve_right (by norm_num)

end Work.CR.Flat
