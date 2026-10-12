import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.BoseBoxFock.KinRowQuant
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Dilation covariance of the `p`-convention Fourier transform

The `p`-convention Fourier transform `kinFT u p = ∫ y, e^{−i⟪p,y⟫} u(y) dy`
(`Submission.Work.SmallBoxBridge.Defs`) is, up to the factor `(2π)⁻³`, the usual one; the
identity proved here is its behaviour under a **scaling of the argument**:

`∫ y, e^{−i⟪p,y⟫} u(ℓ • y) dy = (ℓ³)⁻¹ · kinFT u (ℓ⁻¹ • p)`   for `ℓ > 0`.

The change of variables `y ↦ ℓ⁻¹ • y` scales the Lebesgue measure by `ℓ³` (dimension `3`) and
sends the phase `⟪p, ℓ⁻¹ • y⟫ = ⟪ℓ⁻¹ • p, y⟫` (real inner product, `ℓ⁻¹ · ℓ = 1`).  This is the
identity that lets a bound at one length scale be transferred to a dilated box.
-/

namespace Work.BoseBoxFock

open MeasureTheory

/-- **Dilation of the `p`-convention Fourier transform.**  For `ℓ > 0` and any `u : ℝ³ → ℂ`,
`∫ y, e^{−i⟪p,y⟫} u(ℓ • y) dy = (ℓ³)⁻¹ · kinFT u (ℓ⁻¹ • p)`.

The proof is the additive-Haar change of variables `x ↦ ℓ • x` on `ℝ³` (dimension `3`), the
factor `(ℓ³)⁻¹` being `|(ℓ ^ finrank ℝ ℝ³)⁻¹| = (ℓ³)⁻¹`, together with the rescaling of the
phase via `real_inner_smul_left`/`real_inner_smul_right`. -/
theorem kinFT_comp_smul {ℓ : ℝ} (hℓ : 0 < ℓ) (u : ℝ³ → ℂ) (p : ℝ³) :
    (∫ y, Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * u (ℓ • y))
      = (ℓ ^ 3)⁻¹ * Submission.BoseGases.kinFT u (ℓ⁻¹ • p) := by
  -- the phase is invariant: `⟪p, y⟫ = ⟪ℓ⁻¹ • p, ℓ • y⟫`
  have hinner : ∀ y : ℝ³, inner ℝ (ℓ⁻¹ • p) (ℓ • y) = inner ℝ p y := by
    intro y
    rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc, inv_mul_cancel₀ hℓ.ne', one_mul]
  -- rewrite the left-hand side as the dilation of the integrand of `kinFT u (ℓ⁻¹ • p)`
  have h1 : (∫ y, Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * u (ℓ • y))
      = ∫ y, (fun z : ℝ³ =>
          Complex.exp (-(Complex.I * (inner ℝ (ℓ⁻¹ • p) z : ℂ))) * u z) (ℓ • y) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [← hinner y]
  rw [h1, MeasureTheory.Measure.integral_comp_smul_of_nonneg (MeasureTheory.volume : Measure ℝ³)
        (fun z : ℝ³ => Complex.exp (-(Complex.I * (inner ℝ (ℓ⁻¹ • p) z : ℂ))) * u z) ℓ
        (hR := hℓ.le)]
  -- `finrank ℝ ℝ³ = 3`, and the `ℝ`-scalar action on `ℂ` is multiplication by the coerced scalar
  rw [Submission.BoseGases.kinFT]
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  rw [Algebra.smul_def]
  norm_num

end Work.BoseBoxFock
