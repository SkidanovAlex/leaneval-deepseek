import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BSKinetic

open MeasureTheory

/-- The moving-box mean `bsMean ℓ u ψ = (ℓ³)⁻¹ ∫_{acube ℓ} ψ(ℓ•u + z) dz` of a function `ψ` that
is pointwise bounded by `M` is again bounded by `M` in absolute value: the box has volume `ℓ³`
and the average of a function bounded by `M` stays bounded by `M`. -/
theorem abs_bsMean_le {ℓ M : ℝ} (hℓ : 0 < ℓ) {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hψ : ∀ x, |ψ x| ≤ M) :
    ∀ u : EuclideanSpace ℝ (Fin 3), |Work.BSKinetic.bsMean ℓ u ψ| ≤ M := by
  have hvol : (volume : Measure (EuclideanSpace ℝ (Fin 3))).real
      (Submission.BoseGases.acube ℓ) = ℓ ^ 3 := by
    rw [Measure.real_def, Submission.BoseGases.acube_volume ℓ hℓ.le,
      ENNReal.toReal_ofReal (by positivity)]
  have hℓ3pos : (0 : ℝ) < ℓ ^ 3 := by positivity
  intro u
  have hInt : |∫ z in Submission.BoseGases.acube ℓ, ψ (ℓ • u + z)|
      ≤ M * (volume : Measure (EuclideanSpace ℝ (Fin 3))).real
          (Submission.BoseGases.acube ℓ) := by
    rw [← Real.norm_eq_abs]
    apply MeasureTheory.norm_setIntegral_le_of_norm_le_const
    · rw [Submission.BoseGases.acube_volume ℓ hℓ.le]
      exact ENNReal.ofReal_lt_top
    · intro z hz
      simpa [Real.norm_eq_abs] using hψ (ℓ • u + z)
  rw [hvol] at hInt
  rw [Work.BSKinetic.bsMean, abs_mul, abs_of_pos (inv_pos.mpr hℓ3pos)]
  calc (ℓ ^ 3)⁻¹ * |∫ z in Submission.BoseGases.acube ℓ, ψ (ℓ • u + z)|
      ≤ (ℓ ^ 3)⁻¹ * (M * ℓ ^ 3) :=
        mul_le_mul_of_nonneg_left hInt (by positivity)
    _ = M := by field_simp

end Work.BSKinetic
