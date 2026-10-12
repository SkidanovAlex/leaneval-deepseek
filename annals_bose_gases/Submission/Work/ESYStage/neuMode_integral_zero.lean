import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.ESYStage.Defs
import Submission.Work.SmallBoxA0.KModeDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.ESYStage

open MeasureTheory

/-- The constant box-Neumann mode `k ≡ 0` is the constant function `1`. -/
lemma boxNeumann3_zero_eq_one (ℓ : ℝ) (z : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.boxNeumann3 ℓ 0 z = 1 := by
  simp [Submission.BoseGases.boxNeumann3, Submission.BoseGases.boxNeumann_zero]

/-- **The normalised product Neumann mode has vanishing box mean off the
condensate direction.**  For `k ≠ 0` the pairing of `φ_k` with the constant mode
`φ_0 ≡ 1` is the `L²`-orthogonality of the box mode family already proved in the
library (`Work.SmallBoxA0.boxNeumann3_pair_integral`), hence the mean of `φ_k`
vanishes. -/
theorem neuMode_integral_zero {ℓ : ℝ} (hℓ : 0 < ℓ) {k : Fin 3 → ℕ} (hk : k ≠ 0) :
    (∫ x in Submission.BoseGases.acube ℓ, Work.ESYStage.neuMode ℓ k x) = 0 := by
  have hpair := Work.SmallBoxA0.boxNeumann3_pair_integral hℓ k 0
  rw [if_neg hk] at hpair
  have hint : (∫ x in Submission.BoseGases.acube ℓ,
      Submission.BoseGases.boxNeumann3 ℓ k x) = 0 := by
    rw [← hpair]
    simp only [boxNeumann3_zero_eq_one, mul_one]
  change (∫ x in Submission.BoseGases.acube ℓ,
      (Real.sqrt (∏ j : Fin 3, Submission.BoseGases.coordSqNorm ℓ (k j)))⁻¹
        * Submission.BoseGases.boxNeumann3 ℓ k x) = 0
  rw [MeasureTheory.integral_const_mul, hint, mul_zero]

end Work.ESYStage
