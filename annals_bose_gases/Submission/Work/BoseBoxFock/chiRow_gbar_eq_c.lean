import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Q0Sector
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory

namespace Work.BoseBoxFock

/-- If `g = h + c` with `h` continuous and mean-zero over the centred cube `acube ℓ`,
then the (normalised) mean of `g` over `acube ℓ` is exactly `c`. -/
theorem chiRow_gbar_eq_c {ℓ : ℝ} (hℓ : 0 < ℓ) {g h : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hhc : Continuous h) (hmean : (∫ z in Submission.BoseGases.acube ℓ, h z) = 0) {c : ℝ}
    (hg : ∀ z, g z = h z + c) :
    (1 / ℓ ^ 3) * (∫ z in Submission.BoseGases.acube ℓ, g z) = c := by
  have hint : IntegrableOn h (Submission.BoseGases.acube ℓ) volume :=
    Submission.BoseGases.integrableOn_acube_of_continuous hℓ hhc
  have hintc : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin 3) => c)
      (Submission.BoseGases.acube ℓ) volume :=
    Submission.BoseGases.integrableOn_acube_of_continuous hℓ continuous_const
  have hgc : (∫ z in Submission.BoseGases.acube ℓ, g z) = c * ℓ ^ 3 := by
    have hcongr : (∫ z in Submission.BoseGases.acube ℓ, g z)
        = ∫ z in Submission.BoseGases.acube ℓ, (h z + c) := by
      apply integral_congr_ae
      filter_upwards with z
      exact hg z
    rw [hcongr, integral_add hint hintc, hmean, zero_add]
    exact Submission.BoseGases.integral_const_acube ℓ hℓ c
  rw [hgc]
  field_simp

end Work.BoseBoxFock
