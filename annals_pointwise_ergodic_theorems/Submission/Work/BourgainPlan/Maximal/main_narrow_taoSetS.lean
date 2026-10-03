import Mathlib
import Submission.Work.BourgainPlan.Maximal.iw_superset
import Submission.Work.BourgainPlan.Maximal.exists_flat_bump_uniform
import Submission.Work.BourgainPlan.Maximal.ellp_interpolation
import Submission.Work.BourgainPlan.IonescuWainger.petal_smallness_of_good
import Submission.Work.BourgainPlan.IonescuWainger.erdos_rado_sunflower
import Submission.Work.BourgainPlan.Maximal.hstep3_msw_uniform
import Submission.Work.IonescuWainger.ortho_apply_lower_strata_system_ennreal_uniform
import Submission.Work.IonescuWainger.ortho_apply_upper_pow

namespace Work.BourgainPlan.Maximal

open MeasureTheory ENNReal Finset
open scoped ENNReal BigOperators
open Work.BourgainPlan.IonescuWainger

noncomputable section

/-- The `q`-th power of the `eLpNorm` against the counting measure on `ℤ` is the `ℓ^q`-sum of the
`q`-th powers (i.e. the `q`-th power of the `L^q` norm is the `L^q` "integral"). -/
lemma eLpNorm_count_rpow_eq_tsum' (X : ℤ → ℂ) {q : ℝ} (hq : 0 < q) :
    (eLpNorm X (ENNReal.ofReal q) Measure.count) ^ q
      = ∑' n : ℤ, ENNReal.ofReal (‖X n‖ ^ q) := by
  rw [eLpNorm_count_eq_tsum X hq, ← ENNReal.rpow_mul, one_div_mul_cancel (ne_of_gt hq),
    ENNReal.rpow_one]

/-- The `q`-th power of the `L^q`-norm against the counting measure, written as a `lintegral`
of the `q`-th power of the extended norm. -/
lemma lintegral_enorm_rpow_eq_eLpNorm_rpow (X : ℤ → ℂ) {q : ℝ} (hq : 0 < q) :
    ∫⁻ n : ℤ, ‖X n‖ₑ ^ q ∂Measure.count
      = (eLpNorm X (ENNReal.ofReal q) Measure.count) ^ q := by
  rw [MeasureTheory.lintegral_count, eLpNorm_count_rpow_eq_tsum' X hq]
  exact tsum_congr (fun n => by
    rw [show ‖X n‖ₑ = ENNReal.ofReal ‖X n‖ by simp [enorm_eq_nnnorm],
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq.le])


end

end Work.BourgainPlan.Maximal
