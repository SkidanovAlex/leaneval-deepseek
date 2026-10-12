import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.KinPSuperadd.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.KinPSuperadd

open MeasureTheory

/-- The `N`-particle centred box `abox N s` of any side length `s` is contained
in a compact centred box `abox N R` (`R = max s 1 > 0`). -/
lemma abox_subset_abox_max {N : ℕ} {s : ℝ} :
    Submission.BoseGases.abox N s ⊆ Submission.BoseGases.abox N (max s 1) := by
  intro x hx
  simp only [Submission.BoseGases.abox, Submission.BoseGases.acube, Set.mem_ofPred_eq] at hx ⊢
  intro i m
  have h := hx i m
  rw [Set.mem_Icc] at h ⊢
  have hsR : s ≤ max s 1 := le_max_left s 1
  exact ⟨by linarith [h.1, hsR], by linarith [h.2, hsR]⟩

/-- The square of a continuous function is integrable on the `N`-particle box
`abox N s` (which is contained in a compact centred cube, hence of finite
measure, on which the continuous function is bounded). -/
theorem abox_sq_integrable {N : ℕ} {s : ℝ} {Φ : Submission.BoseGases.X N → ℝ} (hΦ : Continuous Φ) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N => (Φ x) ^ 2)
      (Submission.BoseGases.abox N s) MeasureTheory.volume := by
  have hRpos : 0 < max s 1 := lt_of_lt_of_le zero_lt_one (le_max_right s 1)
  exact (ContinuousOn.integrableOn_compact (Submission.BoseGases.abox_compact N hRpos)
    (hΦ.pow 2).continuousOn).mono_set abox_subset_abox_max

end Work.KinPSuperadd
