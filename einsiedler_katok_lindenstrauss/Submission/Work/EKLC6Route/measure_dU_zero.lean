import Mathlib
import Submission.Work.EKLC6Route.Defs
import Submission.Work.EKLC6Core.measure_eq_zero_of_le_ofReal_min

namespace Work.EKLC6Route

open MeasureTheory Filter Topology
open scoped ENNReal

/-- The set where the displacement `w.dU` vanishes is `μ`-null.  `w.dU z = 0` forces
`z ∈ chartSet t z0 uc θ (2 * r) ρ` (else `w.dU z = w.r > 0`) with `dev (uc z) = w.r`, and for every
`ε > 0` the field `Chart.thin` bounds the measure of `{x ∈ chartSet … (2 * r) ρ | |dev (uc x) - r| ≤ ε}`
by `ENNReal.ofReal (c * ε)`; let `ε → 0`.  No measurability of `w.dU` is needed: `μ` of a
non-measurable set is its outer measure, and `{dU = 0}` is contained in those sets. -/
theorem measure_dU_zero {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] {t : Fin 3 → ℝ} (w : Work.EKLC6Route.Window μ t) :
    μ {z : Work.EKLContract.X3 | w.dU z = 0} = 0 := by
  obtain ⟨c, hc⟩ := w.thin
  -- `{dU = 0}` is contained in every thin slab `{x ∈ chartSet … (2r) ρ | |dev (uc x) - r| ≤ ε}`.
  have hsub : ∀ ε : ℝ, 0 < ε →
      {z : Work.EKLContract.X3 | w.dU z = 0} ⊆
        {x | x ∈ chartSet t w.z0 w.uc w.θ (2 * w.r) w.ρ ∧ |dev (w.uc x) - w.r| ≤ ε} := by
    intro ε hε z hz
    have hz0 : w.dU z = 0 := hz
    by_cases hmem : z ∈ chartSet t w.z0 w.uc w.θ (2 * w.r) w.ρ
    · refine ⟨hmem, ?_⟩
      have hz' : |dev (w.uc z) - w.r| = 0 := by
        have h := hz0
        simp only [Window.dU, hmem] at h
        exact h
      rw [hz']
      exact hε.le
    · have hz' : w.dU z = w.r := by
        simp only [Window.dU, if_neg hmem]
      rw [hz'] at hz0
      exact absurd hz0 w.hr.ne'
  -- hence `μ {dU = 0} ≤ ofReal (c * ε)` for every `ε > 0`; add a nonnegative factor.
  have hbound : ∀ η : ℝ, 0 < η →
      μ {z : Work.EKLContract.X3 | w.dU z = 0} ≤
        ENNReal.ofReal (max c 0 * min 1 (η / 1)) := by
    intro η hη
    have hε : 0 < min 1 η := lt_min one_pos hη
    have hmin : 0 ≤ min 1 η := hε.le
    calc μ {z : Work.EKLContract.X3 | w.dU z = 0}
        ≤ μ {x | x ∈ chartSet t w.z0 w.uc w.θ (2 * w.r) w.ρ ∧
            |dev (w.uc x) - w.r| ≤ min 1 η} :=
          MeasureTheory.measure_mono (hsub (min 1 η) hε)
      _ ≤ ENNReal.ofReal (c * min 1 η) := hc (min 1 η) hε
      _ ≤ ENNReal.ofReal (max c 0 * min 1 (η / 1)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [div_one]
          exact mul_le_mul_of_nonneg_right (le_max_left c 0) hmin
  exact Work.EKLC6Core.measure_eq_zero_of_le_ofReal_min (μ := μ)
    (s := {z : Work.EKLContract.X3 | w.dU z = 0}) one_pos (le_max_right c 0) hbound

end Work.EKLC6Route
