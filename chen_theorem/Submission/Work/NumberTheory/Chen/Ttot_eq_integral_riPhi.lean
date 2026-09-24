import Mathlib
import Submission.Work.NumberTheory.Chen.APSwitchUpper.prof
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhiDelay
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhiLevelCore
import Submission.Work.NumberTheory.Chen.ApSumTenth.riPhi_delay_system

namespace Work.NumberTheory.Chen

open MeasureTheory
open Filter
open scoped BigOperators

/-- **`∫_3^∞ riPhi = Ttot`.**  The series dominated convergence theorem applied to the even
profiles `j ↦ profC (2j)` over `[3,∞)`: each is integrable there (`riSys_integrableOn_profC_Ici`)
and its half-line integral is the level mass `Q j = ∫_3^{2j+3} profC (2j)`
(`riSys_integral_Ici_profC`, the profile being supported in `(-∞, 2j+3]`).  The level masses are
summable with sum `Ttot` (`hasSum_Q`), so `HasSum.unique` identifies the integral of the series
`riPhi = Σ_j profC (2j)` with `Ttot`. -/
theorem Ttot_eq_integral_riPhi : (∫ u in Set.Ici (3:ℝ), Work.NumberTheory.Chen.APSwitchUpper.riPhi u) = Work.NumberTheory.Chen.APSwitchUpper.Ttot := by
  have hInt : ∀ j : ℕ, Integrable (fun u : ℝ => Work.NumberTheory.Chen.APSwitchUpper.profC (2 * j) u)
      (volume.restrict (Set.Ici (3 : ℝ))) :=
    fun j => ApSumTenth.riSys_integrableOn_profC_Ici (2 * j) 3
  have hQ : ∀ j : ℕ,
      (∫ u in Set.Ici (3 : ℝ), Work.NumberTheory.Chen.APSwitchUpper.profC (2 * j) u)
        = Work.NumberTheory.Chen.APSwitchUpper.Q j := by
    intro j
    rw [ApSumTenth.riSys_integral_Ici_profC, Work.NumberTheory.Chen.APSwitchUpper.Q]
    have hc : ((2 * j : ℕ) : ℝ) + 3 = ((2 * j + 3 : ℕ) : ℝ) := by push_cast; ring
    rw [hc]
  have hnorm : (fun j : ℕ =>
        ∫ u in Set.Ici (3 : ℝ), ‖Work.NumberTheory.Chen.APSwitchUpper.profC (2 * j) u‖)
      = fun j : ℕ => ∫ u in Set.Ici (3 : ℝ), Work.NumberTheory.Chen.APSwitchUpper.profC (2 * j) u := by
    funext j
    refine integral_congr_ae (Eventually.of_forall ?_)
    intro u
    exact Real.norm_of_nonneg (Work.NumberTheory.Chen.APSwitchUpper.profC_nonneg (2 * j) u)
  have hsumm : Summable (fun j : ℕ =>
      ∫ u in Set.Ici (3 : ℝ), ‖Work.NumberTheory.Chen.APSwitchUpper.profC (2 * j) u‖) := by
    rw [hnorm]
    rw [show (fun j : ℕ => ∫ u in Set.Ici (3 : ℝ),
          Work.NumberTheory.Chen.APSwitchUpper.profC (2 * j) u)
        = Work.NumberTheory.Chen.APSwitchUpper.Q from funext hQ]
    exact Work.NumberTheory.Chen.APSwitchUpper.summable_Q
  have hmain := hasSum_integral_of_summable_integral_norm
    (F := fun j : ℕ => fun u : ℝ => Work.NumberTheory.Chen.APSwitchUpper.profC (2 * j) u)
    (μ := volume.restrict (Set.Ici (3 : ℝ))) hInt hsumm
  exact HasSum.unique (hmain.congr_fun (fun j => (hQ j).symm))
    Work.NumberTheory.Chen.APSwitchUpper.hasSum_Q

end Work.NumberTheory.Chen
