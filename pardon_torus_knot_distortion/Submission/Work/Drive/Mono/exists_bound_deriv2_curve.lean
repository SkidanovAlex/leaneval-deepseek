import Mathlib
import Submission.Work.Drive.Mono.ae_exists_goodV
import Submission.Work.Drive.Mono.NoBend

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion in
/-- The derivative of a periodic function is periodic (with the same period). -/
theorem periodic_deriv_of_periodic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {T : ℝ} (hper : Function.Periodic f T) : Function.Periodic (deriv f) T := by
  intro x
  rw [← deriv_comp_add_const f T x, funext hper]

open LeanEval.KnotTheory.PardonDistortion in
/-- The second derivative of a knot is `2π`-periodic. -/
theorem periodic_deriv2_curve (K : Knot) :
    Function.Periodic (deriv (deriv K.curve)) (2 * Real.pi) :=
  periodic_deriv_of_periodic (periodic_deriv_curve K)

open LeanEval.KnotTheory.PardonDistortion in
/-- The acceleration of a periodic knot is bounded (periodicity + continuity on one period +
compactness, as for `Work.Drive.Mono.exists_bound_deriv_curve`). -/
theorem exists_bound_deriv2_curve (K : Knot) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖deriv (deriv K.curve) t‖ ≤ C := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hper : Function.Periodic (deriv (deriv K.curve)) (2 * Real.pi) := periodic_deriv2_curve K
  have hcd : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) K.curve := K.smooth.of_le (by decide)
  have hcont : Continuous (deriv (deriv K.curve)) := by
    have h := ContDiff.iterate_deriv' (n := 0) (k := 2) hcd
    simpa using h.continuous
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max 1 C, le_trans zero_le_one (le_max_left _ _), fun t => ?_⟩
  obtain ⟨s, hs, hds⟩ := hper.exists_mem_Ico₀ hpi t
  rw [hds]
  exact le_trans (hC s (Set.Ico_subset_Icc_self hs)) (le_max_right _ _)

end Work.Drive.Mono
