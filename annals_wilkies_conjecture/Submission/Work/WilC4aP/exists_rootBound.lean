import Mathlib
import Submission.Work.WilC4aP.SqDefs
import Submission.Work.WilC4aP.poly_root_bound

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
open scoped BigOperators

namespace Work.WilC4aP

open Polynomial

/-- Uniform Cauchy root bound for the fibres of `P` over the closed disk of radius `r`: there is
`R > 0` such that every root of every fibre `Pz P z` with `‖z‖ ≤ r` satisfies `‖α‖ ≤ R`. -/
theorem exists_rootBound (P : Polynomial (ℂ → ℂ)) (hmon : P.Monic) {r : ℝ}
    (hcont : ∀ z : ℂ, ‖z‖ ≤ r → Work.WilC4aP.HolCoeffs P z) :
    ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, ‖z‖ ≤ r → ∀ α : ℂ, (Work.WilC4aP.Pz P z).eval α = 0 →
      ‖α‖ ≤ R := by
  -- Each coefficient function is continuous on the closed disk, hence bounded there.
  have hbdd : ∀ i : ℕ, ∃ C : ℝ, ∀ z : ℂ, ‖z‖ ≤ r → ‖P.coeff i z‖ ≤ C := by
    intro i
    have hcontOn : ContinuousOn (P.coeff i) (Metric.closedBall (0 : ℂ) r) := by
      intro z hz
      exact ((hcont z (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz) i).continuousAt)
        |>.continuousWithinAt
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) r).exists_bound_of_continuousOn hcontOn
    exact ⟨C, fun z hz => hC z (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz)⟩
  choose C hC using hbdd
  refine ⟨max 1 (∑ i ∈ Finset.range P.natDegree, C i), lt_max_iff.mpr (Or.inl one_pos), ?_⟩
  intro z hz α hα
  have hdeg : (Pz P z).natDegree = P.natDegree := natDegree_Pz hmon z
  have hbound := poly_root_bound (monic_Pz hmon z) hα
  rw [hdeg] at hbound
  refine le_trans hbound (max_le_max_left 1 ?_)
  apply Finset.sum_le_sum
  intro i _
  rw [Pz, Polynomial.coeff_map, evAt_apply]
  exact hC i z hz

end Work.WilC4aP
