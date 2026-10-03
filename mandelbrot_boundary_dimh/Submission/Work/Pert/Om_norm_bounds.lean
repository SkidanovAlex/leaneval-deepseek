import Mathlib
import Submission.Work.Pert.CoordDefs

/-!
# PERT · `Work.Pert.Om_norm_bounds`

`Om η` is the union of the two closed discs `closedBall (±iη) (13η/40)`.  Any point of either disc
is within `η + 13η/40 = 53η/40` of the origin (triangle inequality) and at distance at least
`η - 13η/40 = 27η/40` from it (reverse triangle inequality).  The requested statement records the
weaker, but sufficient, bounds `13η/40 ≤ ‖ζ‖ ≤ 53η/40`.
-/

namespace Work.Pert

open MandelDim Complex Set Metric

noncomputable section

/-- The norm of the centre `iη` (`η > 0`). -/
private lemma norm_I_mul_ofReal {η : ℝ} : ‖Complex.I * (η : ℂ)‖ = |η| := by
  rw [norm_mul, Complex.norm_I, one_mul]
  simp

/-- Norm bounds for an arbitrary closed ball of radius `13η/40` about a centre of norm `η`. -/
private lemma ball_norm_bounds {η : ℝ} (hη : 0 < η) {c ζ : ℂ} (hc : ‖c‖ = η)
    (h : dist ζ c ≤ 13 * η / 40) :
    13 * η / 40 ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ 53 * η / 40 := by
  rw [dist_eq_norm] at h
  constructor
  · -- reverse triangle inequality: `‖c‖ ≤ ‖ζ‖ + ‖c - ζ‖`
    have hsum : ζ + (c - ζ) = c := by ring
    have h2 : ‖c‖ ≤ ‖ζ‖ + ‖c - ζ‖ := by
      have := norm_add_le ζ (c - ζ)
      rwa [hsum] at this
    have h3 : ‖c - ζ‖ = ‖ζ - c‖ := norm_sub_rev c ζ
    rw [hc, h3] at h2
    linarith
  · -- triangle inequality: `‖ζ‖ ≤ ‖ζ - c‖ + ‖c‖`
    have hsum : (ζ - c) + c = ζ := by ring
    have h2 : ‖ζ‖ ≤ ‖ζ - c‖ + ‖c‖ := by
      have := norm_add_le (ζ - c) c
      rwa [hsum] at this
    rw [hc] at h2
    linarith

theorem Om_norm_bounds {η : ℝ} (hη : 0 < η) :
    ∀ ζ ∈ Work.Pert.Om η, 13 * η / 40 ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ 53 * η / 40 := by
  intro ζ hζ
  rw [Work.Pert.Om, Set.mem_union] at hζ
  have hc : ‖Complex.I * (η : ℂ)‖ = η := by
    rw [norm_I_mul_ofReal, abs_of_pos hη]
  rcases hζ with h | h
  · rw [Metric.mem_closedBall] at h
    exact ball_norm_bounds hη hc h
  · rw [Metric.mem_closedBall] at h
    have hc' : ‖-(Complex.I * (η : ℂ))‖ = η := by rw [norm_neg, hc]
    exact ball_norm_bounds hη hc' h

end

end Work.Pert
