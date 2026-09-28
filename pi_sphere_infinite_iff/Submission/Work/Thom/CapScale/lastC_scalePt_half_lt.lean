import Mathlib
import Submission.Work.Thom.CapGeomDefs

namespace Work.Thom.CapScale

/-- The scaling map `Φ_{1/2}` strictly decreases the last coordinate of a point of the closed cap
`{0 ≤ lastC ≤ 1/2}`: it maps that cap into the open cap `{lastC < 1/2}`.

Indeed `lastC (Φ_{1/2} v) = (lastC v / 2) / ‖scaleV (1/2) v‖`, and
`‖scaleV (1/2) v‖² = 1 - 3/4 · (lastC v)² ≥ 13/16 > 1/4 ≥ (lastC v)²`, so
`lastC v < ‖scaleV (1/2) v‖`, which gives the claim. -/
theorem lastC_scalePt_half_lt (n : ℕ) (v : MSph (n + 1)) (h : scaleV n (1 / 2) v.1 ≠ 0)
    (ht0 : 0 ≤ lastC n v.1) (ht1 : lastC n v.1 ≤ 1 / 2) :
    lastC n (scalePt n (1 / 2) v h).1 < 1 / 2 := by
  have hpos : 0 < ‖scaleV n (1 / 2) v.1‖ := norm_pos_iff.mpr h
  -- the squared norm of the scaled vector
  have hnorm : ‖scaleV n (1 / 2) v.1‖ ^ 2 = 1 - 3 / 4 * (lastC n v.1) ^ 2 := by
    have := norm_scaleV_sq_of_unit n (1 / 2) v
    nlinarith [this]
  have hcsq : (lastC n v.1) ^ 2 ≤ 1 / 4 := by nlinarith [ht0, ht1]
  -- hence `lastC v < ‖scaleV (1/2) v‖`
  have hlt : lastC n v.1 < ‖scaleV n (1 / 2) v.1‖ := by
    have key : (lastC n v.1) ^ 2 < ‖scaleV n (1 / 2) v.1‖ ^ 2 := by
      nlinarith [hnorm, hcsq]
    have h2 := sq_lt_sq.mp key
    rwa [abs_of_nonneg ht0, abs_of_nonneg (norm_nonneg _)] at h2
  rw [lastC_scalePt]
  rw [div_lt_iff₀ hpos]
  nlinarith [hlt]

end Work.Thom.CapScale
