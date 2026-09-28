import Mathlib
import Submission.Work.Thom.CapGeomDefs

namespace Work.Thom.CapScale

/-- The scaling `Φ_λ` with `λ ∈ [0,1]` never moves a point of the unit sphere across the
equator: it preserves the sign of `lastC` and does not increase its absolute value.  Concretely,
if `lastC v ≥ 0` then `0 ≤ lastC (Φ_λ v) ≤ lastC v`, and if `lastC v ≤ 0` then
`lastC v ≤ lastC (Φ_λ v) ≤ 0`. -/
theorem lastC_scalePt_bounds (n : ℕ) (lam : ℝ) (v : MSph (n + 1)) (h : scaleV n lam v.1 ≠ 0)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    (0 ≤ lastC n v.1 → 0 ≤ lastC n (scalePt n lam v h).1 ∧
      lastC n (scalePt n lam v h).1 ≤ lastC n v.1) ∧
    (lastC n v.1 ≤ 0 → lastC n v.1 ≤ lastC n (scalePt n lam v h).1 ∧
      lastC n (scalePt n lam v h).1 ≤ 0) := by
  have hNpos : 0 < ‖scaleV n lam v.1‖ := norm_pos_iff.mpr h
  have ht2 : (lastC n v.1) ^ 2 ≤ 1 := by
    nlinarith [abs_lastC_le_one n v, abs_nonneg (lastC n v.1), sq_abs (lastC n v.1)]
  -- The normalisation factor is at least `lam`, since `‖scaleV n lam v‖ ^ 2 - lam ^ 2
  -- = (1 - lam ^ 2) (1 - (lastC v) ^ 2) ≥ 0`.
  have hNlam : lam ≤ ‖scaleV n lam v.1‖ := by
    have hsq := norm_scaleV_sq_of_unit n lam v
    have hfac : 0 ≤ (1 - lam ^ 2) * (1 - (lastC n v.1) ^ 2) := by
      apply mul_nonneg <;> nlinarith [ht2, h0, h1]
    have hkey : lam ^ 2 ≤ ‖scaleV n lam v.1‖ ^ 2 := by
      rw [hsq]; nlinarith [hfac]
    have h2 : |lam| ≤ |‖scaleV n lam v.1‖| := by
      rw [← sq_le_sq]; exact hkey
    rwa [abs_of_nonneg h0, abs_of_nonneg (norm_nonneg _)] at h2
  constructor
  · intro ht
    have hval := lastC_scalePt n lam v h
    constructor
    · rw [hval]; exact div_nonneg (mul_nonneg h0 ht) hNpos.le
    · rw [hval, div_le_iff₀ hNpos]
      nlinarith [mul_le_mul_of_nonneg_right hNlam ht]
  · intro ht
    have hval := lastC_scalePt n lam v h
    constructor
    · rw [hval, le_div_iff₀ hNpos]
      nlinarith [mul_le_mul_of_nonpos_left hNlam ht]
    · rw [hval]
      exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos h0 ht) hNpos.le

end Work.Thom.CapScale
