import Mathlib

namespace Work.CRad

/-- Key identity: for `1 ≤ A`, `A + √(A²-1)` is its own reciprocal counterpart, i.e.
`(A + √(A²-1)) + (A + √(A²-1))⁻¹ = 2A` (since `(A+√(A²-1))(A-√(A²-1)) = 1`). -/
theorem alphaF_inv_identity {A : ℝ} (hA : 1 ≤ A) :
    (A + Real.sqrt (A ^ 2 - 1)) + (A + Real.sqrt (A ^ 2 - 1))⁻¹ = 2 * A := by
  have hA2 : (0:ℝ) ≤ A ^ 2 - 1 := by nlinarith [sq_nonneg (A - 1), hA]
  have hsqA : Real.sqrt (A ^ 2 - 1) ^ 2 = A ^ 2 - 1 := Real.sq_sqrt hA2
  have hmul : (A + Real.sqrt (A ^ 2 - 1)) * (A - Real.sqrt (A ^ 2 - 1)) = 1 := by
    nlinarith [hsqA]
  have hinv : (A + Real.sqrt (A ^ 2 - 1))⁻¹ = A - Real.sqrt (A ^ 2 - 1) :=
    inv_eq_of_mul_eq_one_right hmul
  rw [hinv]; ring

theorem alphaF_ratio_step {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B)
    (h : 2 * A ≤ (1001 / 1000 : ℝ) * (2 * B - 1)) :
    A + Real.sqrt (A ^ 2 - 1) ≤ (1001 / 1000 : ℝ) * (B + Real.sqrt (B ^ 2 - 1)) := by
  set s : ℝ := A + Real.sqrt (A ^ 2 - 1) with hs
  set t : ℝ := B + Real.sqrt (B ^ 2 - 1) with ht
  have hs_inv : s + s⁻¹ = 2 * A := by
    rw [hs]; exact alphaF_inv_identity hA
  have ht_inv : t + t⁻¹ = 2 * B := by
    rw [ht]; exact alphaF_inv_identity hB
  have hs1 : 1 ≤ s := by
    rw [hs]
    have : 0 ≤ Real.sqrt (A ^ 2 - 1) := Real.sqrt_nonneg _
    linarith
  have ht1 : 1 ≤ t := by
    rw [ht]
    have : 0 ≤ Real.sqrt (B ^ 2 - 1) := Real.sqrt_nonneg _
    linarith
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  -- the hypothesis in terms of `s`, `t`
  have hyp : s + s⁻¹ ≤ (1001 / 1000 : ℝ) * (t + t⁻¹ - 1) := by
    have h' := h
    rw [← hs_inv, ← ht_inv] at h'
    exact h'
  -- suppose the contrary, `(1001/1000)·t < s`
  by_contra hcon
  rw [not_le] at hcon
  have hE : s + s⁻¹ - (1001 / 1000 : ℝ) * (t + t⁻¹ - 1) ≤ 0 := by linarith
  have hpos1 : 0 < s - (1001 / 1000 : ℝ) * t := by linarith
  have hpos2 : 0 < s⁻¹ := inv_pos.mpr hs0
  have htinv_le : t⁻¹ ≤ 1 := by
    have := (inv_le_inv₀ ht0 (by norm_num : (0:ℝ) < 1)).mpr ht1
    simpa using this
  have hpos3 : (0:ℝ) ≤ 1 - t⁻¹ := by linarith
  have hcontr :
      0 < (s - (1001 / 1000 : ℝ) * t) + s⁻¹ + (1001 / 1000 : ℝ) * (1 - t⁻¹) := by
    have hc : (0:ℝ) ≤ 1001 / 1000 := by norm_num
    have := mul_nonneg hc hpos3
    linarith
  have heq : s + s⁻¹ - (1001 / 1000 : ℝ) * (t + t⁻¹ - 1)
      = (s - (1001 / 1000 : ℝ) * t) + s⁻¹ + (1001 / 1000 : ℝ) * (1 - t⁻¹) := by
    ring
  linarith [heq]

end Work.CRad
