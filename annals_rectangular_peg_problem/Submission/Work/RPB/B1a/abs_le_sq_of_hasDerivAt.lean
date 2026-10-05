import Mathlib

open Set

namespace Work.RPB.B1a

/-- Mean-value-theorem bound with a linear derivative estimate: if `F 0 = 0` and
`|F' t| ≤ C |t|` on `[-R, R]`, then `|F x| ≤ C x^2` for every `x` with `|x| ≤ R`.

This is the `C * t` growth estimate used when controlling a primitive whose
derivative vanishes to first order at the origin. -/
theorem abs_le_sq_of_hasDerivAt {F F' : ℝ → ℝ} {C R x : ℝ} (hC : 0 ≤ C)
    (hF0 : F 0 = 0) (hd : ∀ t, |t| ≤ R → HasDerivAt F (F' t) t)
    (hb : ∀ t, |t| ≤ R → |F' t| ≤ C * |t|) (hx : |x| ≤ R) :
    |F x| ≤ C * x ^ 2 := by
  rcases le_or_gt 0 x with hx0 | hx0
  · -- Case `0 ≤ x`: apply the mean value theorem on `[0, x]`.
    rcases eq_or_lt_of_le hx0 with rfl | hxpos
    · simp [hF0]
    have hxR : x ≤ R := by rwa [abs_of_nonneg hx0] at hx
    have hmem : ∀ t ∈ Icc (0 : ℝ) x, |t| ≤ R := by
      intro t ht
      rw [abs_of_nonneg ht.1]
      exact le_trans ht.2 hxR
    have hcont : ContinuousOn F (Icc 0 x) := fun t ht =>
      (hd t (hmem t ht)).continuousAt.continuousWithinAt
    have hder : ∀ t ∈ Ioo (0 : ℝ) x, HasDerivAt F (F' t) t := fun t ht =>
      hd t (hmem t ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
    obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope F F' hxpos hcont hder
    simp only [sub_zero, hF0] at hcs
    rw [eq_div_iff (ne_of_gt hxpos)] at hcs
    have hFx : F x = F' c * x := hcs.symm
    have h2 : |F' c| ≤ C * x := by
      have hbc := hb c (hmem c ⟨le_of_lt hc.1, le_of_lt hc.2⟩)
      have hcabs : |c| < x := by rw [abs_of_pos hc.1]; exact hc.2
      calc |F' c| ≤ C * |c| := hbc
        _ ≤ C * x := mul_le_mul_of_nonneg_left (le_of_lt hcabs) hC
    calc |F x| = |F' c| * |x| := by rw [hFx, abs_mul]
      _ = |F' c| * x := by rw [abs_of_nonneg hx0]
      _ ≤ (C * x) * x := mul_le_mul_of_nonneg_right h2 hx0
      _ = C * x ^ 2 := by ring
  · -- Case `x < 0`: apply the mean value theorem on `[x, 0]`.
    have hxR : -x ≤ R := by
      have : |x| = -x := abs_of_neg hx0
      rwa [this] at hx
    have hmem : ∀ t ∈ Icc x 0, |t| ≤ R := by
      intro t ht
      rw [abs_of_nonpos ht.2]
      linarith [ht.1]
    have hcont : ContinuousOn F (Icc x 0) := fun t ht =>
      (hd t (hmem t ht)).continuousAt.continuousWithinAt
    have hder : ∀ t ∈ Ioo x 0, HasDerivAt F (F' t) t := fun t ht =>
      hd t (hmem t ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
    obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope F F' hx0 hcont hder
    have hfx : (F 0 - F x) / (0 - x) = F x / x := by
      rw [hF0, zero_sub, zero_sub, neg_div_neg_eq]
    have hcs' : F' c = F x / x := by rw [hcs, hfx]
    have hFx : F x = F' c * x := by
      rw [hcs', div_mul_cancel₀ (F x) (ne_of_lt hx0)]
    have h2 : |F' c| ≤ C * (-x) := by
      have hbc := hb c (hmem c ⟨le_of_lt hc.1, le_of_lt hc.2⟩)
      have hcabs : |c| < -x := by rw [abs_of_neg hc.2]; linarith [hc.1]
      calc |F' c| ≤ C * |c| := hbc
        _ ≤ C * (-x) := mul_le_mul_of_nonneg_left (le_of_lt hcabs) hC
    calc |F x| = |F' c| * |x| := by rw [hFx, abs_mul]
      _ = |F' c| * (-x) := by rw [abs_of_neg hx0]
      _ ≤ (C * (-x)) * (-x) := mul_le_mul_of_nonneg_right h2 (by linarith)
      _ = C * x ^ 2 := by ring

end Work.RPB.B1a
