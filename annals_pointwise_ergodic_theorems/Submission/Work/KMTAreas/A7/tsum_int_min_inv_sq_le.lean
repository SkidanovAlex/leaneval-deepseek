import Mathlib
import Submission.Work.KMTAreas.A7.tsum_one_div_one_add_sq_mul_le

namespace Work.KMTAreas.A7

open scoped BigOperators

/-- Elementary pointwise comparison: for `x ≠ 0` the clipped reciprocal square is at most twice
the standard Cauchy kernel `1/(1+x²)`.  (For `x² ≤ 1` the left side is at most `1 ≤ 2/(1+x²)`,
and for `x² ≥ 1` it is at most `1/x² ≤ 2/(1+x²)`.) -/
private lemma min_one_inv_sq_le_two_div (x : ℝ) (hx : x ≠ 0) :
    min 1 (1 / x ^ 2) ≤ 2 / (1 + x ^ 2) := by
  have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  rcases le_or_gt (x ^ 2) 1 with h | h
  · have h1 : (1 : ℝ) ≤ 2 / (1 + x ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    exact le_trans (min_le_left _ _) h1
  · have h1 : 1 / x ^ 2 ≤ 2 / (1 + x ^ 2) := by
      rw [div_le_div_iff₀ hx2 (by positivity)]
      nlinarith
    exact le_trans (min_le_right _ _) h1

/-- The bilinear averaging argument produces the `ℤ`-lattice sum of the clipped reciprocal
squares `min 1 (2πw p)^{-2}`; this is at most `3 + 1/w` for every `w > 0`.  The bound is
elementary: the clipped square is dominated pointwise by twice the Cauchy kernel
`1/(1+(2πw p)²)`, whose lattice sum is controlled by `tsum_one_div_one_add_sq_mul_le`. -/
theorem tsum_int_min_inv_sq_le (w : ℝ) (hw : 0 < w) :
    (∑' p : ℤ, (if p = 0 then 1 else min 1 (1 / (2 * Real.pi * w * (p : ℝ)) ^ 2))) ≤ 3 + 1 / w := by
  set s : ℝ := 2 * Real.pi * w with hs
  have hs0 : 0 < s := by rw [hs]; positivity
  have hsne : s ≠ 0 := ne_of_gt hs0
  obtain ⟨hsumm, hbound⟩ := tsum_one_div_one_add_sq_mul_le s hs0 0
  -- the lattice family `1/(1+(s p)²)` and the lattice-sum bound
  have hS : Summable (fun p : ℤ => 1 / (1 + (s * (p : ℝ)) ^ 2)) := by simpa using hsumm
  have hB : (∑' p : ℤ, 1 / (1 + (s * (p : ℝ)) ^ 2)) ≤ 2 + Real.pi / s := by simpa using hbound
  -- the summand of the goal, with the factor `2 * π * w` named `s`
  have hgoal : (∑' p : ℤ, (if p = 0 then 1 else min 1 (1 / (2 * Real.pi * w * (p : ℝ)) ^ 2)))
      = ∑' p : ℤ, (if p = 0 then 1 else min 1 (1 / (s * (p : ℝ)) ^ 2)) := by
    refine tsum_congr (fun p => ?_)
    by_cases hp : p = 0
    · simp only [if_pos hp]
    · simp only [if_neg hp]
      have hc : 2 * Real.pi * w * (p : ℝ) = s * (p : ℝ) := by rw [hs]
      rw [hc]
  -- pointwise domination by `2/(1+(s p)²)`
  have hpt : ∀ p : ℤ, (if p = 0 then 1 else min 1 (1 / (s * (p : ℝ)) ^ 2))
      ≤ (if p = 0 then 1 else 2 / (1 + (s * (p : ℝ)) ^ 2)) := by
    intro p
    by_cases hp : p = 0
    · simp only [if_pos hp]; exact le_rfl
    · simp only [if_neg hp]
      exact min_one_inv_sq_le_two_div _ (mul_ne_zero hsne (Int.cast_ne_zero.mpr hp))
  -- the dominating family is summable, being dominated by `2 * 1/(1+(s p)²)`
  have hGsum : Summable (fun p : ℤ => (if p = 0 then 1 else 2 / (1 + (s * (p : ℝ)) ^ 2))) := by
    refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) (hS.mul_left 2)
    · by_cases hp : p = 0
      · simp [hp]
      · simp only [if_neg hp]; positivity
    · by_cases hp : p = 0
      · simp [hp]
      · simp only [if_neg hp]
        exact le_of_eq (by ring)
  have hFsum : Summable (fun p : ℤ => (if p = 0 then 1 else min 1 (1 / (s * (p : ℝ)) ^ 2))) :=
    Summable.of_nonneg_of_le (fun p => by
      by_cases hp : p = 0
      · simp only [if_pos hp]; exact zero_le_one
      · simp only [if_neg hp]
        exact le_min (by norm_num) (div_nonneg zero_le_one (sq_nonneg _))) hpt hGsum

  -- split off the `p = 0` term of the dominating family
  have hsplit := hGsum.tsum_eq_add_tsum_ite (0 : ℤ)
  have htail : (∑' p : ℤ, (if p = 0 then 0 else (if p = 0 then 1 else 2 / (1 + (s * (p : ℝ)) ^ 2))))
      = 2 * ∑' p : ℤ, (if p = 0 then 0 else 1 / (1 + (s * (p : ℝ)) ^ 2)) := by
    rw [← tsum_mul_left]
    refine tsum_congr (fun p => ?_)
    by_cases hp : p = 0
    · simp only [if_pos hp]; norm_num
    · simp only [if_neg hp]; ring
  -- split off the `p = 0` term of the lattice family, then use the lattice bound
  have htailA : (∑' p : ℤ, (if p = 0 then 0 else 1 / (1 + (s * (p : ℝ)) ^ 2)))
      ≤ 1 + Real.pi / s := by
    have hA0 : (1 : ℝ) / (1 + (s * ((0 : ℤ) : ℝ)) ^ 2) = 1 := by norm_num
    have h := hS.tsum_eq_add_tsum_ite (0 : ℤ)
    rw [hA0] at h
    linarith

  rw [hgoal]
  calc (∑' p : ℤ, (if p = 0 then 1 else min 1 (1 / (s * (p : ℝ)) ^ 2)))
      ≤ ∑' p : ℤ, (if p = 0 then 1 else 2 / (1 + (s * (p : ℝ)) ^ 2)) :=
        Summable.tsum_le_tsum hpt hFsum hGsum
    _ = 1 + 2 * ∑' p : ℤ, (if p = 0 then 0 else 1 / (1 + (s * (p : ℝ)) ^ 2)) := by
        rw [hsplit, htail]
        norm_num
    _ ≤ 1 + 2 * (1 + Real.pi / s) := by linarith
    _ = 3 + 1 / w := by
        rw [hs]
        field_simp
        ring

end Work.KMTAreas.A7
