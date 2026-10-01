import Mathlib
import Submission.Work.LinnikAreas.BGTZ.GEstimateDefs
import Submission.Work.LinnikAreas.BGTZSetup

open DirichletCharacter Complex
open scoped Classical BigOperators

namespace Work.LinnikAreas.BGTZ

/-- For `Re s = 1/2` the modulus of `p^{-s}` is at most `1/√p` (equality for `p > 0`). -/
lemma norm_cpow_neg_half_le (p : ℕ) (s : ℂ) (hs : s.re = 1 / 2) :
    ‖(p : ℂ) ^ (-s)‖ ≤ 1 / Real.sqrt (p : ℝ) := by
  rcases Nat.eq_zero_or_pos p with hp0 | hp
  · subst hp0
    push_cast
    rw [zero_cpow]
    · simp
    · intro h
      have hzero : s = 0 := neg_eq_zero.mp h
      rw [hzero] at hs
      norm_num at hs
  · rw [show (p : ℂ) = ((p : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hp)]
    have hre : (-s).re = -(1 / 2) := by rw [Complex.neg_re, hs]
    rw [hre, Real.rpow_neg (show (0:ℝ) ≤ (p:ℝ) by positivity) (1/2 : ℝ)]
    rw [Real.sqrt_eq_rpow, inv_eq_one_div]

/-- For `Re s = 1/2` the modulus of `p^{-2s}` is at most `1/p` (equality for `p > 0`). -/
lemma norm_cpow_neg_two_le (p : ℕ) (s : ℂ) (hs : s.re = 1 / 2) :
    ‖(p : ℂ) ^ (-(2 * s))‖ ≤ 1 / (p : ℝ) := by
  rcases Nat.eq_zero_or_pos p with hp0 | hp
  · subst hp0
    push_cast
    rw [zero_cpow]
    · simp
    · intro h
      have h2 : 2 * s = 0 := neg_eq_zero.mp h
      have hzero : s = 0 := by simpa using h2
      rw [hzero] at hs
      norm_num at hs
  · rw [show (p : ℂ) = ((p : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hp)]
    have hre : (-(2 * s)).re = -(1:ℝ) := by
      rw [Complex.neg_re, Complex.mul_re]
      simp [hs]
    rw [hre, Real.rpow_neg_one, inv_eq_one_div]

theorem SieveLocalBound {q : ℕ} [NeZero q] (χ₁ χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : s.re = 1 / 2) (p : ℕ) :
    ‖Work.LinnikAreas.BGTZ.sieveLocal χ₁ χ s p‖ ≤ Work.LinnikAreas.BGTZ.gwt χ₁ p := by
  have ha_ge : -1 ≤ (χ₁ p).re := neg_one_le_re_apply χ₁ p
  have ha_le : (χ₁ p).re ≤ 1 := re_apply_le_one χ₁ p
  have hsieve : sieveLocal χ₁ χ s p
      = (((1 + (χ₁ p).re : ℝ)) : ℂ) * (χ p) * (p : ℂ) ^ (-s)
        - (((χ₁ p).re : ℝ) : ℂ) * (χ p) ^ 2 * (p : ℂ) ^ (-(2 * s)) := by
    simp only [sieveLocal]
    push_cast
    ring
  rw [hsieve, gwt]
  have habs1 : |1 + (χ₁ p).re| = 1 + (χ₁ p).re := abs_of_nonneg (by linarith)
  have hA : ‖(((1 + (χ₁ p).re : ℝ)) : ℂ) * (χ p) * (p : ℂ) ^ (-s)‖
      ≤ (1 + (χ₁ p).re) * (1 / Real.sqrt (p : ℝ)) := by
    simp only [norm_mul, norm_real, Real.norm_eq_abs, habs1]
    have hχ : ‖χ p‖ ≤ 1 := norm_le_one χ p
    have hs' : ‖(p : ℂ) ^ (-s)‖ ≤ 1 / Real.sqrt (p : ℝ) := norm_cpow_neg_half_le p s hs
    have h1 : ‖χ p‖ * ‖(p : ℂ) ^ (-s)‖ ≤ 1 * (1 / Real.sqrt (p : ℝ)) :=
      mul_le_mul hχ hs' (norm_nonneg _) (by positivity)
    have h2 : (0:ℝ) ≤ 1 + (χ₁ p).re := by linarith
    nlinarith [h1, h2]
  have hB : ‖(((χ₁ p).re : ℝ) : ℂ) * (χ p) ^ 2 * (p : ℂ) ^ (-(2 * s))‖
      ≤ 1 * (1 / (p : ℝ)) := by
    simp only [norm_mul, norm_pow, norm_real, Real.norm_eq_abs]
    have hχ2 : ‖χ p‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) (norm_le_one χ p)
    have habs : |(χ₁ p).re| ≤ 1 := abs_le.mpr ⟨ha_ge, ha_le⟩
    have h1 : |(χ₁ p).re| * ‖χ p‖ ^ 2 ≤ 1 := by
      have := mul_le_mul habs hχ2 (by positivity) (by norm_num)
      simpa using this
    have hs2 : ‖(p : ℂ) ^ (-(2 * s))‖ ≤ 1 / (p : ℝ) := norm_cpow_neg_two_le p s hs
    nlinarith [h1, hs2, norm_nonneg ((p : ℂ) ^ (-(2 * s)))]
  calc ‖(((1 + (χ₁ p).re : ℝ)) : ℂ) * (χ p) * (p : ℂ) ^ (-s)
          - (((χ₁ p).re : ℝ) : ℂ) * (χ p) ^ 2 * (p : ℂ) ^ (-(2 * s))‖
      ≤ ‖(((1 + (χ₁ p).re : ℝ)) : ℂ) * (χ p) * (p : ℂ) ^ (-s)‖
        + ‖(((χ₁ p).re : ℝ) : ℂ) * (χ p) ^ 2 * (p : ℂ) ^ (-(2 * s))‖ := norm_sub_le _ _
    _ ≤ (1 + (χ₁ p).re) * (1 / Real.sqrt (p : ℝ)) + 1 * (1 / (p : ℝ)) := add_le_add hA hB
    _ = (1 + (χ₁ p).re) / Real.sqrt (p : ℝ) + 1 / (p : ℝ) := by ring

end Work.LinnikAreas.BGTZ
