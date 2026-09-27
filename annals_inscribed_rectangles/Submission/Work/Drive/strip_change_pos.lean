import Mathlib

namespace Work.Drive

/-- If `Circle.exp t = 1` then `t` is an integer multiple of `2π`. -/
lemma exp_eq_one_real {t : ℝ} (h : Circle.exp t = 1) :
    ∃ n : ℤ, t = (n : ℝ) * (2 * Real.pi) := by
  have h1 : Complex.exp ((t : ℂ) * Complex.I) = 1 := by
    have hh := Circle.coe_exp t
    rw [h] at hh
    rw [← hh]
    simp
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
  exact ⟨n, Complex.ofReal_injective
    (mul_right_cancel₀ Complex.I_ne_zero (by rw [hn]; push_cast; ring))⟩

/-- If `Circle.exp t = -1` then `t = π + 2πk` for some integer `k`. -/
lemma exp_eq_neg_one_real {t : ℝ} (h : Circle.exp t = -1) :
    ∃ n : ℤ, t = Real.pi + (n : ℝ) * (2 * Real.pi) := by
  have h1 : Complex.exp ((t : ℂ) * Complex.I) = -1 := by
    have hh := Circle.coe_exp t
    rw [h] at hh
    rw [← hh]
    simp
  have h3 : Complex.exp ((t : ℂ) * Complex.I) = Complex.exp ((Real.pi : ℂ) * Complex.I) := by
    rw [h1, Complex.exp_pi_mul_I]
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h3
  exact ⟨n, Complex.ofReal_injective
    (mul_right_cancel₀ Complex.I_ne_zero (by rw [hn]; push_cast; ring))⟩

/-- The sine of `3π/2 + 2πk` is `-1`. -/
lemma sin_three_pi_div_two_add_int_mul_two_pi (k : ℤ) :
    Real.sin (3 * Real.pi / 2 + (k : ℝ) * (2 * Real.pi)) = -1 := by
  rw [Real.sin_eq_neg_one_iff]
  refine ⟨k + 1, ?_⟩
  push_cast
  ring

/-- Angle change of a continuous lift of a path in the circle that stays in the closed upper half
plane, from the direction `1` to the direction `-1`.

Proof idea: `{x | 0 ≤ sin x}` is the disjoint union of the closed intervals
`[2πk, π+2πk]`. The image `g '' (Icc a b)` is connected, hence lies in a single one of these
intervals, say `[2πk, π+2πk]`. Since `Circle.exp (g a) = 1` forces `g a ∈ 2πℤ`
(`Complex.exp_eq_one_iff`), we get `g a = 2πk`; since `Circle.exp (g b) = -1` forces
`g b ≡ π (mod 2π)` (`Complex.exp_eq_exp_iff_exists_int`), we get `g b = π + 2πk`. -/
theorem strip_change_pos {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : ContinuousOn g (Set.Icc a b)) (hsin : ∀ t ∈ Set.Icc a b, 0 ≤ Real.sin (g t))
    (ha : Circle.exp (g a) = 1) (hb : Circle.exp (g b) = -1) :
    g b - g a = Real.pi := by
  obtain ⟨n, hn⟩ := exp_eq_one_real ha
  obtain ⟨m, hm⟩ := exp_eq_neg_one_real hb
  -- The intermediate value theorem for `g` on the interval `[a, b]`.
  have hsurj := hg.surjOn_uIcc (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab)
  -- `g a` and `g b` lie in the same interval `[2πk, π + 2πk]`, i.e. `n = m`.
  have hmn : m = n := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- `m < n`: then `g b < g a`, and the bad point `3π/2 + 2πm` lies between them.
      have hnm : (m : ℝ) + 1 ≤ (n : ℝ) := by
        exact_mod_cast (show m + 1 ≤ n by omega)
      have hdc : g b < g a := by
        rw [hn, hm]; nlinarith [Real.pi_pos]
      have hy : (3 * Real.pi / 2 + (m : ℝ) * (2 * Real.pi)) ∈ Set.uIcc (g a) (g b) := by
        rw [Set.uIcc_of_ge hdc.le]
        constructor
        · rw [hm]; nlinarith [Real.pi_pos]
        · rw [hn]; nlinarith [Real.pi_pos]
      obtain ⟨t, ht, hgt'⟩ := hsurj hy
      have := hsin t ht
      rw [hgt', sin_three_pi_div_two_add_int_mul_two_pi m] at this
      norm_num at this
    · -- `n < m`: then `g a < g b`, and the bad point `3π/2 + 2πn` lies between them.
      have hnm : (n : ℝ) + 1 ≤ (m : ℝ) := by
        exact_mod_cast (show n + 1 ≤ m by omega)
      have hcd : g a < g b := by
        rw [hn, hm]; nlinarith [Real.pi_pos]
      have hy : (3 * Real.pi / 2 + (n : ℝ) * (2 * Real.pi)) ∈ Set.uIcc (g a) (g b) := by
        rw [Set.uIcc_of_le hcd.le]
        constructor
        · rw [hn]; nlinarith [Real.pi_pos]
        · rw [hm]; nlinarith [Real.pi_pos]
      obtain ⟨t, ht, hgt'⟩ := hsurj hy
      have := hsin t ht
      rw [hgt', sin_three_pi_div_two_add_int_mul_two_pi n] at this
      norm_num at this
  rw [hn, hm, hmn]; ring

end Work.Drive
