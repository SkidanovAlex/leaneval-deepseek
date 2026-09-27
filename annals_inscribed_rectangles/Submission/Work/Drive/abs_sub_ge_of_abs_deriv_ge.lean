import Mathlib

namespace Work.Drive

set_option linter.unusedVariables false

/-- Mean-value (reverse) inequality: if `f` is continuous on `[a,b]`, has derivative `g` on
`(a,b)`, and `|g| ≥ m` there with `m ≥ 0`, then the increment of `f` dominates `m * (b - a)`.

This is the "second half" of the mean value theorem: find `c ∈ (a,b)` with
`f b - f a = g c * (b - a)` and take absolute values. -/
theorem abs_sub_ge_of_abs_deriv_ge {f g : ℝ → ℝ} {a b m : ℝ} (hab : a ≤ b) (hm : 0 ≤ m)
    (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Ioo a b))
    (hd : ∀ x ∈ Set.Ioo a b, HasDerivAt f (g x) x)
    (hmg : ∀ x ∈ Set.Ioo a b, m ≤ |g x|) : m * (b - a) ≤ |f b - f a| := by
  rcases lt_or_eq_of_le hab with hlt | heq
  · -- The interesting case `a < b`: apply the mean value theorem.
    obtain ⟨c, hc, hgc⟩ := exists_hasDerivAt_eq_slope f g hlt hf hd
    have hbda : (0 : ℝ) < b - a := sub_pos.mpr hlt
    have hne : b - a ≠ 0 := ne_of_gt hbda
    -- rewrite the slope equation into `f b - f a = g c * (b - a)`
    have key : f b - f a = g c * (b - a) := by
      rw [eq_div_iff hne] at hgc
      exact hgc.symm
    rw [key, abs_mul, abs_of_pos hbda]
    exact mul_le_mul_of_nonneg_right (hmg c hc) (le_of_lt hbda)
  · -- Degenerate case `a = b`: both sides vanish.
    subst heq
    simp only [sub_self, abs_zero]
    nlinarith [hm]

end Work.Drive
