import Mathlib

/-!
# Derivative bound for `v ↦ F v / √v`

If `F` is `C¹` with `|F'| ≤ 1/M` and `|F| ≤ 2` everywhere, then for `u ≥ 1` the
derivative of `v ↦ F v / √v` at `u` is bounded by

`1 / (M * √u) + 1 / (u * √u)`.

Indeed `(F/√·)' = F'/√· - F/(2··√·)`, and on `u ≥ 1 > 0` the two terms are at
most `(1/M)/√u` and `2/(2·u·√u) = 1/(u·√u)`.
-/

namespace Work.FIArea2

/-- Chain rule for the quotient `v ↦ F v / √v`: its derivative is
`F' u / √u - F u / (2 * u * √u)` at any `u > 0`. -/
lemma deriv_div_sqrt_eq_aux {F : ℝ → ℝ} {u : ℝ} (hF : DifferentiableAt ℝ F u) (hu : 0 < u) :
    deriv (fun v => F v / Real.sqrt v) u
      = deriv F u / Real.sqrt u - F u / (2 * u * Real.sqrt u) := by
  have hsne : Real.sqrt u ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hu)
  have h := (hF.hasDerivAt).div (Real.hasDerivAt_sqrt (ne_of_gt hu)) hsne
  have hd : deriv (fun v => F v / Real.sqrt v) u
      = (deriv F u * Real.sqrt u - F u * (1 / (2 * Real.sqrt u))) / Real.sqrt u ^ 2 := h.deriv
  rw [hd]
  field_simp
  rw [Real.sq_sqrt (le_of_lt hu)]
  ring

theorem abs_deriv_div_sqrt_le {F : ℝ → ℝ} (hFc : ContDiff ℝ 1 F) {M : ℝ} (hM : 0 < M)
    (hderiv : ∀ u : ℝ, |deriv F u| ≤ 1 / M) (hbd : ∀ u : ℝ, |F u| ≤ 2) {u : ℝ} (hu : 1 ≤ u) :
    |deriv (fun v => F v / Real.sqrt v) u| ≤ 1 / (M * Real.sqrt u) + 1 / (u * Real.sqrt u) := by
  have _hMpos : 0 < M := hM
  have hu0 : (0:ℝ) < u := lt_of_lt_of_le zero_lt_one hu
  have hspos : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu0
  have hdiff : DifferentiableAt ℝ F u := hFc.differentiable_one u
  rw [deriv_div_sqrt_eq_aux hdiff hu0]
  have h1 : |deriv F u / Real.sqrt u| ≤ 1 / (M * Real.sqrt u) := by
    rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg u)]
    calc |deriv F u| / Real.sqrt u ≤ (1 / M) / Real.sqrt u :=
          div_le_div_of_nonneg_right (hderiv u) (le_of_lt hspos)
      _ = 1 / (M * Real.sqrt u) := by rw [div_div]
  have h2 : |F u / (2 * u * Real.sqrt u)| ≤ 1 / (u * Real.sqrt u) := by
    have hpos : 0 < 2 * u * Real.sqrt u := mul_pos (mul_pos two_pos hu0) hspos
    rw [abs_div, abs_of_pos hpos]
    calc |F u| / (2 * u * Real.sqrt u) ≤ 2 / (2 * u * Real.sqrt u) :=
          div_le_div_of_nonneg_right (hbd u) (le_of_lt hpos)
      _ = 1 / (u * Real.sqrt u) := by field_simp
  calc |deriv F u / Real.sqrt u - F u / (2 * u * Real.sqrt u)|
      ≤ |deriv F u / Real.sqrt u| + |F u / (2 * u * Real.sqrt u)| := abs_sub _ _
    _ ≤ 1 / (M * Real.sqrt u) + 1 / (u * Real.sqrt u) := add_le_add h1 h2

end Work.FIArea2
