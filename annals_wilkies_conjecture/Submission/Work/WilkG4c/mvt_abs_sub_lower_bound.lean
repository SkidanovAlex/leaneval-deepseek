import Mathlib

namespace Work.WilkG4c

/-- **Mean value theorem, lower bound form.** If `F : ℝ → ℝ` is continuous on `[a,b]`,
differentiable on `(a,b)` and `c ≤ |F'|` on `(a,b)`, then `c * (b - a) ≤ |F b - F a|`. -/
theorem mvt_abs_sub_lower_bound {F : ℝ → ℝ} {a b c : ℝ} (hab : a < b)
    (hcont : ContinuousOn F (Set.Icc a b))
    (hdiff : ∀ x ∈ Set.Ioo a b, DifferentiableAt ℝ F x)
    (hder : ∀ x ∈ Set.Ioo a b, c ≤ |deriv F x|) :
    c * (b - a) ≤ |F b - F a| := by
  have hd : DifferentiableOn ℝ F (Set.Ioo a b) :=
    fun x hx => (hdiff x hx).differentiableWithinAt
  obtain ⟨x, hx, hxeq⟩ := exists_deriv_eq_slope F hab hcont hd
  have hba : (0 : ℝ) < b - a := sub_pos.mpr hab
  have hkey : deriv F x * (b - a) = F b - F a := by
    rw [hxeq, div_mul_cancel₀ _ (ne_of_gt hba)]
  calc c * (b - a) ≤ |deriv F x| * (b - a) :=
        mul_le_mul_of_nonneg_right (hder x hx) hba.le
    _ = |deriv F x * (b - a)| := by rw [abs_mul, abs_of_pos hba]
    _ = |F b - F a| := by rw [hkey]

end Work.WilkG4c
