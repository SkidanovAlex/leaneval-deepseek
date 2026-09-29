import Mathlib

open MeasureTheory

namespace Work.Holonomy3

/-- Interval integrability transfers along the affine reparametrisation `u ↦ (u - a) / w` of
`[0,1]` onto `[a, a+w]` (for `0 < w`). -/
theorem intervalIntegrable_comp_div (g : ℝ → ℝ) {a w : ℝ} (hw : 0 < w)
    (h : IntervalIntegrable g volume 0 1) :
    IntervalIntegrable (fun s : ℝ => g ((s - a) / w)) volume a (a + w) := by
  -- First translate: `x ↦ x - a/w` sends `[a/w, a/w + 1]` to `[0, 1]`.
  have h1 : IntervalIntegrable (fun x : ℝ => g (x - a / w)) volume (0 + a / w) (1 + a / w) :=
    h.comp_sub_right (a / w)
  -- Then scale by `1/w`: `x ↦ x * (1/w)` sends `[a, a+w]` to `[a/w, a/w + 1]`.
  have h2 := h1.comp_mul_right (c := 1 / w)
  convert h2 using 1
  · ext s; field_simp
  · field_simp; ring
  · field_simp; ring

end Work.Holonomy3
