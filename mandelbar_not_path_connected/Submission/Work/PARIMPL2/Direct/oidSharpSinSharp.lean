import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

/-- Sharp lower bounds for `sin` on the small argument `lam * R / 4`.

Since `lam * R ^ 2 ≤ 1` and `R ≥ 128`, the argument `x = lam * R / 4` satisfies
`0 < x ≤ 1/512`, so `x - x ^ 3 / 6 ≤ sin x` gives both `(5/6) x ≤ sin x`
(because `x ^ 2 ≤ 1`) and `x / (2π) * ... `, i.e. `lam * R / (2π) ≤ sin x`,
using `2/π ≤ 5/6`. -/
theorem oidSharpSinSharp (lam R : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R) (hlamR : lam * R ^ 2 ≤ 1) :
    lam * R / (2 * Real.pi) ≤ Real.sin (lam * R / 4) ∧
    (5 / 6) * (lam * R / 4) ≤ Real.sin (lam * R / 4) ∧
    0 < lam * R / 4 ∧ lam * R / 4 ≤ Real.pi / 2 ∧ 0 < Real.sin (lam * R / 4) := by
  have hRpos : (0:ℝ) < R := by linarith
  set x := lam * R / 4 with hx
  have hxpos : 0 < x := by rw [hx]; positivity
  -- key: lam * R ≤ 1/128
  have hkey : lam * R ≤ 1 / 128 := by
    have hRne : R ≠ 0 := ne_of_gt hRpos
    have h1 : lam * R ^ 2 / R ≤ 1 / R := div_le_div_of_nonneg_right hlamR hRpos.le
    have heq : lam * R ^ 2 / R = lam * R := by field_simp
    rw [heq] at h1
    have h2 : 1 / R ≤ 1 / 128 := one_div_le_one_div_of_le (by norm_num) hR
    linarith
  have hx_le : x ≤ 1 / 512 := by
    rw [hx, div_le_iff₀ (by norm_num : (0:ℝ) < 4)]
    nlinarith [hkey]
  have hx1 : x ≤ 1 := by linarith
  have hx_sq_le : x ^ 2 ≤ 1 := by nlinarith [hxpos, hx1]
  have hx2 : x ≤ Real.pi / 2 := by
    have hp : (1:ℝ) / 512 ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
    linarith
  have hsin_lb : x - x ^ 3 / 6 ≤ Real.sin x := Real.sin_ge_sub_cube hxpos.le
  have h5 : (5 / 6) * x ≤ Real.sin x := by
    have : (5 / 6) * x ≤ x - x ^ 3 / 6 := by nlinarith [hx_sq_le, hxpos]
    linarith
  have hcoef : 2 / Real.pi ≤ 5 / 6 := by
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith [Real.pi_gt_three]
  have heq : lam * R / (2 * Real.pi) = (2 / Real.pi) * x := by
    rw [hx]; field_simp; ring
  refine ⟨?_, h5, hxpos, hx2, ?_⟩
  · rw [heq]
    exact (mul_le_mul_of_nonneg_right hcoef hxpos.le).trans h5
  · nlinarith [h5, hxpos]

end Work.PARIMPL2.Direct
