import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.liouville

/-- `‖y^{1-iu} − x^{1-iu}‖ ≤ ‖1-iu‖ (y−x)` for `0 < x ≤ y`: the map `t ↦ t^{1-iu}` has
derivative `(1-iu) t^{-iu}` of modulus `‖1-iu‖` on the positive real axis, because
`‖t^{1-iu}‖ = t`. -/
lemma cpow_one_sub_I_mul_sub_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (u : ℝ) :
    ‖(y : ℂ) ^ (1 - Complex.I * (u : ℂ)) - (x : ℂ) ^ (1 - Complex.I * (u : ℂ))‖ ≤
      ‖1 - Complex.I * (u : ℂ)‖ * (y - x) := by
  set r : ℂ := 1 - Complex.I * (u : ℂ) with hr
  have hr_re : r.re = 1 := by simp [hr]
  have hr_ne : r ≠ 0 := by
    intro h
    rw [h] at hr_re
    simp at hr_re
  let f : ℝ → ℂ := fun t => (t : ℂ) ^ r
  let f' : ℝ → ℂ := fun t => r * (t : ℂ) ^ (r - 1)
  have key : ‖f y - f x‖ ≤ ‖r‖ * ‖y - x‖ := by
    refine Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := f) (f' := f')
      (s := Set.Icc x y) (C := ‖r‖) ?_ ?_ (convex_Icc x y) ⟨le_refl x, hxy⟩ ⟨hxy, le_refl y⟩
    · intro t ht
      have ht_pos : 0 < t := lt_of_lt_of_le hx ht.1
      simpa only [f, f'] using
        (hasDerivAt_ofReal_cpow_const (ne_of_gt ht_pos) hr_ne).hasDerivWithinAt
    · intro t ht
      have ht_pos : 0 < t := lt_of_lt_of_le hx ht.1
      have hnorm : ‖(t : ℂ) ^ (r - 1)‖ = 1 := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos ht_pos]
        have hre : (r - 1).re = 0 := by
          simp [Complex.sub_re, hr_re]
        rw [hre, Real.rpow_zero]
      simp only [f']
      rw [norm_mul, hnorm, mul_one]
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hxy)] at key
  simpa only [f] using key

end Work.BMF.liouville
