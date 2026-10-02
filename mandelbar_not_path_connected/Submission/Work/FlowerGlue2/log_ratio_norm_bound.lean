import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FlowerGlue2

/-- Comparison of the ratio `t ↦ (1 + log t)/t^2` at `‖z‖` against its value at the
`ℓ¹`-norm `|z.re| + |z.im|`.  Since `‖z‖ ≤ |z.re| + |z.im| ≤ √2 * ‖z‖` and the factor `2`
absorbs the factor `t^2 ≤ 2`, the bound holds for every `z` with `1 ≤ ‖z‖`. -/
theorem log_ratio_norm_bound (z : ℂ) (hz : 1 ≤ ‖z‖) :
    (1 + Real.log ‖z‖) / ‖z‖ ^ 2 ≤
      2 * (1 + Real.log (|z.re| + |z.im|)) / (|z.re| + |z.im|) ^ 2 := by
  set r : ℝ := ‖z‖ with hr
  set s : ℝ := |z.re| + |z.im| with hs
  have hr1 : 1 ≤ r := hz
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hrs : r ≤ s := by
    rw [hr, hs]
    exact Complex.norm_le_abs_re_add_abs_im z
  have hs_nonneg : 0 ≤ s := le_trans (le_of_lt hrpos) hrs
  have h2 : s ^ 2 ≤ 2 * r ^ 2 := by
    rw [hs, hr, Complex.sq_norm, Complex.normSq_apply]
    nlinarith [sq_abs z.re, sq_abs z.im, sq_nonneg (|z.re| - |z.im|)]
  set t : ℝ := s / r with ht
  have ht1 : 1 ≤ t := by
    rw [ht]
    exact (one_le_div hrpos).mpr hrs
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have ht2 : t ^ 2 ≤ 2 := by
    rw [ht, div_pow, div_le_iff₀ (by positivity : (0:ℝ) < r ^ 2)]
    linarith [h2]
  have hs_eq : s = t * r := by
    rw [ht]
    exact (div_mul_cancel₀ s (ne_of_gt hrpos)).symm
  have hlogr : 0 ≤ Real.log r := Real.log_nonneg hr1
  have hlogt : 0 ≤ Real.log t := Real.log_nonneg ht1
  rw [hs_eq, Real.log_mul (ne_of_gt htpos) (ne_of_gt hrpos)]
  rw [div_le_div_iff₀ (by positivity : (0:ℝ) < r ^ 2)
    (by positivity : (0:ℝ) < (t * r) ^ 2)]
  have hstep : (1 + Real.log r) * t ^ 2 ≤ 2 * (1 + Real.log t + Real.log r) := by
    have hA : (1 + Real.log r) * t ^ 2 ≤ (1 + Real.log r) * 2 :=
      mul_le_mul_of_nonneg_left ht2 (by linarith)
    have hB : (1 + Real.log r) * 2 ≤ 2 * (1 + Real.log t + Real.log r) := by linarith
    linarith
  have hfin : (1 + Real.log r) * t ^ 2 * r ^ 2 ≤
      2 * (1 + Real.log t + Real.log r) * r ^ 2 :=
    mul_le_mul_of_nonneg_right hstep (sq_nonneg r)
  nlinarith [hfin]

end Work.FlowerGlue2
