import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open scoped ENNReal

/-- Weighted AM–GM (geometric mean ≤ arithmetic mean) for two `ℝ≥0∞`-values that are `ofReal`s
of nonnegative reals: `x ^ lam * y ^ (1 - lam) ≤ lam * x + (1 - lam) * y`. -/
lemma ennreal_ofReal_geomMeanLeArithMean (x y lam : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    ENNReal.ofReal x ^ lam * ENNReal.ofReal y ^ (1 - lam) ≤
      ENNReal.ofReal lam * ENNReal.ofReal x
        + ENNReal.ofReal (1 - lam) * ENNReal.ofReal y := by
  have h1ml : 0 ≤ 1 - lam := by linarith
  have hreal : x ^ lam * y ^ (1 - lam) ≤ lam * x + (1 - lam) * y :=
    Real.geom_mean_le_arith_mean2_weighted h0 h1ml hx hy (by ring)
  rw [ENNReal.ofReal_rpow_of_nonneg hx h0, ENNReal.ofReal_rpow_of_nonneg hy h1ml]
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hx lam), ← ENNReal.ofReal_mul h0,
    ← ENNReal.ofReal_mul h1ml]
  rw [← ENNReal.ofReal_add (mul_nonneg h0 hx) (mul_nonneg h1ml hy)]
  exact ENNReal.ofReal_le_ofReal hreal

/-- Weighted AM–GM (geometric mean ≤ arithmetic mean) for `ℝ≥0∞`, two-variable form. -/
theorem ennrealGeomMeanLeArithMean {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (a b : ℝ≥0∞) :
    a ^ lam * b ^ (1 - lam) ≤ ENNReal.ofReal lam * a + ENNReal.ofReal (1 - lam) * b := by
  rcases eq_or_lt_of_le h0 with rfl | h0'
  · simp
  rcases eq_or_lt_of_le h1 with rfl | h1'
  · simp
  have h1ml : 0 < 1 - lam := by linarith
  have hlam : ENNReal.ofReal lam ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr h0'
  have h1ml_ne : ENNReal.ofReal (1 - lam) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr h1ml
  rcases eq_or_ne a ⊤ with ha | ha
  · rw [ha, ENNReal.top_rpow_of_pos h0', ENNReal.mul_top hlam]
    simp
  rcases eq_or_ne b ⊤ with hb | hb
  · rw [hb, ENNReal.mul_top h1ml_ne]
    simp
  · rw [← ENNReal.ofReal_toReal ha, ← ENNReal.ofReal_toReal hb]
    exact ennreal_ofReal_geomMeanLeArithMean a.toReal b.toReal lam
      ENNReal.toReal_nonneg ENNReal.toReal_nonneg h0 h1

end Work.BW
