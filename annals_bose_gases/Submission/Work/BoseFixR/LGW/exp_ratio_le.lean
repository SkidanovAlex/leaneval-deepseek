import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR.LGW

/-- Elementary lower bound for `cosh`: `1 + t^2/2 ≤ cosh t`.

From `sinh x ≥ x` on `x ≥ 0` and `cosh (2 s) = 1 + 2 sinh s ^ 2` applied at `s = |t|/2`. -/
lemma one_add_sq_div_two_le_cosh (t : ℝ) : 1 + t^2/2 ≤ Real.cosh t := by
  set s : ℝ := |t| / 2 with hs
  have hsnonneg : 0 ≤ s := by rw [hs]; positivity
  have hs2 : 2 * s = |t| := by rw [hs]; ring
  have hle : s ≤ Real.sinh s := Real.self_le_sinh_iff.mpr hsnonneg
  have hsq : s^2 ≤ Real.sinh s ^ 2 := pow_le_pow_left₀ hsnonneg hle 2
  have hcosh : Real.cosh t = 1 + 2 * Real.sinh s ^ 2 := by
    rw [(Real.cosh_abs t).symm, ← hs2, Real.cosh_two_mul, Real.cosh_sq']
    ring
  have ht2 : t^2/2 = 2 * s^2 := by
    rw [hs, div_pow, sq_abs]; ring
  rw [hcosh, ht2]
  linarith

/-- `cosh t ≥ 1 + t^2/2` rewritten as `2 + t^2 ≤ exp t + exp (-t)`. -/
lemma add_sq_le_exp_add_exp_neg (t : ℝ) : 2 + t^2 ≤ Real.exp t + Real.exp (-t) := by
  have h := one_add_sq_div_two_le_cosh t
  rw [Real.cosh_eq] at h
  linarith

theorem exp_ratio_le (t : ℝ) : Real.exp t / (1 + Real.exp t)^2 ≤ 1/(4 + t^2) := by
  have h2 : 2 + t^2 ≤ Real.exp t + Real.exp (-t) := add_sq_le_exp_add_exp_neg t
  have he : 0 < Real.exp t := Real.exp_pos t
  -- Multiply `2 + t^2 ≤ e^t + e^{-t}` by `e^t > 0` and expand, using `e^t · e^{-t} = 1`.
  have hmain : (4 + t^2) * Real.exp t ≤ (1 + Real.exp t)^2 := by
    have hmul : (2 + t^2) * Real.exp t ≤ (Real.exp t + Real.exp (-t)) * Real.exp t :=
      mul_le_mul_of_nonneg_right h2 he.le
    have hprod : Real.exp t * Real.exp (-t) = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith [hmul, hprod]
  -- Both denominators are positive, so clear them.
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  simpa [mul_comm] using hmain

end Work.BoseFixR.LGW
