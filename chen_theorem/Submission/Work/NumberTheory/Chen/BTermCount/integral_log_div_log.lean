import Mathlib

namespace Work.NumberTheory.Chen.BTermCount

/-- Change of variables `t ↦ s = log t / log X` in the integral `∫ F(log t/log X)/(t log t) dt`, valid for `1 < X`, `0 < a ≤ b` and `F` continuous on the image interval. (Substitution `t = X^s`, whose derivative is `X^s log X`, and then `log (X^s) = s log X`.) -/
theorem integral_log_div_log (X a b : ℝ) (hX : 1 < X) (ha : 0 < a) (ha1 : 1 < a) (hab : a ≤ b) (F : ℝ → ℝ)
    (hF : ContinuousOn F (Set.Icc (Real.log a / Real.log X) (Real.log b / Real.log X))) :
    (∫ t in a..b, F (Real.log t / Real.log X) / (t * Real.log t))
      = ∫ s in (Real.log a / Real.log X)..(Real.log b / Real.log X), F s / s := by
  have hX0 : 0 < X := lt_trans zero_lt_one hX
  have hLpos : 0 < Real.log X := Real.log_pos hX
  have hb1 : 1 < b := lt_of_lt_of_le ha1 hab
  have hαβ : Real.log a / Real.log X ≤ Real.log b / Real.log X :=
    div_le_div_of_nonneg_right (Real.log_le_log ha hab) hLpos.le
  have hα : 0 < Real.log a / Real.log X := div_pos (Real.log_pos ha1) hLpos
  have hpow_a : X ^ (Real.log a / Real.log X) = a := by
    rw [Real.rpow_def_of_pos hX0]
    rw [show Real.log X * (Real.log a / Real.log X) = Real.log a by field_simp]
    exact Real.exp_log ha
  have hpow_b : X ^ (Real.log b / Real.log X) = b := by
    rw [Real.rpow_def_of_pos hX0]
    rw [show Real.log X * (Real.log b / Real.log X) = Real.log b by field_simp]
    exact Real.exp_log (lt_trans zero_lt_one hb1)
  have hkey := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := Real.log a / Real.log X) (b := Real.log b / Real.log X)
    (f := fun s : ℝ => X ^ s) (f' := fun s : ℝ => X ^ s * Real.log X)
    (g := fun u : ℝ => F (Real.log u / Real.log X) / (u * Real.log u))
    ((Real.continuous_const_rpow hX0.ne').continuousOn)
    (fun x _ => (Real.hasStrictDerivAt_const_rpow hX0 x).hasDerivAt)
    (fun x _ => le_of_lt (mul_pos (Real.rpow_pos_of_pos hX0 x) hLpos))
  rw [hpow_a, hpow_b] at hkey
  simp only [Function.comp_apply] at hkey
  have hcongr : (∫ x in (Real.log a / Real.log X)..(Real.log b / Real.log X),
      (fun u : ℝ => F (Real.log u / Real.log X) / (u * Real.log u)) (X ^ x) * (X ^ x * Real.log X))
      = ∫ x in (Real.log a / Real.log X)..(Real.log b / Real.log X), F x / x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hαβ] at hx
    have hxpos : 0 < x := lt_of_lt_of_le hα hx.1
    simp only
    rw [Real.log_rpow hX0 x]
    have h1 : x * Real.log X / Real.log X = x := by field_simp
    rw [h1]
    have hXx : 0 < X ^ x := Real.rpow_pos_of_pos hX0 x
    field_simp
  rw [hcongr] at hkey
  exact hkey.symm

end Work.NumberTheory.Chen.BTermCount
