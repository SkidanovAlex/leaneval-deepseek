import Mathlib

namespace Work.LinnikAreas

/-- Elementary numerical comparison used in the Linnik argument: the product
`C₀ * ((q) * T)^e` is dominated by `C * exp ((5/2) ((1-σ) log q)) * T^(3/2)`,
because `q^e ≤ q^((5/2)(1-σ)) = exp((5/2)(1-σ) log q)` (with `q ≥ 2 > 1` and
`e ≤ (5/2)(1-σ)`), because `T^e ≤ T^(3/2)` (with `T ≥ 1` and `e ≤ 3/2`), and
because `C₀ ≤ C` with `C₀ ≥ 0`. -/
theorem rpow_le_expHeight_mul {q : ℕ} (hq : 2 ≤ q) {T C₀ C e σ : ℝ} (hT : 1 ≤ T)
    (hC₀ : 0 ≤ C₀) (hC : C₀ ≤ C) (hef : e ≤ (5 : ℝ) / 2 * (1 - σ))
    (heg : e ≤ (3 : ℝ) / 2) :
    C₀ * ((q : ℝ) * T) ^ e
      ≤ C * Real.exp ((5 / 2) * ((1 - σ) * Real.log q)) * T ^ ((3 : ℝ) / 2) := by
  have hq1nat : (1 : ℕ) ≤ q := le_trans (by norm_num) hq
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1nat
  have hqpos : (0 : ℝ) < (q : ℝ) := lt_of_lt_of_le zero_lt_one hq1
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hT
  have hqTpos : (0 : ℝ) < (q : ℝ) * T := mul_pos hqpos hTpos
  have hlogq_nonneg : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hq1
  -- the `q`-part: `q^e ≤ exp ((5/2) ((1-σ) log q))`
  have hqe : (q : ℝ) ^ e ≤ Real.exp ((5 / 2) * ((1 - σ) * Real.log q)) := by
    calc (q : ℝ) ^ e = Real.exp (Real.log (q : ℝ) * e) := Real.rpow_def_of_pos hqpos e
      _ ≤ Real.exp (Real.log (q : ℝ) * ((5 / 2) * (1 - σ))) :=
            Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hef hlogq_nonneg)
      _ = Real.exp ((5 / 2) * ((1 - σ) * Real.log q)) := by
            congr 1; ring
  -- the `T`-part: `T^e ≤ T^(3/2)`
  have hTe : T ^ e ≤ T ^ ((3 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le hT heg
  -- combine
  have hmain : ((q : ℝ) * T) ^ e
      ≤ Real.exp ((5 / 2) * ((1 - σ) * Real.log q)) * T ^ ((3 : ℝ) / 2) := by
    rw [Real.mul_rpow (le_of_lt hqpos) (le_of_lt hTpos)]
    exact mul_le_mul hqe hTe (Real.rpow_nonneg (le_of_lt hTpos) e) (Real.exp_nonneg _)
  calc C₀ * ((q : ℝ) * T) ^ e
      ≤ C * ((q : ℝ) * T) ^ e :=
        mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (le_of_lt hqTpos) e)
    _ ≤ C * (Real.exp ((5 / 2) * ((1 - σ) * Real.log q)) * T ^ ((3 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left hmain (le_trans hC₀ hC)
    _ = C * Real.exp ((5 / 2) * ((1 - σ) * Real.log q)) * T ^ ((3 : ℝ) / 2) := by ring

end Work.LinnikAreas
