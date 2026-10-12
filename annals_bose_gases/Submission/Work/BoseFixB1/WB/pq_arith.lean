import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1.WB

theorem pq_arith {A B T C ε : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hT : 0 ≤ T) (hTB : T ≤ B)
    (hε : 0 < ε) (hC : |C| ≤ Real.sqrt A * Real.sqrt T) :
    A + 2 * C + T ≤ (1 + ε) * A + (1 + ε⁻¹) * B ∧
      (1 - ε) * A - (1 + ε⁻¹) * B ≤ A + 2 * C + T := by
  -- Write s = √A √T, so |C| ≤ s and s² = A·T (both A, T ≥ 0).
  have hεinv : 0 ≤ ε⁻¹ := inv_nonneg.mpr (le_of_lt hε)
  have hs : 0 ≤ Real.sqrt A * Real.sqrt T :=
    mul_nonneg (Real.sqrt_nonneg A) (Real.sqrt_nonneg T)
  have hsq : (Real.sqrt A * Real.sqrt T) ^ 2 = A * T := by
    rw [mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hT]
  have hinv : ε * ε⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hε)
  -- The weighted AM–GM inequality: 2√A√T ≤ εA + ε⁻¹T.
  have key : (ε * A + ε⁻¹ * T) ^ 2 - (2 * (Real.sqrt A * Real.sqrt T)) ^ 2
      = (ε * A - ε⁻¹ * T) ^ 2 := by
    nlinarith [hsq, hinv]
  have hsquare : (2 * (Real.sqrt A * Real.sqrt T)) ^ 2 ≤ (ε * A + ε⁻¹ * T) ^ 2 := by
    nlinarith [sq_nonneg (ε * A - ε⁻¹ * T)]
  have hAM : 2 * (Real.sqrt A * Real.sqrt T) ≤ ε * A + ε⁻¹ * T := by
    have h2s : (0:ℝ) ≤ 2 * (Real.sqrt A * Real.sqrt T) := by linarith
    have hR : (0:ℝ) ≤ ε * A + ε⁻¹ * T := by
      have h1 : 0 ≤ ε * A := mul_nonneg (le_of_lt hε) hA
      have h2 : 0 ≤ ε⁻¹ * T := mul_nonneg hεinv hT
      linarith
    have h := sq_le_sq.mp hsquare
    rwa [abs_of_nonneg h2s, abs_of_nonneg hR] at h
  have hC_le : C ≤ Real.sqrt A * Real.sqrt T := le_trans (le_abs_self C) hC
  have hC_ge : -Real.sqrt A * Real.sqrt T ≤ C := by
    have h2 : -C ≤ Real.sqrt A * Real.sqrt T := le_trans (neg_le_abs C) hC
    linarith
  have hTBinv : ε⁻¹ * T ≤ ε⁻¹ * B := mul_le_mul_of_nonneg_left hTB hεinv
  constructor
  · -- upper: 2C ≤ 2s ≤ εA + ε⁻¹T ≤ εA + (1 + ε⁻¹)B - T
    nlinarith [hC_le, hAM, hTB, hTBinv]
  · -- lower: 2C ≥ -2s ≥ -(εA + ε⁻¹T) ≥ -(εA + (1 + ε⁻¹)B + T)
    nlinarith [hC_ge, hAM, hTBinv, hT, hB]

end Work.BoseFixB1.WB
