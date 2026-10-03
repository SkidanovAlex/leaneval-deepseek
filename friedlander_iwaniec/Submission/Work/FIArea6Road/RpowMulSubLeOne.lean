import Mathlib

namespace Work.FIArea6Road

/-- For `1 ≤ C ≤ N` and `x ≤ 1`, we have `N ^ x * C ^ (1 - x) ≤ N`.
Since `1 - x ≥ 0`, monotonicity of `rpow` gives `C ^ (1 - x) ≤ N ^ (1 - x)`,
and `N ^ x * N ^ (1 - x) = N ^ (x + (1 - x)) = N`. -/
theorem RpowMulSubLeOne (N C x : ℝ) (hN : 1 ≤ N) (hC : 1 ≤ C) (hCN : C ≤ N) (hx : x ≤ 1) :
    N ^ x * C ^ (1 - x) ≤ N := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have h1x : 0 ≤ 1 - x := by linarith
  have hle : C ^ (1 - x) ≤ N ^ (1 - x) := Real.rpow_le_rpow (le_of_lt hCpos) hCN h1x
  calc N ^ x * C ^ (1 - x)
      ≤ N ^ x * N ^ (1 - x) := mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg (le_of_lt hNpos) x)
    _ = N := by
        rw [← Real.rpow_add hNpos]
        have : x + (1 - x) = 1 := by ring
        rw [this, Real.rpow_one]

end Work.FIArea6Road
