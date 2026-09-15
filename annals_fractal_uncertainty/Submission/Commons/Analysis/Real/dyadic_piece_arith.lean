import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.Analysis.Real

theorem dyadic_piece_arith (i a j : ℕ) (hia : i ≤ a) :
    (((2 : ℝ) ^ (j + 1))⁻¹) ^ i * (2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) * (1 - ((a - i : ℕ) : ℝ)))
      = (2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) * (1 - (a : ℝ))) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hcast : ((a - i : ℕ) : ℝ) = (a : ℝ) - (i : ℝ) := Nat.cast_sub hia
  rw [hcast]
  set N : ℝ := ((j + 1 : ℕ) : ℝ) with hN
  have hpow : ((2 : ℝ) ^ (j + 1))⁻¹ = (2 : ℝ) ^ (-N) := by
    rw [← Real.rpow_natCast (2 : ℝ) (j + 1), ← hN]
    exact (Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) N).symm
  have hnd : ((2 : ℝ) ^ (-N)) ^ i = (2 : ℝ) ^ ((-N) * (i : ℝ)) := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (-N)) i]
    exact (Real.rpow_mul (x := 2) (by norm_num) (-N) (i : ℝ)).symm
  calc
    (((2 : ℝ) ^ (j + 1))⁻¹) ^ i * (2 : ℝ) ^ (N * (1 - ((a : ℝ) - (i : ℝ))))
        = ((2 : ℝ) ^ (-N)) ^ i * (2 : ℝ) ^ (N * (1 - ((a : ℝ) - (i : ℝ)))) := by rw [hpow]
    _ = (2 : ℝ) ^ ((-N) * (i : ℝ)) * (2 : ℝ) ^ (N * (1 - ((a : ℝ) - (i : ℝ)))) := by rw [hnd]
    _ = (2 : ℝ) ^ ((-N) * (i : ℝ) + N * (1 - ((a : ℝ) - (i : ℝ)))) := by rw [← Real.rpow_add h2]
    _ = (2 : ℝ) ^ (N * (1 - (a : ℝ))) := by
        congr 1
        ring

end Commons.Analysis.Real