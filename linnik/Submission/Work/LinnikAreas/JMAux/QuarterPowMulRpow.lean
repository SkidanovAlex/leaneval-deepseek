import Mathlib

namespace Work.LinnikAreas.JMAux

lemma QuarterPowMulRpow (q k : ℕ) (θ : ℝ) :
    (1/4:ℝ)^k * (((q:ℝ) * (2:ℝ)^k)^θ) = (q:ℝ)^θ * ((2:ℝ)^(θ - 2))^k := by
  have h2 : (0:ℝ) < 2 := by norm_num
  have h2le : (0:ℝ) ≤ 2 := le_of_lt h2
  have hq : (0:ℝ) ≤ (q:ℝ) := by positivity
  have hquarter : (1/4:ℝ) = (2:ℝ)^(-2:ℝ) := by
    rw [show (-2:ℝ) = -(2:ℝ) by norm_num, Real.rpow_neg h2le, Real.rpow_two]
    norm_num
  have h1 : (1/4:ℝ)^k = (2:ℝ)^((-2:ℝ)*(k:ℝ)) := by
    rw [← Real.rpow_natCast (1/4:ℝ) k, hquarter, ← Real.rpow_mul h2le]
  have hL : (1/4:ℝ)^k * (((q:ℝ) * (2:ℝ)^k)^θ) = (q:ℝ)^θ * (2:ℝ)^((k:ℝ)*(θ-2)) := by
    rw [Real.mul_rpow hq (by positivity : (0:ℝ) ≤ (2:ℝ)^k)]
    rw [← Real.rpow_natCast_mul h2le k θ]
    rw [h1]
    rw [show (2:ℝ)^((-2:ℝ)*(k:ℝ)) * ((q:ℝ)^θ * (2:ℝ)^((k:ℝ)*θ))
          = (q:ℝ)^θ * ((2:ℝ)^((-2:ℝ)*(k:ℝ)) * (2:ℝ)^((k:ℝ)*θ)) by ring]
    rw [← Real.rpow_add h2]
    rw [show (-2:ℝ)*(k:ℝ) + (k:ℝ)*θ = (k:ℝ)*(θ-2) by ring]
  have hR : (q:ℝ)^θ * ((2:ℝ)^(θ-2))^k = (q:ℝ)^θ * (2:ℝ)^((k:ℝ)*(θ-2)) := by
    rw [← Real.rpow_natCast ((2:ℝ)^(θ-2)) k]
    rw [← Real.rpow_mul h2le]
    rw [show (θ-2)*(k:ℝ) = (k:ℝ)*(θ-2) by ring]
  exact hL.trans hR.symm

end Work.LinnikAreas.JMAux
