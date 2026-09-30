import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedVariables false

namespace Commons.Analysis.Real

theorem mul_rpow_interp_bound (C N A m : ℝ) (hC : 0 ≤ C) (hN : 0 ≤ N) (hA : 0 ≤ A)
    (hm : 0 ≤ m) (ε : ℝ) (hε : 0 ≤ ε) (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β = 1)
    (hmle : m ≤ Real.sqrt N * Real.sqrt A) :
    m ^ α * (C * Real.sqrt A * N ^ ε) ^ β ≤ C ^ β * Real.sqrt A * N ^ (α / 2 + ε * β) := by
  have hsqrtN : 0 ≤ Real.sqrt N := Real.sqrt_nonneg N
  have hsqrtA : 0 ≤ Real.sqrt A := Real.sqrt_nonneg A
  have hNε : 0 ≤ N ^ ε := Real.rpow_nonneg hN ε
  have hCs : 0 ≤ C * Real.sqrt A := mul_nonneg hC hsqrtA
  have hCsN : 0 ≤ C * Real.sqrt A * N ^ ε := mul_nonneg hCs hNε
  have hα2 : 0 ≤ α / 2 := div_nonneg hα (by norm_num : 0 ≤ (2 : ℝ))
  have hεβ : 0 ≤ ε * β := mul_nonneg hε hβ
  have hsqrtN_pow : (Real.sqrt N) ^ α = N ^ (α / 2) := by
    rw [Real.sqrt_eq_rpow]
    rw [← Real.rpow_mul hN (1 / 2) α]
    congr 1
    ring
  have hNeps_pow : (N ^ ε) ^ β = N ^ (ε * β) := by
    rw [← Real.rpow_mul hN ε β]
  calc
    m ^ α * (C * Real.sqrt A * N ^ ε) ^ β
        ≤ (Real.sqrt N * Real.sqrt A) ^ α * (C * Real.sqrt A * N ^ ε) ^ β := by
            exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hm hmle hα)
              (Real.rpow_nonneg hCsN β)
    _ = C ^ β * ((Real.sqrt N) ^ α * ((Real.sqrt A) ^ α * (Real.sqrt A) ^ β)) * (N ^ ε) ^ β := by
            rw [Real.mul_rpow hsqrtN hsqrtA]
            rw [Real.mul_rpow hCs hNε, Real.mul_rpow hC hsqrtA]
            ring_nf
    _ = C ^ β * ((Real.sqrt N) ^ α * (Real.sqrt A) ^ (α + β)) * (N ^ ε) ^ β := by
            rw [← Real.rpow_add_of_nonneg hsqrtA hα hβ]
    _ = C ^ β * Real.sqrt A * (Real.sqrt N) ^ α * (N ^ ε) ^ β := by
            rw [hαβ, Real.rpow_one]
            ring_nf
    _ = C ^ β * Real.sqrt A * N ^ (α / 2 + ε * β) := by
            calc
              C ^ β * Real.sqrt A * (Real.sqrt N) ^ α * (N ^ ε) ^ β
                  = C ^ β * Real.sqrt A * N ^ (α / 2) * N ^ (ε * β) := by
                      rw [hsqrtN_pow, hNeps_pow]
              _ = C ^ β * Real.sqrt A * (N ^ (α / 2) * N ^ (ε * β)) := by
                      ring
              _ = C ^ β * Real.sqrt A * N ^ (α / 2 + ε * β) := by
                      rw [← Real.rpow_add_of_nonneg hN hα2 hεβ]

end Commons.Analysis.Real