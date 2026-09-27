import Mathlib
import Submission.Work.EKLC8Core.Vol

namespace Work.EKLC8Core

theorem step7_arith {T θ τ η : ℝ} (hT : 0 < T) (hθ : 4 * T ≤ θ) (hθ' : θ ≤ 6 * T)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ T) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    0 ≤ (θ - η * τ) / 2 ∧ τ + (θ - η * τ) / 2 = (θ + (2 - η) * τ) / 2 ∧
    Real.exp (2 * ((θ - η * τ) / 2)) = Real.exp (θ - η * τ) ∧
    (θ + (2 - η) * τ) / 2 ∈ Set.Icc (2 * T) (4 * T) := by
  -- η * τ ≤ 1 * T = T since 0 ≤ η ≤ 1, 0 ≤ τ ≤ T
  have hητ : η * τ ≤ T := by
    have := mul_le_mul hη1 hτ1 hτ0 (by norm_num : (0:ℝ) ≤ 1)
    simpa using this
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- 0 ≤ (θ - η * τ)/2, from ητ ≤ T ≤ θ
    nlinarith [hητ, hθ]
  · -- algebraic identity
    ring
  · -- equal arguments of exp
    rw [show 2 * ((θ - η * τ) / 2) = θ - η * τ by ring]
  · -- two-sided bound
    constructor
    · nlinarith [hτ0, hη1, hη0, hθ]
    · nlinarith [hθ', hτ1, hη0]

end Work.EKLC8Core
