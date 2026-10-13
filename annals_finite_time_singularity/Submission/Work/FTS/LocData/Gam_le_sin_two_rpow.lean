import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.LocData.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The angular weight bound `Γ(θ) ≤ sin(2θ)^{α/5}` on `Iθ`

`Γ(θ) = (sin θ cos²θ)^{α/3}` and, on `Iθ = [0,π/2]`, `sin(2θ) = 2 sin θ cos θ`.  The
pointwise estimate of this file is the elementary angular inequality used to absorb the
factor `Γ` into the weight `sin(2θ)^{-γ/2}` of the `ℋ^k`-integrand (Elgindi, Annals 194(3)
2021, §Notation and §H2).

## Mathematics

Write `A = sin θ · cos²θ` and `b = sin(2θ)`.  On `Iθ` both are nonnegative and `b ≤ 1`.
Since `0 ≤ cos θ ≤ 1`,

* `A = b·cos θ / 2 ≤ b / 2`, hence `A ^ 5 ≤ (b/2) ^ 5 ≤ b ^ 5`;
* `b ^ 5 ≤ b ^ 3` because `0 ≤ b ≤ 1`.

So `A ^ 5 ≤ b ^ 3`.  Raising to the nonnegative power `α/15` and using
`(A ^ 5) ^ (α/15) = A ^ (5·α/15) = A ^ (α/3)`, `(b ^ 3) ^ (α/15) = b ^ (3·α/15) = b ^ (α/5)`
gives `Γ(θ) = A ^ (α/3) ≤ b ^ (α/5) = sin(2θ) ^ (α/5)`.
-/
open scoped Real

namespace Work.FTS.LocData

theorem Gam_le_sin_two_rpow (α : ℝ) (hα : 0 < α) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.Gam α θ ≤ (Real.sin (2 * θ)) ^ (α / 5) := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  have hs0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ0, by linarith [hθ1, Real.pi_pos]⟩
  have hc0 : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ0, Real.pi_pos], hθ1⟩
  have hc1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hb0 : 0 ≤ Real.sin (2 * θ) := by rw [Real.sin_two_mul]; positivity
  have hb1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hA0 : 0 ≤ Real.sin θ * Real.cos θ ^ 2 := mul_nonneg hs0 (sq_nonneg _)
  -- `A ≤ sin(2θ)/2`
  have hAs : Real.sin θ * Real.cos θ ^ 2 ≤ Real.sin (2 * θ) / 2 := by
    rw [Real.sin_two_mul]
    have hcs : Real.cos θ ^ 2 ≤ Real.cos θ := by nlinarith [hc0, hc1, sq_nonneg (Real.cos θ)]
    nlinarith [mul_le_mul_of_nonneg_left hcs hs0]
  -- the numerical core: `A ^ 5 ≤ sin(2θ) ^ 3`
  have hA5 : (Real.sin θ * Real.cos θ ^ 2) ^ 5 ≤ (Real.sin (2 * θ)) ^ 3 := by
    have h1 : (Real.sin θ * Real.cos θ ^ 2) ^ 5 ≤ (Real.sin (2 * θ) / 2) ^ 5 :=
      pow_le_pow_left₀ hA0 hAs 5
    have h2 : (Real.sin (2 * θ) / 2) ^ 5 ≤ (Real.sin (2 * θ)) ^ 5 := by
      apply pow_le_pow_left₀ (by positivity)
      linarith
    have h3 : (Real.sin (2 * θ)) ^ 5 ≤ (Real.sin (2 * θ)) ^ 3 :=
      pow_le_pow_of_le_one hb0 hb1 (by norm_num)
    linarith
  have hA5r : (Real.sin θ * Real.cos θ ^ 2) ^ (5:ℝ) ≤ (Real.sin (2 * θ)) ^ (3:ℝ) := by
    simpa using hA5
  -- raise to the power `α/15 ≥ 0`
  have h1 : (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3)
      = ((Real.sin θ * Real.cos θ ^ 2) ^ (5:ℝ)) ^ (α / 15) := by
    rw [← Real.rpow_mul hA0 5 (α / 15), show (5:ℝ) * (α / 15) = α / 3 by ring]
  have h2 : ((Real.sin (2 * θ)) ^ (3:ℝ)) ^ (α / 15) = (Real.sin (2 * θ)) ^ (α / 5) := by
    rw [← Real.rpow_mul hb0 3 (α / 15), show (3:ℝ) * (α / 15) = α / 5 by ring]
  have h3 : ((Real.sin θ * Real.cos θ ^ 2) ^ (5:ℝ)) ^ (α / 15)
      ≤ ((Real.sin (2 * θ)) ^ (3:ℝ)) ^ (α / 15) :=
    Real.rpow_le_rpow (Real.rpow_nonneg hA0 5) hA5r (by linarith)
  rw [← h1, h2] at h3
  simp only [Work.Spaces.Gam]
  exact h3

end Work.FTS.LocData
