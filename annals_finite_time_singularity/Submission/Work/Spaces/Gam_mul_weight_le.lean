import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The angular weight bound `α Γ(θ) sin(2θ)^{-α/5} / (α + sin(2θ)) ≤ 1`

This is the elementary pointwise estimate on the angular weight
`sin(2θ)^{-α/5} / (α + sin(2θ))` multiplying `Γ` in the `𝒲^{l,∞}`-norms of

T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
incompressible Euler equations on `ℝ³`*, Annals of Math. 194 (3) 2021.

## Mathematics

Write `s = sin θ`, `c = cos θ` and `A = s c²`, so that on `Iθ = [0, π/2]`
both are nonnegative, `Γ(θ) = A ^ (α/3)` and `sin(2θ) = 2 s c`.

The key pointwise inequality is `A ^ 5 ≤ (sin 2θ) ^ 3`: indeed
`A ^ 5 = (s² c⁷) · (s³ c³) ≤ s³ c³ ≤ 8 s³ c³ = (2 s c) ^ 3`, because
`0 ≤ s, c ≤ 1`.  Raising to the power `α/15 ≥ 0` gives `A ^ (α/3) ≤ (sin 2θ) ^ (α/5)`,
i.e. `Γ(θ) ≤ sin(2θ) ^ (α/5)`.  Multiplying by the nonnegative factor
`sin(2θ)^{-α/5}` and using `x ^ (α/5) * x ^ (-(α/5)) ≤ 1` (equality when
`x > 0`, and `0` when `x = 0`) yields `Γ(θ) sin(2θ)^{-α/5} ≤ 1`, hence
`α Γ(θ) sin(2θ)^{-α/5} ≤ α ≤ α + sin(2θ)`.  Dividing by the positive
denominator `α + sin(2θ)` gives the claim.
-/
open scoped Real

namespace Work.Spaces

theorem Gam_mul_weight_le (α θ : ℝ) (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    α * Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) ≤ 1 := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  -- Basic sign/bound facts for `sin θ` and `cos θ` on `Iθ`.
  have hs0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩
  have hc0 : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩
  have hs1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hc1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  -- The angular factor `A = sin θ · cos²θ`, so that `Γ(θ) = A ^ (α/3)`.
  set A : ℝ := Real.sin θ * Real.cos θ ^ 2 with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hGamA : Work.Spaces.Gam α θ = A ^ (α / 3) := by
    simp only [Work.Spaces.Gam]
    rw [hA]
  have he0 : 0 ≤ Real.sin (2 * θ) := by
    rw [Real.sin_two_mul]; positivity
  -- The numerical core: `A ^ 5 ≤ sin(2θ) ^ 3`.
  have hA5r : A ^ (5:ℝ) ≤ (Real.sin (2 * θ)) ^ (3:ℝ) := by
    have hm : A ^ 5 ≤ (Real.sin (2 * θ)) ^ 3 := by
      rw [hA, Real.sin_two_mul]
      have h1 : (Real.sin θ) ^ 2 * (Real.cos θ) ^ 7 ≤ 1 := by
        have a : (Real.sin θ) ^ 2 ≤ 1 := pow_le_one₀ (n := 2) hs0 hs1
        have b : (Real.cos θ) ^ 7 ≤ 1 := pow_le_one₀ (n := 7) hc0 hc1
        nlinarith [mul_le_mul a b (pow_nonneg hc0 7) (by norm_num : (0:ℝ) ≤ 1)]
      have hQ : 0 ≤ (Real.sin θ) ^ 3 * (Real.cos θ) ^ 3 := by positivity
      have step : ((Real.sin θ) ^ 2 * (Real.cos θ) ^ 7) * ((Real.sin θ) ^ 3 * (Real.cos θ) ^ 3)
          ≤ 1 * ((Real.sin θ) ^ 3 * (Real.cos θ) ^ 3) :=
        mul_le_mul_of_nonneg_right h1 hQ
      nlinarith [step, hQ, sq_nonneg (Real.sin θ * Real.cos θ)]
    simpa using hm
  -- Raising to the (nonnegative) power `α/15`: `Γ(θ) ≤ sin(2θ) ^ (α/5)`.
  have hGam : Work.Spaces.Gam α θ ≤ (Real.sin (2 * θ)) ^ (α / 5) := by
    have h1 : A ^ (α / 3) = (A ^ (5:ℝ)) ^ (α / 15) := by
      rw [← Real.rpow_mul hA0 5 (α / 15), show (5:ℝ) * (α / 15) = α / 3 by ring]
    have h2 : ((Real.sin (2 * θ)) ^ (3:ℝ)) ^ (α / 15) = (Real.sin (2 * θ)) ^ (α / 5) := by
      rw [← Real.rpow_mul he0 3 (α / 15), show (3:ℝ) * (α / 15) = α / 5 by ring]
    have h3 : (A ^ (5:ℝ)) ^ (α / 15) ≤ ((Real.sin (2 * θ)) ^ (3:ℝ)) ^ (α / 15) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hA0 5) hA5r (by linarith)
    rw [← h1, h2] at h3
    rwa [hGamA]
  -- `Γ(θ) · sin(2θ)^{-α/5} ≤ 1`.
  have hge : Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ (-(α / 5)) ≤ 1 := by
    have h1 : Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ (-(α / 5))
        ≤ (Real.sin (2 * θ)) ^ (α / 5) * (Real.sin (2 * θ)) ^ (-(α / 5)) :=
      mul_le_mul_of_nonneg_right hGam (Real.rpow_nonneg he0 _)
    have h2 : (Real.sin (2 * θ)) ^ (α / 5) * (Real.sin (2 * θ)) ^ (-(α / 5)) ≤ 1 := by
      rcases eq_or_lt_of_le he0 with h | h
      · rw [← h, Real.zero_rpow (by linarith : α / 5 ≠ 0),
            Real.zero_rpow (by linarith : -(α / 5) ≠ 0)]
        norm_num
      · rw [← Real.rpow_add h (α / 5) (-(α / 5)), show α / 5 + -(α / 5) = 0 by ring,
            Real.rpow_zero]
    linarith
  -- Multiply by `α` and divide by `α + sin(2θ) > 0`.
  have hnum : α * Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ (-(α / 5)) ≤ α := by
    have h := mul_le_mul_of_nonneg_left hge (le_of_lt hα)
    rw [mul_one] at h
    linarith [h]
  have hden : 0 < α + Real.sin (2 * θ) := by linarith
  have hfin : α / (α + Real.sin (2 * θ)) ≤ 1 := by
    rw [div_le_one hden]; linarith
  calc α * Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))
      ≤ α / (α + Real.sin (2 * θ)) := div_le_div_of_nonneg_right hnum (le_of_lt hden)
    _ ≤ 1 := hfin

end Work.Spaces
