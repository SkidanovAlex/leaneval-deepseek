import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.Nonlinear.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Γ(θ) · sin(2θ)^{-α/5} ≤ 1` on `Iθ`

This is the elementary pointwise angular estimate used throughout the `𝒲^{l,∞}`-norm
bounds of the `F_*`-package (see `Work.Spaces.Gam_mul_weight_le`, whose proof contains
exactly this estimate, and `Work.FTS.Nonlinear.FstarPkg.WlInf_Gamma_radial`).

## Mathematics

Write `s = sin θ`, `c = cos θ` and `A = s c²`; on `Iθ = [0, π/2]` both `s` and `c` lie
in `[0,1]`, `Γ(θ) = A ^ (α/3)` and `sin(2θ) = 2 s c`.  The numerical core is
`A ^ 5 ≤ sin(2θ) ^ 3`: indeed `A ^ 5 = (s² c⁷)(s³ c³) ≤ s³ c³ ≤ 8 s³ c³ = (2 s c)³`
because `0 ≤ s, c ≤ 1`.  Raising to the power `α/15 ≥ 0` gives `Γ(θ) ≤ sin(2θ) ^ (α/5)`,
and multiplying by the nonnegative factor `sin(2θ)^{-α/5}`, with
`x ^ (α/5) · x ^ (-(α/5)) ≤ 1` (equality for `x > 0`, and `0` for `x = 0`), gives the
claim.
-/

namespace Work.FTS.Nonlinear.FstarPkg

open scoped Real

/-- `sin(2θ) ≥ 0` on `Iθ = [0,π/2]`. -/
lemma sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  have hs0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ0, by linarith [Real.pi_pos]⟩
  have hc0 : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩
  rw [Real.sin_two_mul]
  positivity

/-- On `Iθ = [0,π/2]` the angular weight `Γ` is dominated by the corresponding power of
`sin(2θ)`: `Γ(θ) ≤ sin(2θ)^{α/5}`. -/
lemma Gam_le_sin_two_rpow {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.Gam α θ ≤ (Real.sin (2 * θ)) ^ (α / 5) := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  have hs0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ0, by linarith [Real.pi_pos]⟩
  have hc0 : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩
  have hs1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hc1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  set A : ℝ := Real.sin θ * Real.cos θ ^ 2 with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hGamA : Work.Spaces.Gam α θ = A ^ (α / 3) := by
    simp only [Work.Spaces.Gam]; rw [hA]
  have he0 : 0 ≤ Real.sin (2 * θ) := by rw [Real.sin_two_mul]; positivity
  -- The numerical core: `A ^ 5 ≤ sin(2θ) ^ 3`.
  have hA5r : A ^ (5 : ℝ) ≤ (Real.sin (2 * θ)) ^ (3 : ℝ) := by
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
  -- Raise to the nonnegative power `α/15`.
  have h1 : A ^ (α / 3) = (A ^ (5:ℝ)) ^ (α / 15) := by
    rw [← Real.rpow_mul hA0 5 (α / 15), show (5:ℝ) * (α / 15) = α / 3 by ring]
  have h2 : ((Real.sin (2 * θ)) ^ (3:ℝ)) ^ (α / 15) = (Real.sin (2 * θ)) ^ (α / 5) := by
    rw [← Real.rpow_mul he0 3 (α / 15), show (3:ℝ) * (α / 15) = α / 5 by ring]
  have h3 : (A ^ (5:ℝ)) ^ (α / 15) ≤ ((Real.sin (2 * θ)) ^ (3:ℝ)) ^ (α / 15) :=
    Real.rpow_le_rpow (Real.rpow_nonneg hA0 5) hA5r (by linarith)
  rw [← h1, h2] at h3
  rwa [hGamA]

theorem GamSinRpowMulLeOne {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ (-(α / 5)) ≤ 1 := by
  -- `α ≤ 1` is not needed for the estimate, but it is part of the requested interface.
  have _hα1 := hα1
  have he0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  have hGam : Work.Spaces.Gam α θ ≤ (Real.sin (2 * θ)) ^ (α / 5) :=
    Gam_le_sin_two_rpow hα hθ
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
  exact le_trans h1 h2

end Work.FTS.Nonlinear.FstarPkg
