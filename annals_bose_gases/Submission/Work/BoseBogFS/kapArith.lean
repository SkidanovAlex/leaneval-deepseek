import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.BoseBogFS.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

open scoped BigOperators Real

theorem kapArith {Mode : Type*} [Fintype Mode]
    (chi Wk tau : Mode → ℝ) (W0 ρ μ ℓ a gHat0 δ' δ₁ δ₂ : ℝ)
    (hρ : 0 < ρ) (hℓ : 0 ≤ ℓ) (ha : 0 ≤ a)
    (hg0 : gHat0 = 8 * Real.pi * a)
    (hW0pos : 0 < W0) (hW0up : W0 ≤ 8 * Real.pi * a * (1 + δ'))
    (hδ'0 : 0 ≤ δ') (hδ'1 : δ' ≤ 1 / 2) (hδ₁0 : 0 ≤ δ₁) (hδ₁1 : δ₁ ≤ 1 / 2)
    (hδ₂0 : 0 ≤ δ₂) (hδ₂1 : δ₂ ≤ 1 / 2)
    (hchi : (∑ k : Mode, (chi k) ^ 2) ≤ 1 + δ₁)
    (hden : ∀ k : Mode, 2 * ρ * W0 * (1 - δ₂) ≤ tau k + 2 * ρ * (Wk k))
    (hpos : ∀ k : Mode, 0 < tau k + 2 * ρ * (Wk k)) :
    (∑ k : Mode, (1 / 2 : ℝ) * Work.BoseB6.bogKappaErr (tau k + ρ * (Wk k)) (ρ * (Wk k))
        ((ρ - μ) * W0 * chi k * Real.sqrt (ρ * ℓ ^ 3)))
      ≤ (ρ - μ) ^ 2 * (gHat0 / 2) * ℓ ^ 3 * (1 + 4 * (δ' + δ₁ + δ₂)) := by
  classical
  -- `bogKappaErr A B κ = 2κ²/(A+B)`, so the `k`-th summand is `κ_k²/(τ_k + 2ρ𝓦_k)`
  -- with `κ_k = (ρ-μ)W₀ χ_k √(ρℓ³)`.
  have hℓ3 : (0:ℝ) ≤ ℓ^3 := pow_nonneg hℓ 3
  have hg0nn : (0:ℝ) ≤ gHat0 := by rw [hg0]; positivity
  have hD : (0:ℝ) < 2*(1-δ₂) := by linarith
  have hsq1 : (0:ℝ) ≤ 1+δ₁ := by linarith
  -- **The per-mode bound.**  The denominator is bounded below by `hden`, so the whole
  -- summand is at most `(ρ-μ)²W₀χ_k²ℓ³ / (2(1-δ₂))`.
  have hper : ∀ k : Mode,
      (1/2) * Work.BoseB6.bogKappaErr (tau k + ρ*(Wk k)) (ρ*(Wk k))
          ((ρ-μ)*W0*(chi k)*Real.sqrt (ρ*ℓ^3))
        ≤ ((ρ-μ)^2 * W0 * (chi k)^2 * ℓ^3)/(2*(1-δ₂)) := by
    intro k
    have hTnn : 0 ≤ (ρ-μ)^2 * W0 * (chi k)^2 * ℓ^3 :=
      mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (le_of_lt hW0pos)) (sq_nonneg _)) hℓ3
    have hsq : (Real.sqrt (ρ*ℓ^3))^2 = ρ*ℓ^3 := Real.sq_sqrt (by positivity)
    have hκeq : ((ρ-μ)*W0*(chi k)*Real.sqrt (ρ*ℓ^3))^2
        = ((ρ-μ)^2 * W0 * (chi k)^2 * ℓ^3) * (ρ*W0) := by
      rw [mul_pow, mul_pow, mul_pow, hsq]; ring
    have hstep : (1/2) * Work.BoseB6.bogKappaErr (tau k + ρ*(Wk k)) (ρ*(Wk k))
          ((ρ-μ)*W0*(chi k)*Real.sqrt (ρ*ℓ^3))
        = ((ρ-μ)*W0*(chi k)*Real.sqrt (ρ*ℓ^3))^2 / (tau k + 2*ρ*(Wk k)) := by
      rw [Work.BoseB6.bogKappaErr]
      have hAB : (tau k + ρ*(Wk k)) + ρ*(Wk k) = tau k + 2*ρ*(Wk k) := by ring
      rw [hAB]; ring
    rw [hstep, div_le_div_iff₀ (hpos k) hD]
    calc ((ρ-μ)*W0*(chi k)*Real.sqrt (ρ*ℓ^3))^2 * (2*(1-δ₂))
        = ((ρ-μ)^2 * W0 * (chi k)^2 * ℓ^3) * (2*ρ*W0*(1-δ₂)) := by rw [hκeq]; ring
      _ ≤ ((ρ-μ)^2 * W0 * (chi k)^2 * ℓ^3) * (tau k + 2*ρ*(Wk k)) :=
          mul_le_mul_of_nonneg_left (hden k) hTnn
  -- **The sum.**  Factor the constant and apply the χ-normalisation `hchi`.
  have hsum : (∑ k : Mode, ((ρ-μ)^2 * W0 * (chi k)^2 * ℓ^3)/(2*(1-δ₂)))
      = ((ρ-μ)^2 * W0 * ℓ^3/(2*(1-δ₂))) * (∑ k : Mode, (chi k)^2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring_nf
  have hcoefnn : 0 ≤ (ρ-μ)^2 * W0 * ℓ^3/(2*(1-δ₂)) :=
    div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (le_of_lt hW0pos)) hℓ3) (le_of_lt hD)
  have hsumle : ((ρ-μ)^2 * W0 * ℓ^3/(2*(1-δ₂))) * (∑ k : Mode, (chi k)^2)
      ≤ ((ρ-μ)^2 * W0 * ℓ^3/(2*(1-δ₂))) * (1+δ₁) :=
    mul_le_mul_of_nonneg_left hchi hcoefnn
  -- **The `W₀`-row** `hW0up`.
  have hW : ((ρ-μ)^2 * W0 * ℓ^3/(2*(1-δ₂))) * (1+δ₁)
      ≤ ((ρ-μ)^2 * (gHat0*(1+δ')) * ℓ^3/(2*(1-δ₂))) * (1+δ₁) := by
    apply mul_le_mul_of_nonneg_right _ hsq1
    apply div_le_div_of_nonneg_right _ (le_of_lt hD)
    rw [hg0]
    calc (ρ-μ)^2 * W0 * ℓ^3 = W0 * ((ρ-μ)^2 * ℓ^3) := by ring
      _ ≤ (8*Real.pi*a*(1+δ')) * ((ρ-μ)^2 * ℓ^3) :=
          mul_le_mul_of_nonneg_right hW0up (mul_nonneg (sq_nonneg _) hℓ3)
      _ = (ρ-μ)^2 * (8*Real.pi*a*(1+δ')) * ℓ^3 := by ring
  -- **The pure-arithmetic core** `(1+δ')(1+δ₁) ≤ (1-δ₂)(1+4(δ'+δ₁+δ₂))`.
  have hprod : (1+δ')*(1+δ₁) ≤ (1-δ₂)*(1+4*(δ'+δ₁+δ₂)) := by
    nlinarith [mul_nonneg hδ'0 hδ₁0, mul_nonneg hδ'0 hδ₂0, mul_nonneg hδ₁0 hδ₂0,
      mul_nonneg hδ'0 (by linarith : (0:ℝ) ≤ 1/2 - δ₂),
      mul_nonneg hδ₁0 (by linarith : (0:ℝ) ≤ 1/2 - δ₂),
      mul_nonneg hδ₂0 (by linarith : (0:ℝ) ≤ 1/2 - δ₂)]
  have hC : 0 ≤ (ρ-μ)^2 * gHat0 * ℓ^3 :=
    mul_nonneg (mul_nonneg (sq_nonneg _) hg0nn) hℓ3
  have hfin : ((ρ-μ)^2 * (gHat0*(1+δ')) * ℓ^3/(2*(1-δ₂))) * (1+δ₁)
      ≤ (ρ-μ)^2 * (gHat0/2) * ℓ^3 * (1+4*(δ'+δ₁+δ₂)) := by
    have h1 : (ρ-μ)^2 * gHat0 * ℓ^3 * ((1+δ')*(1+δ₁))
        ≤ (ρ-μ)^2 * gHat0 * ℓ^3 * ((1-δ₂)*(1+4*(δ'+δ₁+δ₂))) :=
      mul_le_mul_of_nonneg_left hprod hC
    have hA : ((ρ-μ)^2 * (gHat0*(1+δ')) * ℓ^3/(2*(1-δ₂))) * (1+δ₁)
        = ((ρ-μ)^2 * (gHat0*(1+δ')) * ℓ^3 * (1+δ₁))/(2*(1-δ₂)) := by
      ring_nf
    rw [hA, div_le_iff₀ hD]
    nlinarith [h1]
  calc (∑ k : Mode, (1/2) * Work.BoseB6.bogKappaErr (tau k + ρ*(Wk k)) (ρ*(Wk k))
        ((ρ-μ)*W0*(chi k)*Real.sqrt (ρ*ℓ^3)))
      ≤ ∑ k : Mode, ((ρ-μ)^2 * W0 * (chi k)^2 * ℓ^3)/(2*(1-δ₂)) :=
        Finset.sum_le_sum fun k _ => hper k
    _ = ((ρ-μ)^2 * W0 * ℓ^3/(2*(1-δ₂))) * (∑ k : Mode, (chi k)^2) := hsum
    _ ≤ ((ρ-μ)^2 * W0 * ℓ^3/(2*(1-δ₂))) * (1+δ₁) := hsumle
    _ ≤ ((ρ-μ)^2 * (gHat0*(1+δ')) * ℓ^3/(2*(1-δ₂))) * (1+δ₁) := hW
    _ ≤ (ρ-μ)^2 * (gHat0/2) * ℓ^3 * (1+4*(δ'+δ₁+δ₂)) := hfin

end Work.BoseBogFS
