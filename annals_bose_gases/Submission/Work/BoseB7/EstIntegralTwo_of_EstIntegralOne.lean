import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseB7.Integral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7.EstIntegralTwo_of_EstIntegralOne`

FS `lem:EstimateIntegral` has two conclusions.  The first (`eq:CompIntegrals-Final`)
compares `ρ_zŴ₁ω(0)` with the `P_H`-sum `∑_{k∈P_H}Ŵ₁(k)α_k`; the second
(`eq:CompIntegrals-Final-2`) compares `Ŵ₁ω(0)` with `∑_{k∈P_H}Ŵ₁(k)²/(2𝒟_k)`.

The two are *the same inequality* at FS's parameter point, because on `P_H` one has
`ℬ_k = ρ_zŴ₁(k)` (`Bcoef`, i.e. `Q3Env.alpha`/`Q3Env.D` on the mode set), so that

  `Ŵ₁(k)α_k = Ŵ₁(k) · ℬ_k/(𝒜_k+√(𝒜_k²-ℬ_k²)) = ρ_zŴ₁(k)²/(2𝒟_k)`

(`𝒟_k = ½(𝒜_k+√(𝒜_k²-ℬ_k²))`, `α_k = ℬ_k/(𝒜_k+√(𝒜_k²-ℬ_k²))`) pointwise on `P_H`.
Summing and dividing the `ρ_z`-factor out of the left-hand side gives
`EstIntegralTwo` from `EstIntegralOne`, with the *same* constant `C1`.

## Contents

* `W1_mul_alpha_eq` — the pointwise identity `Ŵ₁(k)α_k = ρ_zŴ₁(k)²/(2𝒟_k)` on `P_H`.
* `EstIntegralTwo_of_EstIntegralOne` — the requested implication.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]

/-- **The pointwise identity behind FS `eq:CompIntegrals-Final-2`.**  On `P_H`,

  `Ŵ₁(k)α_k = ρ_zŴ₁(k)²/(2𝒟_k)`,

since `ℬ_k = ρ_zŴ₁(k)` there and `α_k = ℬ_k/(𝒜_k+√(𝒜_k²-ℬ_k²))`,
`2𝒟_k = 𝒜_k+√(𝒜_k²-ℬ_k²)`.  No positivity of the denominator is needed: both
sides are the same quotient, and if `𝒜_k+√(𝒜_k²-ℬ_k²) = 0` both vanish. -/
theorem W1_mul_alpha_eq (E : Q3Env Mode) {k : Mode} (hB : E.B k = E.rho * E.W1 k) :
    E.W1 k * E.alpha k = E.rho * (E.W1 k ^ 2 / (2 * E.D k)) := by
  simp only [Q3Env.alpha, Q3Env.D, Dcoef, alphaCoef, Submission.BoseGases.bogAlpha,
    Submission.BoseGases.bogD]
  rw [hB]
  ring_nf

/-- **FS `lem:EstimateIntegral`, second part from the first.**  If
`Ŵ₁ω(k)`-sum form `Ŵ₁(k)α_k` computes `ρ_zŴ₁ω(0)` to accuracy
`Cρ_za(μa³)^{5/12}K_H^{-1}` (`EstIntegralOne`), then the second-order sum
`Ŵ₁(k)²/(2𝒟_k)` computes `Ŵ₁ω(0)` to accuracy `Ca(μa³)^{5/12}K_H^{-1}`
(`EstIntegralTwo`), the `ρ_z` cancelling between `ℬ_k = ρ_zŴ₁(k)` and the
left-hand factor `ρ_zŴ₁ω(0)`. -/
theorem EstIntegralTwo_of_EstIntegralOne {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode)
    {C1 : ℝ} (hrho : 0 < E.rho)
    (hBrel : ∀ k ∈ F.PHset E, E.B k = E.rho * E.W1 k)
    (hOne : Work.BoseB7.EstIntegralOne F E C1) :
    Work.BoseB7.EstIntegralTwo F E C1 := by
  -- the pointwise `α ↔ 𝒟` identity on `P_H`
  have hterm : ∀ k ∈ F.PHset E,
      E.W1 k * E.alpha k = E.rho * (E.W1 k ^ 2 / (2 * E.D k)) := fun k hk =>
    W1_mul_alpha_eq E (hBrel k hk)
  -- hence the two sums differ by exactly the factor `ρ_z`
  have hsum : ∑ k ∈ F.PHset E, E.W1 k * E.alpha k
      = E.rho * ∑ k ∈ F.PHset E, E.W1 k ^ 2 / (2 * E.D k) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl hterm
  unfold EstIntegralOne at hOne
  unfold EstIntegralTwo
  rw [hsum] at hOne
  have hfac : E.rho * E.W1omega0 - E.rho * ∑ k ∈ F.PHset E, E.W1 k ^ 2 / (2 * E.D k)
      = E.rho * (E.W1omega0 - ∑ k ∈ F.PHset E, E.W1 k ^ 2 / (2 * E.D k)) := by ring
  rw [hfac, abs_mul, abs_of_pos hrho] at hOne
  have hrw : C1 * E.rho * E.aScat * dil E (5 / 12) * E.KH ^ (-(1 : ℝ))
      = E.rho * (C1 * E.aScat * dil E (5 / 12) * E.KH ^ (-(1 : ℝ))) := by ring
  rw [hrw] at hOne
  exact (mul_le_mul_iff_of_pos_left hrho).mp hOne

end Work.BoseB7
