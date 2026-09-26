import Mathlib
import Submission.Work.Asymptotics.Compact.kplus8_tail_core
import Submission.Work.Asymptotics.Compact.kminus_tail_core
import Submission.Work.Asymptotics.funnelTailBasic

/-!
# Clearing the `K₊`-correction `Φ` of the funnel bracket

The `K₊`-side of the funnel deviation is

  `K₊^{(8)} - 𝒢₊^{(8)} = tailC⁻¹ (Φ₁ + Φ₂ + Φ₃)`

(`Compact.KPlus8_sub_Gplus8_decomp`), where

  `Φ₂ = φ₂(τ)E₁₄(τ)z² / (Δ(τ)(j(τ) - j(z)))`,
  `Φ₃ = (τE₆(τ)·phitVec z 2·(E₈(z)-E₄(z)³+Δ(z)j(τ))
          - 2φ₀(τ)E₄(τ)·phitVec z 1·(E₁₀(z)-E₄(z)³+Δ(z)j(τ))) / (Δ(z)(j(τ)-j(z)))`

carry the pole `1/(j(τ)-j(z)) = -Δ(z)/Sh(τ,z)`.  Multiplying by the clearing factor
`Δ(τ)·Sh(τ,z) = Δ(τ)E₄(z)³ - Δ(z)E₄(τ)³` removes it:

  `Δ(τ)Sh(τ,z)·Φ₂ = -φ₂(τ)E₁₄(τ)z²Δ(z)`,
  `Δ(τ)Sh(τ,z)·Φ₃ = -Δ(τ)·(τE₆(τ)·phitVec z 2·(E₈(z)-E₄(z)³+Δ(z)j(τ))
      - 2φ₀(τ)E₄(τ)·phitVec z 1·(E₁₀(z)-E₄(z)³+Δ(z)j(τ)))`.

Both are identities in the *atoms* `φ₂, φ₀, E₄, E₆, E₈, E₁₀, E₁₄, Δ(τ), j(τ), Δ(z), E₄(z)`, with
every division cleared: they are the entry point of the "direct calculation" of the `E(z)ᵏ`
coefficients of the cleared residual `Δ(τ)Sh(τ,z)·(Kdev8Bracket - 2·KdevE2·E(z)²)`. -/

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

open Work.Kernels

/-- `Sh τ z = -Δ(z)(j(τ) - j(z))`, so `1/(j(τ)-j(z)) = -Δ(z)/Sh(τ,z)` when `Sh ≠ 0`. -/
lemma inv_J_eq (τ z : ℍ) (hS : Work.Asymptotics.Compact.Sh τ z ≠ 0) :
    (jInvariantFun τ - jInvariantFun z)⁻¹
      = -(DeltaFun z) * (Work.Asymptotics.Compact.Sh τ z)⁻¹ := by
  have hΔ : DeltaFun z ≠ 0 := ClassicalFacts.DeltaFun_ne_zero z
  have hJ : jInvariantFun τ - jInvariantFun z ≠ 0 := by
    intro h
    exact hS (by rw [Work.Asymptotics.Compact.Sh_eq τ z, h, mul_zero, neg_zero])
  have h1 : Work.Asymptotics.Compact.Sh τ z
      = -(DeltaFun z * (jInvariantFun τ - jInvariantFun z)) :=
    Work.Asymptotics.Compact.Sh_eq τ z
  rw [h1, inv_neg, mul_inv]
  field_simp

/-- Clearing the pole of `Φ₂`. -/
theorem Delta_mul_Sh_mul_PhiDiv (τ z : ℍ) (hS : Work.Asymptotics.Compact.Sh τ z ≠ 0) :
    DeltaFun τ * Work.Asymptotics.Compact.Sh τ z * Work.Asymptotics.Compact.PhiDiv τ z
      = -(phi2 τ * E14Fun τ * (z : ℂ) ^ 2 * DeltaFun z) := by
  have hΔτ : DeltaFun τ ≠ 0 := ClassicalFacts.DeltaFun_ne_zero τ
  have hΔz : DeltaFun z ≠ 0 := ClassicalFacts.DeltaFun_ne_zero z
  rw [Work.Asymptotics.Compact.PhiDiv, div_eq_mul_inv, mul_inv, inv_J_eq τ z hS]
  field_simp

/-- Clearing the pole of `Φ₃`. -/
theorem Delta_mul_Sh_mul_PhiCorr (τ z : ℍ) (hS : Work.Asymptotics.Compact.Sh τ z ≠ 0) :
    DeltaFun τ * Work.Asymptotics.Compact.Sh τ z * Work.Asymptotics.Compact.PhiCorr τ z
      = -(DeltaFun τ * ((τ : ℂ) * E6Fun τ * Work.Kernels.phitVec z 2
            * (E8Fun z - E4Fun z ^ 3 + DeltaFun z * jInvariantFun τ)
          - 2 * phi0 τ * E4Fun τ * Work.Kernels.phitVec z 1
            * (E10Fun z - E4Fun z ^ 3 + DeltaFun z * jInvariantFun τ))) := by
  have hΔz : DeltaFun z ≠ 0 := ClassicalFacts.DeltaFun_ne_zero z
  have hJ : jInvariantFun τ - jInvariantFun z ≠ 0 := by
    intro h
    exact hS (by rw [Work.Asymptotics.Compact.Sh_eq τ z, h, mul_zero, neg_zero])
  rw [Work.Asymptotics.Compact.PhiCorr, div_eq_mul_inv, mul_inv, inv_J_eq τ z hS]
  field_simp

/-- **The cleared `K₊`-correction.**  Multiplying `Φ₁+Φ₂+Φ₃` by the clearing factor
`Δ(τ)Sh(τ,z) = Δ(τ)E₄(z)³ - Δ(z)E₄(τ)³` gives a denominator-free expression in the atoms,
which is the starting point of the `E(z)⁴`-coefficient computation. -/
theorem Delta_mul_Sh_mul_PhiSum (τ z : ℍ) (hS : Work.Asymptotics.Compact.Sh τ z ≠ 0) :
    DeltaFun τ * Work.Asymptotics.Compact.Sh τ z
        * (Work.Asymptotics.Compact.PhiMain τ z + Work.Asymptotics.Compact.PhiDiv τ z
            + Work.Asymptotics.Compact.PhiCorr τ z)
      = (DeltaFun τ * E4Fun z ^ 3 - DeltaFun z * E4Fun τ ^ 3)
          * Work.Asymptotics.Compact.PhiMain τ z
        - phi2 τ * E14Fun τ * (z : ℂ) ^ 2 * DeltaFun z
        - DeltaFun τ * ((τ : ℂ) * E6Fun τ * Work.Kernels.phitVec z 2
              * (E8Fun z - E4Fun z ^ 3 + DeltaFun z * jInvariantFun τ)
            - 2 * phi0 τ * E4Fun τ * Work.Kernels.phitVec z 1
              * (E10Fun z - E4Fun z ^ 3 + DeltaFun z * jInvariantFun τ)) := by
  have h1 := Delta_mul_Sh_mul_PhiDiv τ z hS
  have h2 := Delta_mul_Sh_mul_PhiCorr τ z hS
  have hSh : DeltaFun τ * Work.Asymptotics.Compact.Sh τ z
      = DeltaFun τ * E4Fun z ^ 3 - DeltaFun z * E4Fun τ ^ 3 := by
    rw [Work.Asymptotics.Compact.Sh, ← ClassicalFacts.DeltaFun_mul_jInvariantFun τ]
    ring
  have h3 : DeltaFun τ * Work.Asymptotics.Compact.Sh τ z
        * Work.Asymptotics.Compact.PhiMain τ z
      = (DeltaFun τ * E4Fun z ^ 3 - DeltaFun z * E4Fun τ ^ 3)
        * Work.Asymptotics.Compact.PhiMain τ z := by
    rw [hSh]
  rw [mul_add, mul_add, h3, h1, h2]
  ring

end

end Work.Asymptotics.KhatE1Core
