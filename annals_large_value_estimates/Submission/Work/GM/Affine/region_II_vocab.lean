import Mathlib
import Submission.Work.GM.Affine.region_II_defs
import Submission.Work.GM.Affine.ghat_poisson_expansion

/-!
# GM §9, region II: vocabulary for the reduction (9.6')

This file introduces the objects used to state the region-II reduction `Work.GM.Affine.region_II_reduction`
in a form adapted to the *Poisson/dual* representation of `ghat`:

* `Bsum f M₂ u = Σ_{m₂ ∈ R2 M₂} m₂ f̂(m₂ u)` is the `m₂`-sum; by definition
  `Hfun f M₂ M₃ ℓ τ = Bsum f M₂ (ℓ + τ/M₃)`;
* `Wsum K M₃ x = M₃ Σ_{ℓ∈ℤ} ψ̂₁(M₃(ℓ - x)) = Σ_{m₃∈R3ext} ψ₁(m₃/M₃) e(m₃ x)` is the (periodic)
  "resonance weight";
* `ghat` is the `m₁`-sum of `(1/|m₁|) Bsum(ξ/m₁) Wsum(ξ/m₁)`;
* `ghatRes` keeps only the ℓ within `2/M₃` of `ξ/m₁` ("resonant" pairs), `ghatFar` is the rest.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-- The `m₂`-sum `B(u) = Σ_{m₂ ∈ R2 M₂} m₂ f̂(m₂ u)`. -/
def Bsum (f : ℝ → ℝ) (M₂ u : ℝ) : ℂ :=
  ∑ m₂ ∈ R2 M₂, ((m₂ : ℝ) : ℂ) * Fhat f ((m₂ : ℝ) * u)

/-- `Hfun` is `Bsum` evaluated at `ℓ + τ/M₃`. -/
lemma Hfun_eq_Bsum (f : ℝ → ℝ) (M₂ M₃ : ℝ) (ℓ : ℤ) (τ : ℝ) :
    Hfun f M₂ M₃ ℓ τ = Bsum f M₂ ((ℓ : ℝ) + τ / M₃) := rfl

/-- The resonance weight `W(x) = M₃ Σ_ℓ ψ̂₁(M₃(ℓ-x))` (equal to `Σ_{m₃} ψ₁(m₃/M₃) e(m₃x)`). -/
def Wsum (K M₃ : ℝ) (x : ℝ) : ℂ :=
  (M₃ : ℂ) * ∑' ℓ : ℤ, psi1hat K (M₃ * ((ℓ : ℝ) - x))

/-- The right-hand side of the region-II reduction, without the constants:
`Σ_ℓ ∫_{|τ| ≤ 2} ‖H_ℓ(τ)‖² dτ`. -/
def WinMass (f : ℝ → ℝ) (M₂ M₃ : ℝ) : ℝ :=
  ∑' ℓ : ℤ, ∫ τ in Set.Icc (-2 : ℝ) 2, ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2

/-- The **resonant** part of `ghat`: only the pairs `(m₁, ℓ)` with `|ℓ - ξ/m₁| ≤ 2/M₃`. -/
def ghatRes (K M₁ M₂ M₃ : ℝ) (f : ℝ → ℝ) (ξ : ℝ) : ℂ :=
  ∑ m₁ ∈ R1 M₁, ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
    ((M₃ : ℂ) * ∑' ℓ : ℤ,
      if |(ℓ : ℝ) - ξ / (m₁ : ℝ)| ≤ 2 / M₃ then psi1hat K (M₃ * ((ℓ : ℝ) - ξ / (m₁ : ℝ))) else 0)

/-- The **far** part of `ghat`: the complement of `ghatRes`. -/
def ghatFar (K M₁ M₂ M₃ : ℝ) (f : ℝ → ℝ) (ξ : ℝ) : ℂ :=
  ghat K M₁ M₂ M₃ f ξ - ghatRes K M₁ M₂ M₃ f ξ

lemma ghat_eq_res_add_far (K M₁ M₂ M₃ : ℝ) (f : ℝ → ℝ) (ξ : ℝ) :
    ghat K M₁ M₂ M₃ f ξ = ghatRes K M₁ M₂ M₃ f ξ + ghatFar K M₁ M₂ M₃ f ξ := by
  simp [ghatFar]

/-- **Expansion of `ghat`** into the `m₁`-sum of `Bsum` and the resonance weight `Wsum`. -/
theorem ghat_eq_sum_Bsum_Wsum {K M₁ M₂ M₃ : ℝ} (hK : 0 < K) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (hM₃ : 0 < M₃) {f : ℝ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f) (ξ : ℝ) :
    ghat K M₁ M₂ M₃ f ξ =
      ∑ m₁ ∈ R1 M₁, ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
        Wsum K M₃ (ξ / (m₁ : ℝ)) := by
  rw [ghat_poisson_expansion hK hM₁ hM₂ hM₃ hf hcs ξ]
  refine Finset.sum_congr rfl fun m₁ hm₁ => ?_
  have hterm : ∀ m₂ ∈ R2 M₂,
      ((((m₂ : ℝ) / |(m₁ : ℝ)| : ℝ)) : ℂ) * Fhat f (ξ * (m₂ : ℝ) / (m₁ : ℝ))
        = ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * (((m₂ : ℝ) : ℂ) * Fhat f ((m₂ : ℝ) * (ξ / (m₁ : ℝ)))) := by
    intro m₂ _
    have harg : ξ * (m₂ : ℝ) / (m₁ : ℝ) = (m₂ : ℝ) * (ξ / (m₁ : ℝ)) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]; ring
    rw [harg, div_eq_mul_inv]
    push_cast
    ring
  have hsum : (∑ m₂ ∈ R2 M₂, ((((m₂ : ℝ) / |(m₁ : ℝ)| : ℝ)) : ℂ) * Fhat f (ξ * (m₂ : ℝ) / (m₁ : ℝ)))
      = ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ *
        (∑ m₂ ∈ R2 M₂, (((m₂ : ℝ) : ℂ) * Fhat f ((m₂ : ℝ) * (ξ / (m₁ : ℝ))))) := by
    rw [Finset.sum_congr rfl hterm, Finset.mul_sum]
  rw [← Finset.sum_mul, hsum, Wsum, Bsum]

end

end Work.GM.Affine
