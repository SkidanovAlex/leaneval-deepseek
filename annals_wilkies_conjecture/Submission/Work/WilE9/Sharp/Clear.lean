/-
  WilE9 / Sharp — clearing denominators for a *monomial* substitution.

  When the BNZ implicit-function data of a stratum is transported to coordinates in which the
  "unbounded" ambient variables are replaced by bounded ones (for E9: `xᵢ ↦ yᵢ / wᵢ` and
  `s ↦ τ / u`, where `yᵢ = ψ xᵢ`, `wᵢ = psig xᵢ`, `τ = ψ s`, `u = psig s` are all bounded by one),
  every polynomial identity acquires a common denominator `∏_{b:β} v(den b)^K`.

  `clearNumDen num den ρ K P` is the numerator: the polynomial obtained from `P` by substituting
  `X (Sum.inl b) ↦ X (num b) / X (den b)` and `X (Sum.inr c) ↦ X (ρ c)` and then multiplying by
  `∏_b X (den b)^K`.  The companion identity is proved in `WilE9/Sharp/clearNumDen_eval` and the
  degree bound in `WilE9/Sharp/clearNumDen_totalDegree_le`.
-/
import Mathlib

set_option autoImplicit false
noncomputable section
namespace Work.WilE9.Sharp

open MvPolynomial

/-- The numerator of `∏_{b:β} (X (den b))^K · P (X (Sum.inl b) ↦ X (num b)/X (den b))`.
The hypothesis needed to read it back is `P.totalDegree ≤ K`. -/
def clearNumDen {β γ α : Type*} [Fintype β] [Fintype γ] (num den : β → α) (ρ : γ → α)
    (K : ℕ) (P : MvPolynomial (β ⊕ γ) ℝ) : MvPolynomial α ℝ :=
  ∑ m ∈ P.support,
    C (P.coeff m) *
      (∏ b : β, X (num b) ^ (m (Sum.inl b)) * X (den b) ^ (K - m (Sum.inl b))) *
      (∏ c : γ, X (ρ c) ^ (m (Sum.inr c)))

end Work.WilE9.Sharp
