import Mathlib
import Submission.Work.Interfaces.Parabolic

/-!
# `Work.L62.StabHyp` — the head-stability content of Shishikura's Lemma 6.2, as a hypothesis

`Work.L62.head_stability` (the finitely-many-inverse-branches / shadowing step of Lemma 6.2) is
proved separately.  `StabHyp d` is that statement *verbatim* with the `β₀, ζ, j₀, z, r` arguments
turned into leading `∀`-binders, so that the surrounding assembly (`Work.L62.head_package`) can be
built before/independently of it: if `Work.L62.head_stability` is available then
`head_stability d hd : StabHyp d` holds by definitional unfolding (the hypothesis `hd` does not
occur in the type).
-/

namespace Work.L62

open MandelDim

/-- The conclusion of `Work.L62.head_stability`. -/
def StabHyp {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D) : Prop :=
  ∀ (β₀ : ℂ) (j₀ : ℕ), 0 < j₀ → ∀ (ζ : ℂ) (z : ℕ → ℂ), z 0 = ζ →
    (∀ j : ℕ, 1 ≤ j → j ≤ j₀ → z j ∈ d.DE ∧ d.E (z j) - β₀ = z (j - 1) ∧ deriv d.E (z j) ≠ 0) →
    ∀ r : ℝ, 0 < r → r < 1 / 8 →
      (⋃ j ∈ Finset.Icc 1 j₀, Metric.closedBall (z j) (2 * r)) ⊆ d.DE →
    ∃ (ρ₁ ε δ C C' : ℝ), 0 < ρ₁ ∧ ρ₁ ≤ r ∧ 0 < ε ∧ 0 < δ ∧ 0 < C ∧ 0 < C' ∧
      IsCompact (⋃ j ∈ Finset.Icc 1 j₀, Metric.closedBall (z j) (2 * r)) ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₁ → ∀ β : ℂ, ‖β - β₀‖ < ε →
        ∀ (R : ℂ → ℂ) (DR : Set ℂ), IsOpen DR →
          (⋃ j ∈ Finset.Icc 1 j₀, Metric.closedBall (z j) (2 * r)) ⊆ DR →
          DifferentiableOn ℂ R DR →
          (∀ w ∈ ⋃ j ∈ Finset.Icc 1 j₀, Metric.closedBall (z j) (2 * r), ‖R w - d.E w‖ < δ) →
          ∃ W : ℕ → Set ℂ, W 0 = Metric.ball ζ ρ ∧ ∀ j, j < j₀ →
            W (j + 1) ⊆ Metric.ball (z (j + 1)) r ∧ IsOpen (W (j + 1)) ∧ IsConnected (W (j + 1)) ∧
            Bornology.IsBounded (W (j + 1)) ∧
            Set.InjOn (fun u => R u - β) (W (j + 1)) ∧
            (fun u => R u - β) '' W (j + 1) = W j ∧
            ∀ u ∈ W (j + 1), C < ‖deriv ((fun u => R u - β)^[j + 1]) u‖ ∧
              ‖deriv ((fun u => R u - β)^[j + 1]) u‖ < C'

end Work.L62
