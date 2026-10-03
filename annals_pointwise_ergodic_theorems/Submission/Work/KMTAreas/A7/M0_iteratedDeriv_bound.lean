import Mathlib
import Submission.Work.KMTAreas.A7.M0DerivBound
import Submission.Work.KMTPlan.A6.M0_iteratedDeriv

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger

/-- **The iterated `(ξ₁,ξ₂)`-derivative bound for the §6 symbol difference `M₀`.**

The derivative `∂^{j₁}_{ξ₁}∂^{j₂}_{ξ₂} M₀` is the symbol difference `M0deriv` of
`ModelApproxM0Deriv.lean` (this is `Work.KMTPlan.A6.M0_iteratedDeriv`), and the sharp bound on it
is `M0DerivBound`.  Here the frequency scales `X₁ = 2^{k₁}`, `X₂ = 2^{d k₂}` of the statement are
substituted for the abstract `X₁, X₂` of `M0DerivBound`; both are `≥ 1`, so the hypotheses of
`M0DerivBound` are met. -/
theorem M0_iteratedDeriv_bound (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree) :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧
      ∀ (N q k₁ k₂ : ℕ) (β₁ β₂ : Work.Analysis.IonescuWainger.Circle) (ξ₁ ξ₂ : ℝ)
        (j₁ j₂ : ℕ),
        1 ≤ N → 1 ≤ q → q • β₁ = 0 → q • β₂ = 0 → j₁ ≤ 2 → j₂ ≤ 2 →
        |ξ₁| ≤ (2 : ℝ) ^ k₁ / (N : ℝ) →
        |ξ₂| ≤ (2 : ℝ) ^ (P.natDegree * k₂) / (N : ℝ) ^ P.natDegree →
        ‖iteratedDeriv j₁ (fun a : ℝ =>
            iteratedDeriv j₂ (fun b : ℝ => Work.KMTAreas.A7.M0 P N q β₁ β₂ a b) ξ₂) ξ₁‖
          ≤ C * ((2 : ℝ) ^ k₁ + (2 : ℝ) ^ (P.natDegree * k₂) + 1) ^ A * (q : ℝ) *
              ((N : ℝ) ^ j₁ * (N : ℝ) ^ (P.natDegree * j₂)) / (N : ℝ) := by
  obtain ⟨C, A, hCpos, hAnn, hC⟩ := M0DerivBound P hdeg
  refine ⟨C, A, hCpos, hAnn, ?_⟩
  intro N q k₁ k₂ β₁ β₂ ξ₁ ξ₂ j₁ j₂ hN hq hβ₁ hβ₂ hj₁ hj₂ hξ₁ hξ₂
  have hX₁ : (1 : ℝ) ≤ (2 : ℝ) ^ k₁ := one_le_pow₀ (n := k₁) (by norm_num)
  have hX₂ : (1 : ℝ) ≤ (2 : ℝ) ^ (P.natDegree * k₂) :=
    one_le_pow₀ (n := P.natDegree * k₂) (by norm_num)
  rw [Work.KMTPlan.A6.M0_iteratedDeriv P N q β₁ β₂ hj₁ hj₂ ξ₁ ξ₂]
  exact hC N q β₁ β₂ ξ₁ ξ₂ ((2 : ℝ) ^ k₁) ((2 : ℝ) ^ (P.natDegree * k₂)) j₁ j₂
    hN hq hj₁ hj₂ hX₁ hX₂ hβ₁ hβ₂ hξ₁ hξ₂

end Work.KMTAreas.A7
