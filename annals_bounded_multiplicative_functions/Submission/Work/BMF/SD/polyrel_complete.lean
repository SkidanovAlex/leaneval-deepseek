import Mathlib
import Submission.Work.BMF.SD.corr_shift

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.SD

/-- Completing a `PolyRel` relation: if `P₂` is replaced by a polynomial `pol'` that agrees with
`P₂` up to a degree-`≤ k` polynomial which is `Cη`-small on the *first* interval, and the second
interval is moved to a comparable one, then the relation persists with the accumulated constant
`C * C + C + 1 + Cη`.

The point is that the difference `η = pol' - P₂` may be absorbed into the `ε`-slot of `PolyRel`
(which is only required to have degree `≤ k` and be bounded by `C` on `I₁`), while the integrality
slot `γ` is left untouched — indeed `P₁ = ε + P₂ + γ = (ε - η) + pol' + γ`. -/
lemma polyrel_complete {k : ℕ} {C Cη : ℝ} {x₁ L₁ : ℝ} {P₁ : Polynomial ℝ} {x₂ L₂ x₂' L₂' : ℝ} {P₂ pol' : Polynomial ℝ} (h : Work.BMF.PolyRel k C 1 x₁ L₁ P₁ x₂ L₂ P₂) (hC : 0 < C) (hCη : 0 ≤ Cη) (hL₁ : 0 < L₁) (hL₂' : 0 < L₂') (h1 : L₂ ≤ C * L₂') (h2 : L₂' ≤ C * L₂) (h3 : |x₂ - x₂'| ≤ C * L₂) (hη : pol' - P₂ ∈ Polynomial.degreeLE ℝ (k : WithBot ℕ)) (hb : ∀ t ∈ Set.Icc x₁ (x₁ + L₁), |pol'.eval t - P₂.eval t| ≤ Cη) : Work.BMF.PolyRel k (C * C + C + 1 + Cη) 1 x₁ L₁ P₁ x₂' L₂' pol' := by
  have hL₂ : 0 < L₂ := by nlinarith [h2, hL₂', hC]
  have hb' : ∀ t ∈ Set.Icc x₁ (x₁ + L₁), |(pol' - P₂).eval t| ≤ Cη := by
    intro t ht
    rw [Polynomial.eval_sub]
    exact hb t ht
  have h' := Work.BMF.PolyRel.change_second' (δ := (1 : ℝ)) h hC hCη hL₁ hL₂ hL₂' h1 h2 h3 hη hb'
  convert h' using 2
  ring

end Work.BMF.SD
