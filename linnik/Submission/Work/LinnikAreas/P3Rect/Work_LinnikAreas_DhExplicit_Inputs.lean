import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.LinnikAreas.DhK.Defs

/-!
# `Work.LinnikAreas.DhExplicit.Inputs`

The two analytic inputs of the Turán route to the Deuring–Heilbronn repulsion (Kadiri–Ng–Wong,
arXiv:1902.08640, §2), together with the technical consequence that a real zero of a real
character with `λ ≤ 1/100` forces the conductor to be large.
-/

namespace Work.LinnikAreas.DhExplicit

open Work.LinnikContract

/-- The inverse-square zero-sum bound (KNW Lemma 2.6) for the zeros of `ζ_K = ζ · L(·,χ)`. -/
def MassBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (w : ℂ) (hw : (3 / 2 : ℝ) ≤ w.re),
    Summable (fun u : ℂ => ((DhK.kMult χ u : ℕ) : ℝ) / ‖w - u‖ ^ 2) ∧
      (∑' u : ℂ, ((DhK.kMult χ u : ℕ) : ℝ) / ‖w - u‖ ^ 2)
        ≤ C * (Real.log (q : ℝ) + Real.log (2 + ‖w‖) + 2)

/-- The differentiated explicit formula (KNW (2.5)–(2.6)), inequality form. -/
def ExplFormula : Prop :=
  ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) (hχ2 : χ ^ 2 = 1) (j : ℕ) (hj : 1 ≤ j) (c γ' : ℝ) (hc : 5 ≤ c)
    {β₁ : ℝ} (hβ₁ : β₁ < 1)
    (hz₁ : DirichletCharacter.completedLFunction χ (β₁ : ℂ) = 0),
    Summable (fun u : ℂ => ((DhK.kMult χ u : ℕ) : ℝ) *
          ((1 / ((c : ℂ) - u) ^ (2 * j)).re
            + (1 / ((c : ℂ) + Complex.I * (γ' : ℂ) - u) ^ (2 * j)).re)) ∧
    4 * (j : ℝ) * (1 - β₁) / (c - 1) ^ (2 * j + 1) ≥
      (∑' u : ℂ, ((DhK.kMult χ u : ℕ) : ℝ) *
          ((1 / ((c : ℂ) - u) ^ (2 * j)).re
            + (1 / ((c : ℂ) + Complex.I * (γ' : ℂ) - u) ^ (2 * j)).re))
        - ((DhK.kMult χ (β₁ : ℂ) : ℕ) : ℝ)
          * ((1 / ((c : ℂ) - (β₁ : ℂ)) ^ (2 * j)).re
              + (1 / ((c : ℂ) + Complex.I * (γ' : ℂ) - (β₁ : ℂ)) ^ (2 * j)).re)

/-- A real zero of a real character with `λ ≤ 1/100` forces a large conductor. -/
def ConductorLarge : Prop :=
  ∀ Q : ℕ, ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
    ∀ [NeZero q] (χ₀ : DirichletCharacter ℂ q) (ρ₀ : ℂ),
    χ₀ ≠ 1 → χ₀ ^ 2 = 1 → ρ₀.im = 0 → zeroMult χ₀ ρ₀ ≠ 0 →
    lamOf q ρ₀ ≤ 1 / 100 → Q ≤ χ₀.conductor

end Work.LinnikAreas.DhExplicit
