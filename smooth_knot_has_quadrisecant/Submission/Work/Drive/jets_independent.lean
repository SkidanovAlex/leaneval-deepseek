import Mathlib
import Submission.Work.Drive.knotPerturbDefs
import Submission.Work.Drive.jetDefs
import Submission.Work.Drive.jetF_zero_of_coeff
import Submission.Work.Drive.coeff_zero_of_jetFc
import Submission.Work.Drive.jetExp_ne_of_ne

/-!
# Independence of the six jet functionals

The six functionals (value and derivative at each of three pairwise distinct points of `[0, 2π)`)
are linearly independent on the space of trigonometric polynomials of degree at most `4`, spanned
by `trigBasis 0, …, trigBasis 8`.
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

noncomputable section

/-- **Independence of the six jet functionals** in coefficientwise form. -/
theorem jets_independent (p q r : ℝ) (hp : p ∈ Set.Ico 0 (2 * Real.pi))
    (hq : q ∈ Set.Ico 0 (2 * Real.pi)) (hr : r ∈ Set.Ico 0 (2 * Real.pi))
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (α β γ δ ε ζ : ℝ)
    (h : ∀ j : Fin 9, α * trigBasis j p + β * trigBasisD j p + γ * trigBasis j q
        + δ * trigBasisD j q + ε * trigBasis j r + ζ * trigBasisD j r = 0) :
    α = 0 ∧ β = 0 ∧ γ = 0 ∧ δ = 0 ∧ ε = 0 ∧ ζ = 0 :=
  coeff_zero_of_jetFc (jetExp p) (jetExp q) (jetExp r) (jetExp_ne_zero p) (jetExp_ne_zero q)
    (jetExp_ne_zero r) (jetExp_ne_of_ne p q hp hq hpq) (jetExp_ne_of_ne p r hp hr hpr)
    (jetExp_ne_of_ne q r hq hr hqr) α β γ δ ε ζ
    (fun k hk1 hk2 => jetF_zero_of_coeff p q r α β γ δ ε ζ h k hk1 hk2)

end

end Work.Drive
