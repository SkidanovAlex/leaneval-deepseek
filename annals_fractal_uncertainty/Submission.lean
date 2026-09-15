import ChallengeDeps
import Submission.Helpers
import Submission.FUP.HSFinal
import Submission.FUP.Chain

open FractalUncertainty
open MeasureTheory FourierTransform Metric
open scoped ENNReal

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

namespace Submission

/-- **Cohen's Theorem 1.1** (`Fractal uncertainty in higher dimensions`, Annals of Math. 202
(2025), Theorem 1.1).

The proof runs through the reduction chain of `Submission/FUP/Chain.lean`: Han–Schlag's
Theorem 5.1 (`Submission.FUP.HSFinal.han_schlag_statement_of_localization`) is *proved* from
the single-scale localisation statement `Submission.FUP.LocalizationStatement` (Han–Schlag's
Corollary 4.2), and the higher-dimensional Beurling–Malliavin input of Cohen's §3 is proved in
`Submission/FUP/PSHToFourier*`.  The only remaining literature input of the whole development
is therefore `LocalizationStatement`, recorded as
`Submission.FUP.Spec.localization_statement_original`. -/
theorem theorem_1_1 (ν : ℝ) (hν₀ : 0 < ν) :
    ∃ (β C : ℝ), β > 0 ∧ C > 0 ∧ ∀ (h : ℝ) (X Y : Set ℝᵈ)
      (hX : MeasurableSet X) (hY : MeasurableSet Y), h ∈ Set.Ioo 0 (1 / 100) →
        X ⊆ cube (-1) 1 → PorousOnBalls ν h 1 X → Y ⊆ cube (-h⁻¹) h⁻¹ →
          PorousOnLines ν 1 h⁻¹ Y → ∀ (f : Lp ℂ 2), (𝓕 f : Lp ℂ 2) =ᵐ[volume.restrict Yᶜ] 0 →
            (eLpNorm (X.indicator f) 2).toReal ≤ C * h ^ β * ‖f‖ :=
  FUP.theorem_1_1_of_han_schlag_all (d := d)
    (FUP.han_schlag_statement_of_localization (d := d)
      (FUP.Spec.localization_statement_original (d := d))) ν hν₀

end Submission
