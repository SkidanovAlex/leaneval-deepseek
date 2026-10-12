import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PairGc21Bounds
import Submission.Work.BoseBoxFock.pairGc21_agree
import Submission.Work.BoseBoxFock.pairGc21_fderiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

theorem pairGc21_core {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    {Θ Θ₀ : Work.BoseDict.Xn n → ℂ} {A : EuclideanSpace ℝ (Fin 3) → ℂ} {cA : ℝ}
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀)
    (hΘ : ∀ x, Θ x = Set.indicator (Submission.BoseGases.abox n ℓ) Θ₀ x)
    (hA : Measurable A)
    (hAb : ∀ x, ‖A x‖ ≤ cA) (hcA : 0 ≤ cA) :
    (∀ u y : EuclideanSpace ℝ (Fin 3), u ∈ Work.BoseK15.corpusBox.boxL ℓ →
        y ∈ Work.BoseK15.corpusBox.boxL ℓ → pairG21 p Θ A u y = pairGc21 ℓ p hp Θ₀ A u y)
    ∧ Continuous (Function.uncurry (pairGc21 ℓ p hp Θ₀ A))
    ∧ (∀ z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
        DifferentiableAt ℝ (fun u' => pairGc21 ℓ p hp Θ₀ A u' z.2) z.1)
    ∧ (∀ u y : EuclideanSpace ℝ (Fin 3), ‖pairGc21 ℓ p hp Θ₀ A u y‖ ^ 2
          ≤ cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * memY21 ℓ p Θ₀ y u)
    ∧ (∀ z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3), ∑ j : Fin 3,
          ‖fderiv ℝ (fun u' => pairGc21 ℓ p hp Θ₀ A u' z.2) z.1
            (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
          ≤ cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * dirY21 ℓ p Θ₀ z.2 z.1) := by
  have hfd := pairGc21_fderiv hℓ p hp hΘ₀ hA hAb hcA
  refine ⟨pairGc21_agree hℓ p hp hΘ hΘ₀ hA hAb hcA,
    pairGc21_continuous hℓ p hp hΘ₀ hA hAb hcA, hfd.1, ?_, ?_⟩
  · intro u y
    exact pairGc21_mass_le hℓ p hp hΘ₀ hA hAb hcA u y
  · intro z
    exact pairGc21_dir_le_of_fderiv hℓ p hp hΘ₀ hA hAb hcA z.2 z.1 (fun j => hfd.2 z j)

end Work.BoseBoxFock
