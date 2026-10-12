import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.pairGc21FderivV2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

theorem pairGc21_fderiv {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    {Θ₀ : Work.BoseDict.Xn n → ℂ} {A : EuclideanSpace ℝ (Fin 3) → ℂ} {cA : ℝ}
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀) (hA : Measurable A) (hAb : ∀ x, ‖A x‖ ≤ cA)
    (hcA : 0 ≤ cA) :
    (∀ z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
        DifferentiableAt ℝ (fun u' => pairGc21 ℓ p hp Θ₀ A u' z.2) z.1)
    ∧ (∀ (z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) (j : Fin 3),
        fderiv ℝ (fun u' => pairGc21 ℓ p hp Θ₀ A u' z.2) z.1
            (EuclideanSpace.single j (1 : ℝ))
          = ∫ z' in triBox ℓ p,
              (star (Θ₀ (insertCoord2 p z'.1.1 z'.1.2 z'.2)) * A z'.1.1 * A z'.1.2)
                * fderiv ℝ Θ₀ (insertCoord2 p z.2 z.1 z'.2) (slotDirVec p.2 j)) := by
  exact pairGc21FderivV2 hℓ p hp hΘ₀ hA hAb hcA

end Work.BoseBoxFock
