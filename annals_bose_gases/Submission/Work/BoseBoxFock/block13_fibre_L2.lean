import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.B13Final
import Submission.Work.BoseBoxFock.PotPairRowsAux
import Submission.Work.BoseBoxFock.fibre_kernel_free
import Submission.Work.BoseBoxFock.pinQ_kernel_expansion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

theorem block13_fibre_L2 {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    {Θ : Work.BoseDict.Xn n → ℂ} {A B : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hΘm : MeasureTheory.AEStronglyMeasurable Θ)
    (hΘL : MeasureTheory.Integrable (fun x => ‖Θ x‖ ^ 2))
    (hAm : MeasureTheory.AEStronglyMeasurable A)
    (hAL : MeasureTheory.Integrable (fun x => ‖A x‖ ^ 2))
    (hBm : MeasureTheory.AEStronglyMeasurable B)
    (hBL : MeasureTheory.Integrable (fun x => ‖B x‖ ^ 2)) :
    ∫ w : EuclideanSpace ℝ (Fin 3), ∫ y : EuclideanSpace ℝ (Fin 3),
        ‖∫ x' : {k : Fin n // k ≠ p.2} → EuclideanSpace ℝ (Fin 3), ∫ u : EuclideanSpace ℝ (Fin 3),
        (starRingEnd ℂ) (Θ (fun k => if h : k = p.2 then w else x' ⟨k, h⟩))
          * A ((fun k => if h : k = p.2 then w else x' ⟨k, h⟩) p.1)
          * (starRingEnd ℂ) (B u)
          * Θ (Function.update (Function.update
              (fun k => if h : k = p.2 then w else x' ⟨k, h⟩) p.1 y) p.2 u)‖ ^ 2
      ≤ (∫ x, ‖A x‖ ^ 2) * (∫ x, ‖B x‖ ^ 2) * (∫ x, ‖Θ x‖ ^ 2) ^ 2 := by
  exact block13_fibre_L2_aux p hp hΘm hΘL hAm hAL hBm hBL

end Work.BoseBoxFock
