import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.PerBoxNames
import Submission.Work.FockBridge.Count
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1

theorem integralSqSectorPiece {N : ℕ} {L : ℝ}
    {B : Set (EuclideanSpace ℝ (Fin 3))}
    {Φ w : Submission.BoseGases.X N → ℝ}
    (hint : ∀ k ∈ Finset.range (N + 1),
      MeasureTheory.IntegrableOn
        (fun x => (Work.FockBridge.sectorPiece B k Φ x) ^ 2 * w x)
        (Submission.BoseGases.abox N L)) :
    (∫ x in Submission.BoseGases.abox N L, (Φ x) ^ 2 * w x)
      = ∑ k ∈ Finset.range (N + 1),
          ∫ x in Submission.BoseGases.abox N L,
            (Work.FockBridge.sectorPiece B k Φ x) ^ 2 * w x := by
  -- pointwise: the sector pieces of `Φ` square-sum back to `Φ²` (the Fock/particle-number
  -- decomposition), and the weight `w` factors out of the finite sum
  have hpt : (fun x : Submission.BoseGases.X N => (Φ x) ^ 2 * w x)
      = fun x => ∑ k ∈ Finset.range (N + 1),
          (Work.FockBridge.sectorPiece B k Φ x) ^ 2 * w x := by
    funext x
    rw [← Finset.sum_mul, Work.FockBridge.sum_sectorPiece_sq]
  rw [hpt]
  exact MeasureTheory.integral_finsetSum (Finset.range (N + 1)) hint

end Work.BoseFixB1
