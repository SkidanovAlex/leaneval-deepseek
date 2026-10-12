import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.boxM1Info
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.AprioriCount

theorem boxM1_eq_w1MassB {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {M : ℕ}
    (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
        (Submission.BoseGases.wSmall1Pair h M ℓ d u)
      = Work.BoseFixB1.w1MassB h M ℓ d u := by
  rw [Work.BoseFixB1.w1MassB]
  exact Work.BoseFixB1S.boxM1_eq_nested u (fun x y hxy =>
    Work.BoseFixB1S.wSmallPair_eq_zero_of_notMem_dlBox hM hℓ hd u hxy)

end Work.AprioriCount
