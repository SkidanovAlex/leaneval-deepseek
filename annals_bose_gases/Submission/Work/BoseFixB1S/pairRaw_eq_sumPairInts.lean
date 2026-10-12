import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.BoxPotFrag
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1S

set_option autoImplicit false
set_option maxHeartbeats 800000

theorem pairRaw_eq_sumPairInts {N : ℕ} (volA ℓ : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (w w1 w2 om : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (Φ : Submission.BoseGases.X N → ℝ) :
    Work.BoseFixB1S.pairRaw volA ℓ A w w1 w2 om Φ
      = ∑ p ∈ Submission.BoseGases.pairSet N,
          Work.BoseFixB1S.pairInts volA ℓ A w w1 w2 om Φ p.1 p.2 := by
  simp only [pairRaw, pairInts, fg0, fg1, fg2a, fg2b, fg2c, fg3, fg4, mul_assoc]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [integral_const_mul]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]

end Work.BoseFixB1S
