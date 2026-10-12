import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.boxPIndSelfAdjoint
import Submission.Work.BoseFixB1S.peelPInd_pairMixed
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S.N0Out

open MeasureTheory
open scoped Real BigOperators

/-- **The ordered double sum of the box projections is the flat plus the pair count.**

`∑ᵢ∑ⱼ ∫ (PᵢΦ)(PⱼΦ)`: the diagonal `i = j` terms are `∫ (PᵢΦ)²` (the flat count `boxFlatCount`),
and on the off-diagonal `i ≠ j` the two-slot peel
`Work.BoseFixB1S.Q0C.pair_mixed_N` (both `Pᵢ` and `Pⱼ` carry the box indicator `1_A`, so the
slot means factorise and the `x i`- and `x j`-integrals produce the *same* double mean on each
side) turns `∫ (PᵢΦ)(PⱼΦ)` into `∫ (PᵢPⱼΦ)²`, which is the pair count `boxPairCount`.  The
bookkeeping `∑ᵢ∑ⱼ = ∑ᵢ + ∑_{p ∈ pairSet N}` (over ordered pairs, both orders) is
`Work.BoseFixB1S.Q0C.sum_univ_univ_eq`. -/
theorem pIndDoubleSumEq {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    (∑ i : Fin N, ∑ j : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        Work.UBBInputs8.boxPInd volA A i Φ x * Work.UBBInputs8.boxPInd volA A j Φ x)
      = Work.BoseFixB1S.boxFlatCount volA ℓ A Φ
        + Work.BoseFixB1S.boxPairCount volA ℓ A Φ := by
  rw [Work.BoseFixB1S.boxFlatCount, Work.BoseFixB1S.boxPairCount]
  rw [Work.BoseFixB1S.Q0C.sum_univ_univ_eq (fun i j : Fin N =>
    ∫ x in Submission.BoseGases.abox N ℓ,
      Work.UBBInputs8.boxPInd volA A i Φ x * Work.UBBInputs8.boxPInd volA A j Φ x)]
  congr 1
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    exact integral_congr_ae (ae_of_all _ (fun x => by ring))
  · refine Finset.sum_congr rfl (fun p hp => ?_)
    exact Work.BoseFixB1S.Q0C.pair_mixed_N (volA := volA) hℓ hvol hA hvolA hAc
      (Finset.mem_filter.mp hp).2 hΦc

end Work.BoseFixB1S.N0Out
