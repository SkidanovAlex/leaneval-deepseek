import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB1Cube.ConeC.BoseFixB1S_hopQIndDecomp
import Submission.Work.BoseB1Cube.ConeC.BoseFixB1_SectorAux_boxPairQCountMeas
import Submission.Work.BoseFixB1.SectorAux.GoodStateSpectralPieces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1.SectorAux

theorem hopQIndDecomp_g {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) {Φ : Submission.BoseGases.X N → ℝ}
    (hΦm : Measurable Φ) {Cb : ℝ}
    (hΦb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ Cb) (i : Fin N) :
    ∀ x ∈ Submission.BoseGases.abox N ℓ,
      Work.UBBInputs8.boxQInd volA A i Φ x
        = ∑ p ∈ (Work.BoseFixB1S.disjPairs N).filter (fun p => i ∈ p.2),
            Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x := by
  -- The `GoodState` (measurable + bounded on the analysis box) form of this identity is the
  -- bundled-hypothesis rendering of the requested statement; bundle the hypotheses and hand over.
  have hΦG : Work.BoseFixB1S.GoodState ℓ Φ :=
    ⟨hΦm, max Cb 0, fun x hx => le_trans (hΦb x hx) (le_max_left Cb 0)⟩
  exact Work.BoseFixB1.SectorAux.boxPairQCount_qdecompGood
    hℓ hvol hA hvolA hAc hΦG i

end Work.BoseFixB1.SectorAux
