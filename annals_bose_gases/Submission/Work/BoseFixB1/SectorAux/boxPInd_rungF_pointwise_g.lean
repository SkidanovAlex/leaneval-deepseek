import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.SectorAux.GoodStateSpectralPieces
import Submission.Work.BoseFixB1.boxPInd_rungF_pointwise
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1.SectorAux

/-- **Rung-`F` pointwise identity in the `GoodState` class.**

For `A ⊆ acube ℓ` of measure `volA`, a state `Φ` that is measurable and bounded on the analysis
box (`GoodState ℓ Φ`, here given as the pair `hΦm`, `hΦb`) and `x ∈ abox N ℓ`,

    Pᵢ(Σ_j P_jΦ) x = Σ_j P_j(PᵢΦ) x .

This is the `GoodState` counterpart of `Work.BoseFixB1.boxPInd_rungF_pointwise` (whose hypothesis
is `Continuous Φ`).  The proof is the same two ingredients, at the weaker regularity class: the
slot-linearity `Work.BoseFixB1.boxPInd_sum` (whose fibre-integrability side conditions follow from
`slotInt_of_bound`, `measurable_boxPInd`, `abs_boxPInd_le`) followed by the termwise commutation
`PᵢP_j = P_jPᵢ` (`Work.BoseFixB1S.boxPInd_boxPInd_comm_good`, stated for `GoodState`s); for
`j = i` the two sides are the identical expression `Pᵢ(PᵢΦ) x`. -/
theorem boxPInd_rungF_pointwise_g {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (i : Fin N) {Φ : Submission.BoseGases.X N → ℝ} (hΦm : Measurable Φ) {Cb : ℝ}
    (hΦb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ Cb) :
    ∀ x ∈ Submission.BoseGases.abox N ℓ,
      Work.UBBInputs8.boxPInd volA A i
          (fun y => ∑ j : Fin N, Work.UBBInputs8.boxPInd volA A j Φ y) x
        = ∑ j : Fin N,
            Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x := by
  intro x hx
  have hgood : Work.BoseFixB1S.GoodState ℓ Φ := ⟨hΦm, Cb, hΦb⟩
  have hint : ∀ j : Fin N,
      MeasureTheory.IntegrableOn
        (fun z => Work.UBBInputs8.boxPInd volA A j Φ (Function.update x i z)) A MeasureTheory.volume :=
    fun j => Work.BoseFixB1S.slotInt_of_bound hℓ hA hAc i x hx
      (Work.BoseFixB1S.measurable_boxPInd volA A hA j hΦm)
      (Work.BoseFixB1S.abs_boxPInd_le hℓ hvol hA hvolA hAc j hΦb)
  rw [Work.BoseFixB1.boxPInd_sum volA A i x (fun j => Work.UBBInputs8.boxPInd volA A j Φ) hint]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases hji : j = i
  · subst hji; rfl
  · exact (Work.BoseFixB1S.boxPInd_boxPInd_comm_good hℓ hvol hA hvolA hAc (Ne.symm hji)
      hgood x hx).symm

end Work.BoseFixB1.SectorAux
