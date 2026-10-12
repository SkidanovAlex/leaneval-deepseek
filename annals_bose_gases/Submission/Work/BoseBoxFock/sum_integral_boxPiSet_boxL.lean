import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.imgFibreEnergyDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory

/-- **Linearity of the finite sum under the two box integrals.**  The outer variable `x'` ranges
over the `n`-fold box `boxPiSet ι ℓ`, the inner variable `s` over the box `boxL ℓ`.  Since `Fin 3`
is finite, distributing the sum over the two integrals only needs the integrability of every
`h j` on the product of the two (compact) boxes; both boxes are compact, so a continuous `h j` is
integrable there. -/
theorem sum_integral_boxPiSet_boxL {ι : Type*} [Fintype ι] {ℓ : ℝ} (hℓ : 0 < ℓ)
    {h : Fin 3 → (ι → EuclideanSpace ℝ (Fin 3)) × EuclideanSpace ℝ (Fin 3) → ℝ}
    (hh : ∀ j, Continuous (h j)) :
    (∑ j : Fin 3, ∫ x' in Work.BoseBoxFock.boxPiSet ι ℓ,
        ∫ s in Work.BoseK15.corpusBox.boxL ℓ, h j (x', s))
      = ∫ x' in Work.BoseBoxFock.boxPiSet ι ℓ,
          ∫ s in Work.BoseK15.corpusBox.boxL ℓ, ∑ j : Fin 3, h j (x', s) := by
  -- `h j` is continuous, hence integrable on the product of the two compact boxes.
  have hInt : ∀ j : Fin 3, Integrable (h j)
      (((volume : Measure (ι → EuclideanSpace ℝ (Fin 3))).restrict
          (Work.BoseBoxFock.boxPiSet ι ℓ)).prod
        ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (Work.BoseK15.corpusBox.boxL ℓ))) := by
    intro j
    have hmp : ((volume : Measure (ι → EuclideanSpace ℝ (Fin 3))).restrict
          (Work.BoseBoxFock.boxPiSet ι ℓ)).prod
        ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (Work.BoseK15.corpusBox.boxL ℓ))
        = (volume : Measure
            ((ι → EuclideanSpace ℝ (Fin 3)) × EuclideanSpace ℝ (Fin 3))).restrict
            (Work.BoseBoxFock.boxPiSet ι ℓ
              ×ˢ Work.BoseK15.corpusBox.boxL ℓ) := by
      rw [Measure.prod_restrict, Measure.volume_eq_prod]
    rw [hmp]
    exact ((hh j).continuousOn).integrableOn_compact
      ((isCompact_boxPiSet hℓ).prod (Work.BoseK15.corpusBox.boxL_compact ℓ))
  -- Integrability of the sections `s ↦ h j (x', s)` (`x'` frozen).
  have hsec : ∀ (j : Fin 3) (x' : ι → EuclideanSpace ℝ (Fin 3)),
      Integrable (fun s => h j (x', s))
        ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (Work.BoseK15.corpusBox.boxL ℓ)) := by
    intro j x'
    exact (((hh j).comp (continuous_const.prodMk continuous_id)).continuousOn).integrableOn_compact
      (Work.BoseK15.corpusBox.boxL_compact ℓ)
  -- Integrability of the fibre integrals `x' ↦ ∫_s h j (x', s)` (Fubini on the product box).
  have hout : ∀ j : Fin 3,
      Integrable (fun x' => ∫ s in Work.BoseK15.corpusBox.boxL ℓ, h j (x', s))
        ((volume : Measure (ι → EuclideanSpace ℝ (Fin 3))).restrict
          (Work.BoseBoxFock.boxPiSet ι ℓ)) := by
    intro j
    exact (hInt j).integral_prod_left
  -- Pointwise, the inner integral of the sum is the sum of the inner integrals.
  have hinner : ∀ x' : ι → EuclideanSpace ℝ (Fin 3),
      (∫ s in Work.BoseK15.corpusBox.boxL ℓ, ∑ j : Fin 3, h j (x', s))
        = ∑ j : Fin 3, ∫ s in Work.BoseK15.corpusBox.boxL ℓ, h j (x', s) := by
    intro x'
    exact integral_finsetSum Finset.univ (fun j _ => hsec j x')
  have hstep : (∫ x' in Work.BoseBoxFock.boxPiSet ι ℓ,
        ∫ s in Work.BoseK15.corpusBox.boxL ℓ, ∑ j : Fin 3, h j (x', s))
      = ∫ x' in Work.BoseBoxFock.boxPiSet ι ℓ,
          ∑ j : Fin 3, ∫ s in Work.BoseK15.corpusBox.boxL ℓ, h j (x', s) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x' => ?_)
    exact hinner x'
  calc (∑ j : Fin 3, ∫ x' in Work.BoseBoxFock.boxPiSet ι ℓ,
        ∫ s in Work.BoseK15.corpusBox.boxL ℓ, h j (x', s))
      = ∑ j : Fin 3, ∫ x' in Work.BoseBoxFock.boxPiSet ι ℓ,
          (∫ s in Work.BoseK15.corpusBox.boxL ℓ, h j (x', s)) := rfl
    _ = ∫ x' in Work.BoseBoxFock.boxPiSet ι ℓ,
          ∑ j : Fin 3, ∫ s in Work.BoseK15.corpusBox.boxL ℓ, h j (x', s) :=
        (integral_finsetSum Finset.univ (fun j _ => hout j)).symm
    _ = ∫ x' in Work.BoseBoxFock.boxPiSet ι ℓ,
          ∫ s in Work.BoseK15.corpusBox.boxL ℓ, ∑ j : Fin 3, h j (x', s) := hstep.symm

end Work.BoseBoxFock
