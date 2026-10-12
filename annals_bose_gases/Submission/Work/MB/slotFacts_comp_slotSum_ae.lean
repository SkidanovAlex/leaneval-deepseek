import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.MB.boxSlotSum_comp_pairCoord_ae
import Submission.Work.MB.boxSlotSum_comp_sector_split_ae
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.MB

theorem slotFacts_comp_slotSum_ae {m n : ℕ} {ℓ : ℝ}
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (hint : ∀ l l', MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) => star (e l z) * e l' z))
    {Φc : Work.BoseDict.Xn n → ℂ} (hΦm : Measurable Φc) (hΦb : ∃ C, ∀ x, ‖Φc x‖ ≤ C)
    (hΦsupp : tsupport Φc ⊆ Submission.BoseGases.abox n ℓ)
    (T₁ T₂ : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) :
    Work.BoseBoxFock.SlotFacts e Φc
      (fun Θ : Work.BoseDict.Xn n → ℂ =>
        Work.BoseDict.boxSlotSum e T₁ (Work.BoseDict.boxSlotSum e T₂ Θ))
      (fun S X => Work.BoseBoxFock.slotSumSub e T₁ S (Work.BoseBoxFock.slotSumSub e T₂ S X)) := by
  classical
  -- the box support of the state, in the *product-of-corpus-boxes* form used by the weak slot
  -- calculus (valid for every `ℓ`, not only `0 < ℓ`)
  have hΦs : Function.support Φc ⊆ Work.MB.boxPow n ℓ :=
    Work.MB.support_subset_boxPow_of_tsupport hΦsupp
  refine ⟨?_, ?_, ?_⟩
  · -- ## `good`: the composite preserves measurable, everywhere bounded states
    intro X hX
    obtain ⟨hm, hb⟩ := boxSlotSum_measurable_bounded_ae hmeas hbdE hsupp T₂ X hX.1 hX.2
    exact boxSlotSum_measurable_bounded_ae hmeas hbdE hsupp T₁
      (Work.BoseDict.boxSlotSum e T₂ X) hm hb
  · -- ## `slice`: the pointwise decoupling on a sector
    intro S u y
    exact boxSlotSum_comp_pairCoord_ae hmeas hbdE hsupp horth hint T₁ T₂ S Φc hΦm hΦb
      hΦsupp u y
  · -- ## `split`: the sector splitting of the quadratic form
    have h := congrArg Complex.re
      (boxSlotSum_comp_sector_split_ae hmeas hbdE hsupp horth hint T₁ T₂ Φc hΦm hΦb hΦs)
    have hsum : (∑ S : Finset (Fin n), ∫ x : Work.BoseDict.Xn n,
          star (Work.BoseBoxFock.slotExact e S Φc x)
            * Work.BoseDict.boxSlotSum e T₁
                (Work.BoseDict.boxSlotSum e T₂ (Work.BoseBoxFock.slotExact e S Φc)) x).re
        = ∑ S : Finset (Fin n), (∫ x : Work.BoseDict.Xn n,
          star (Work.BoseBoxFock.slotExact e S Φc x)
            * Work.BoseDict.boxSlotSum e T₁
                (Work.BoseDict.boxSlotSum e T₂ (Work.BoseBoxFock.slotExact e S Φc)) x).re := by
      simp
    exact h.trans hsum

end Work.MB
