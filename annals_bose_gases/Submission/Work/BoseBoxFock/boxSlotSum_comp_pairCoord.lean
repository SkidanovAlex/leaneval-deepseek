import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.boxSlotSum_comp_sectorPointwise
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

theorem boxSlotSum_comp_pairCoord {m n : ℕ} (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ)
    (T₁ T₂ : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (S : Finset (Fin n))
    (Φ : Work.BoseDict.Xn n → ℂ)
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (horth : ∀ l l', (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (hint : ∀ l l', MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) => star (e l z) * e l' z))
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ)
    (u : {i // i ∈ S} → EuclideanSpace ℝ (Fin 3))
    (y : {i // i ∉ S} → EuclideanSpace ℝ (Fin 3)) :
    (Work.BoseDict.boxSlotSum e T₁
        (Work.BoseDict.boxSlotSum e T₂ (Work.BoseBoxFock.slotExact e S Φ)))
      (Work.BoseBoxFock.pairCoord S u y)
      = Work.BoseBoxFock.slotSumSub e T₁ S
          (Work.BoseBoxFock.slotSumSub e T₂ S (Work.BoseBoxFock.sectorSlice e S Φ y)) u := by
  classical
  obtain ⟨hΘm, hΘb, -⟩ :=
    slotExact_measurable_bounded_compactSupport e he hec S Φ hΦ hΦc
  obtain ⟨hΨm, hΨb⟩ :=
    boxSlotSum_measurable_bounded e he hec T₂ (slotExact e S Φ) hΘm hΘb
  have hΨ0 : ∀ j : Fin n, j ∉ S →
      slotProj1 e j (Work.BoseDict.boxSlotSum e T₂ (slotExact e S Φ)) = 0 := by
    intro j hj
    rw [boxSlotSum_slotProj1_comm e he hec horth hint T₂ (slotExact e S Φ) hΘm hΘb j]
    rw [slotProj1_slotExact_eq_zero e he hec horth S j hj Φ hΦ.measurable
      (hΦ.bounded_above_of_compact_support hΦc)]
    exact boxSlotSum_zero e he hec T₂
  rw [boxSlotSum_pairCoord_gen e T₁ S _ he hec horth hint hΨm hΨb hΨ0 u y]
  congr 1
  funext u'
  exact boxSlotSum_pairCoord e T₂ S Φ he hec horth hint hΦ hΦc u' y

end Work.BoseBoxFock
