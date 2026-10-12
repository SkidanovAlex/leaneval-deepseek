import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseDict.Defs3
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

theorem cIPn_boxSlotOf_two_slot_gen {m d : ℕ} {ℓ : ℝ}
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (w₁ v₁ w₂ v₂ : Fin m → ℝ) (i j : Fin d) (hij : i ≠ j)
    (Θ : Work.BoseDict.Xn d → ℂ) :
    Work.BoseDict.cIPn d Θ
        (Work.BoseDict.boxSlotOf e w₁ v₁ i (Work.BoseDict.boxSlotOf e w₂ v₂ j Θ))
      = ∫ x : Work.BoseDict.Xn d,
          ∫ s : EuclideanSpace ℝ (Fin 3),
            ∫ u : EuclideanSpace ℝ (Fin 3),
              (starRingEnd ℂ) (Θ x) * Work.BoseDict.etaOf e w₁ (x i)
                * (starRingEnd ℂ) (Work.BoseDict.etaOf e v₁ s) * Work.BoseDict.etaOf e w₂ (x j)
                * (starRingEnd ℂ) (Work.BoseDict.etaOf e v₂ u)
                * Θ (Function.update (Function.update x i s) j u) := by
  have hji : j ≠ i := fun h => hij h.symm
  simp only [Work.BoseDict.cIPn, Work.BoseDict.boxSlotOf, Function.update_apply, if_neg hji]
  simp only [← MeasureTheory.integral_const_mul, mul_assoc]

end Work.BoseBoxFock
