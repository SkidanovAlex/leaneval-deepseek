import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.abox_slice_peel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pb3_fubini_abox_boxL` — Fubini over the two finite boxes

The two boxes involved,

* `abox n ℓ` — the `n`-particle box `Λ(ℓ)^n ⊆ (Fin n → ℝ³)`,
* `boxL ℓ` — the corpus cube `Λ(ℓ) = ℓ • cell ⊆ ℝ³`,

are both measurable and of **finite** volume (`ℓ³ⁿ` and `ℓ³`), so for a measurable integrand
`F` that is bounded by a constant `C` both iterated integrals are honest and Fubini's theorem
`MeasureTheory.integral_integral_swap` may be applied to the product of the two *restricted*
measures:

    (volume ↾ abox n ℓ).prod (volume ↾ boxL ℓ) = (volume.prod volume) ↾ (abox n ℓ ×ˢ boxL ℓ).

The boundedness supplies integrability against this finite product measure
(`MeasureTheory.IntegrableOn.of_bound`), and the two iterated integrals in the statement are
definitionally the two iterated integrals of `integral_integral_swap`.

`sorry`-free.
-/

open MeasureTheory

namespace Work.BoseBoxFock

theorem pb3_fubini_abox_boxL {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {F : (Fin n → EuclideanSpace ℝ (Fin 3)) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (Fm : Measurable (Function.uncurry F)) {C : ℝ} (hC : ∀ x u, ‖F x u‖ ≤ C) :
    (∫ x in Submission.BoseGases.abox n ℓ, ∫ u in Work.BoseK15.corpusBox.boxL ℓ, F x u)
      = ∫ u in Work.BoseK15.corpusBox.boxL ℓ,
          ∫ x in Submission.BoseGases.abox n ℓ, F x u := by
  -- finiteness of the two boxes
  have hμs : (volume : Measure (Fin n → EuclideanSpace ℝ (Fin 3)))
      (Submission.BoseGases.abox n ℓ) < ⊤ :=
    Submission.BoseGases.abox_lt_top n ℓ hℓ.le
  have hνt : (volume : Measure (EuclideanSpace ℝ (Fin 3)))
      (Work.BoseK15.corpusBox.boxL ℓ) < ⊤ := by
    rw [Work.BoseB4.BoxData.volume_boxL _ hℓ]
    exact ENNReal.ofReal_lt_top
  have hfin : (((volume : Measure (Fin n → EuclideanSpace ℝ (Fin 3))).prod
        (volume : Measure (EuclideanSpace ℝ (Fin 3))))
      ((Submission.BoseGases.abox n ℓ) ×ˢ (Work.BoseK15.corpusBox.boxL ℓ))) < ⊤ := by
    rw [MeasureTheory.Measure.prod_prod]
    exact ENNReal.mul_lt_top hμs hνt
  -- the bounded measurable integrand is integrable against the finite product measure
  have hAint : IntegrableOn (Function.uncurry F)
      ((Submission.BoseGases.abox n ℓ) ×ˢ (Work.BoseK15.corpusBox.boxL ℓ))
      (((volume : Measure (Fin n → EuclideanSpace ℝ (Fin 3))).prod
        (volume : Measure (EuclideanSpace ℝ (Fin 3))))) := by
    refine MeasureTheory.IntegrableOn.of_bound hfin ?_ C ?_
    · exact Fm.aestronglyMeasurable.restrict
    · exact Filter.Eventually.of_forall (fun z => hC z.1 z.2)
  -- transport to the product of the two restricted measures
  have hInt : Integrable (Function.uncurry F)
      (((volume : Measure (Fin n → EuclideanSpace ℝ (Fin 3))).restrict
          (Submission.BoseGases.abox n ℓ)).prod
        ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (Work.BoseK15.corpusBox.boxL ℓ))) := by
    rw [MeasureTheory.Measure.prod_restrict]
    exact hAint
  exact MeasureTheory.integral_integral_swap hInt

end Work.BoseBoxFock
