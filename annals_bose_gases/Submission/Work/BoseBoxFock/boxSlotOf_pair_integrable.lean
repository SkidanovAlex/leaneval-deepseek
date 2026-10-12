import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.slotPairDefs
import Submission.Work.MB.boxSlotSum_measurable_bounded_ae
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

theorem boxSlotOf_pair_integrable {m d : ℕ} {ℓ : ℝ} {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l))
    (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w₁ v₁ w₂ v₂ : Fin m → ℝ) (i j : Fin d)
    (Θ : (Fin d → EuclideanSpace ℝ (Fin 3)) → ℂ) (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow d ℓ) :
    MeasureTheory.Integrable (fun x : Fin d → EuclideanSpace ℝ (Fin 3) =>
      (starRingEnd ℂ) (Θ x) * Work.BoseDict.boxSlotOf e w₁ v₁ i
        (Work.BoseDict.boxSlotOf e w₂ v₂ j Θ) x) := by
  -- A single slot preserves measurability and everywhere boundedness at the weak mode bundle,
  -- so the double slot `boxSlotOf e w₁ v₁ i (boxSlotOf e w₂ v₂ j Θ)` does too.
  obtain ⟨hΘ'm, hΘ'b⟩ :=
    Work.MB.boxSlotOf_measurable_bounded_weak hmeas hbdd hsupp w₂ v₂ j Θ hΘm hΘb
  obtain ⟨hgm, hgb⟩ :=
    Work.MB.boxSlotOf_measurable_bounded_weak hmeas hbdd hsupp w₁ v₁ i
      (Work.BoseDict.boxSlotOf e w₂ v₂ j Θ) hΘ'm hΘ'b
  -- `Θ` is measurable, everywhere bounded and supported in the box `boxPow d ℓ`, which has
  -- finite measure; hence `star Θ * (double slot)` is integrable.
  obtain ⟨CΘ, hCΘ⟩ := hΘb
  obtain ⟨Cg, hCg⟩ := hgb
  refine Work.MB.integrable_of_bdd_of_support (S := Work.MB.boxPow d ℓ)
    (Work.MB.measurableSet_boxPow d ℓ) (Work.MB.volume_boxPow_lt_top d ℓ) ?_
    (C := max CΘ 0 * max Cg 0) ?_ ?_
  · exact ((Complex.continuous_conj.measurable.comp hΘm).mul hgm).aestronglyMeasurable
  · intro x
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul ((hCΘ x).trans (le_max_left _ _)) ((hCg x).trans (le_max_left _ _))
      (norm_nonneg _) (le_max_right _ _)
  · intro x hx
    rw [Function.notMem_support.mp (fun h => hx (hΘs h)), map_zero, zero_mul]

end Work.BoseBoxFock
