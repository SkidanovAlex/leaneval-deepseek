import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.Gen.n0EOpGood
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S.Gen

open MeasureTheory

set_option maxHeartbeats 800000

/-- **Integrability of the slot fibre of a `good` state.**  If `f` is measurable and bounded on
every ball, then its slot fibre `z ↦ f (x|i↦z)` is integrable over any `A ⊆ acube ℓ`:  the fibre
lies in the ball of radius `max ‖x‖ ℓ`, so `BddOnBalls` bounds it there, while `A` has finite
measure (`Work.BoseFixB1S.volume_A_lt_top`). -/
theorem integrableOn_slot_of_good {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (i : Fin N)
    {f : Submission.BoseGases.X N → ℝ} (hf : f ∈ good N)
    (x : Submission.BoseGases.X N) :
    IntegrableOn (fun z : EuclideanSpace ℝ (Fin 3) => f (Function.update x i z)) A volume := by
  obtain ⟨hfm, hfb⟩ := mem_good_iff.mp hf
  obtain ⟨C, hC⟩ := hfb (max ‖x‖ ℓ)
  refine IntegrableOn.of_bound (Work.BoseFixB1S.volume_A_lt_top hℓ hAc) ?_ C ?_
  · exact (hfm.comp (by fun_prop : Measurable (fun z : EuclideanSpace ℝ (Fin 3) =>
      Function.update x i z))).aestronglyMeasurable
  · rw [MeasureTheory.ae_restrict_iff' hA]
    filter_upwards with z hz
    rw [Real.norm_eq_abs]
    exact hC (Function.update x i z)
      (le_trans (norm_update_le x i z)
        (max_le_max le_rfl (norm_le_of_mem_acube hℓ.le (hAc hz))))

/-- **Pointwise additivity of `Pᵢ`** at a state whose two slot fibres are integrable; this is the
`x`-by-`x` form of the linearity of the Bochner integral over `A`. -/
theorem boxPInd_add_of_integrable {N : ℕ} (volA : ℝ) {A : Set (EuclideanSpace ℝ (Fin 3))}
    (i : Fin N) (x : Submission.BoseGases.X N) {f g : Submission.BoseGases.X N → ℝ}
    (hf : IntegrableOn (fun z : EuclideanSpace ℝ (Fin 3) => f (Function.update x i z)) A)
    (hg : IntegrableOn (fun z : EuclideanSpace ℝ (Fin 3) => g (Function.update x i z)) A) :
    Work.UBBInputs8.boxPInd volA A i (f + g) x
      = Work.UBBInputs8.boxPInd volA A i f x + Work.UBBInputs8.boxPInd volA A i g x := by
  have h : (∫ z in A, (f + g) (Function.update x i z))
      = (∫ z in A, f (Function.update x i z)) + ∫ z in A, g (Function.update x i z) := by
    rw [← MeasureTheory.integral_add hf hg]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with z
    rfl
  simp only [Work.UBBInputs8.boxPInd]
  rw [h]
  ring

theorem boxPInd_add_good {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (i : Fin N)
    {f g : Submission.BoseGases.X N → ℝ}
    (hf : f ∈ Work.BoseFixB1S.Gen.good N) (hg : g ∈ Work.BoseFixB1S.Gen.good N) :
    Work.UBBInputs8.boxPInd volA A i (f + g) =
      Work.UBBInputs8.boxPInd volA A i f + Work.UBBInputs8.boxPInd volA A i g := by
  ext x
  rw [Pi.add_apply,
    boxPInd_add_of_integrable volA i x
      (integrableOn_slot_of_good hℓ hA hAc i hf x)
      (integrableOn_slot_of_good hℓ hA hAc i hg x)]

end Work.BoseFixB1S.Gen
