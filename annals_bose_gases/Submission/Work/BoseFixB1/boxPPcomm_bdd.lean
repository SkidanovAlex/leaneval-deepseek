import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1S.BoxPotOper
import Submission.Work.BoseFixB1S.boxPIndSelfAdjoint
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1

open MeasureTheory
open scoped Real BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

/-- **The two-slot mean is symmetric.** For a measurable state `f` bounded by `C` on the box,
the ordered double mean of `f` over `A × A` in the slots `i ≠ j` does not depend on the order
of the two slots.  (Measurable-bounded version of `Work.BoseFixB1S.twoMean_comm`, whose proof
uses continuity of the state only to bound it on the box.) -/
theorem twoMean_comm_bdd {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ)
    {A : Set E3} (hA : MeasurableSet A) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {i j : Fin N} (hij : i ≠ j) {f : Submission.BoseGases.X N → ℝ} (hfm : Measurable f)
    {C : ℝ} (hfb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |f x| ≤ C)
    {x : Submission.BoseGases.X N} (hx : x ∈ Submission.BoseGases.abox N ℓ) :
    Work.BoseFixB1S.twoMean volA A i j f x = Work.BoseFixB1S.twoMean volA A j i f x := by
  have hfin : (volume : Measure E3) A < ⊤ := Work.BoseFixB1S.volume_A_lt_top hℓ hAc
  haveI : IsFiniteMeasure ((volume : Measure E3).restrict A) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr (ne_of_lt hfin)
  -- The two-slot integrand of the swapped orientation is integrable on `A × A`.
  have hInt : MeasureTheory.Integrable
      (fun p : E3 × E3 => f (Function.update (Function.update x i p.1) j p.2))
      (((volume : Measure E3).restrict A).prod ((volume : Measure E3).restrict A)) := by
    refine MeasureTheory.Integrable.of_bound ?_ C ?_
    · exact (hfm.comp (by fun_prop :
        Measurable fun p : E3 × E3 =>
          Function.update (Function.update x i p.1) j p.2)).aestronglyMeasurable
    · have hae : ∀ᵐ p ∂(((volume : Measure E3).restrict A).prod
          ((volume : Measure E3).restrict A)), p ∈ A ×ˢ A := by
        rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.ae_restrict_iff' (hA.prod hA)]
        exact Filter.Eventually.of_forall (fun p hp => hp)
      filter_upwards [hae] with p hp
      rw [Real.norm_eq_abs]
      exact hfb _ (Work.BoseFixB1S.update_mem_abox' hAc
        (Work.BoseFixB1S.update_mem_abox' hAc hx i hp.1) j hp.2)
  -- Fubini, then the pointwise slot swap `Function.update_comm`.
  have hmain : (∫ z in A, ∫ w in A, f (Function.update (Function.update x i z) j w))
      = (∫ z in A, ∫ w in A, f (Function.update (Function.update x j z) i w)) := by
    rw [MeasureTheory.integral_integral_swap hInt]
    apply integral_congr_ae; filter_upwards with w
    apply integral_congr_ae; filter_upwards with z
    rw [Function.update_comm hij z w x]
  unfold Work.BoseFixB1S.twoMean
  rw [hmain]

/-- **The FS box projections commute in distinct slots.** For `i ≠ j` the two FS box
projections `Pᵢ = boxPInd V A i` commute pointwise on states measurable and bounded on the
box (the measurable-bounded form of `Work.BoseFixB1S.boxPInd_comm`). -/
theorem boxPPcomm_bdd {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {f : Submission.BoseGases.X N → ℝ} (hfm : Measurable f) {C : ℝ}
    (hfb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |f x| ≤ C)
    {i j : Fin N} (hij : i ≠ j) {x : Submission.BoseGases.X N}
    (hx : x ∈ Submission.BoseGases.abox N ℓ) :
    Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxPInd V A j f) x
      = Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxPInd V A i f) x := by
  have hcomm := twoMean_comm_bdd (volA := V) hℓ hA hAc hij hfm hfb hx
  rw [Work.BoseFixB1S.boxPInd_twoMean V A (i := i) (j := j) hij f x,
      Work.BoseFixB1S.boxPInd_twoMean V A (i := j) (j := i) hij.symm f x, hcomm]
  ring

end Work.BoseFixB1
