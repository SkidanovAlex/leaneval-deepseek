import Mathlib
import Submission.Work.EKLComp.ErgMax.ShiftDefs

open MeasureTheory Topology Filter
open scoped ENNReal

namespace Work.EKLComp.ErgMax

open Work.EKLContract

/-- Integrating a bounded continuous function against the pushforward of `ν` under
`act (aDiag (shiftR u v))` gives `psi ν f u v`. -/
theorem integral_map_act_aDiag_shiftR (ν : MeasureTheory.Measure Work.EKLContract.X3)
    (f : BoundedContinuousFunction Work.EKLContract.X3 ℝ) (u v : ℝ) :
    (∫ x, f x ∂(ν.map (Work.EKLComp.ErgMax.act
        (Work.EKLContract.aDiag (Work.EKLComp.ErgMax.shiftR u v))))) =
      Work.EKLComp.ErgMax.psi ν f u v := by
  rw [integral_map (Measurable.aemeasurable (Work.EKLComp.ErgMax.measurable_act _))
      ((BoundedContinuousFunction.continuous f).aestronglyMeasurable)]
  simp only [Work.EKLComp.ErgMax.psi_apply, Work.EKLComp.ErgMax.act_apply,
    Work.EKLComp.ErgMax.aDiag_shiftR]

theorem integral_avg_map_sum (ν : MeasureTheory.Measure Work.EKLContract.X3)
    [MeasureTheory.IsFiniteMeasure ν]
    (f : BoundedContinuousFunction Work.EKLContract.X3 ℝ) (r s : ℝ) (N : ℕ) :
    (∫ x, f x ∂((Work.EKLComp.ErgMax.avg ν N).map
        (Work.EKLComp.ErgMax.act (Work.EKLContract.aPlus r s)))) =
      (((Work.EKLComp.ErgMax.n N * Work.EKLComp.ErgMax.n N : ℕ) : ℝ))⁻¹ *
        ∑ i : Fin (Work.EKLComp.ErgMax.n N), ∑ j : Fin (Work.EKLComp.ErgMax.n N),
          Work.EKLComp.ErgMax.psi ν f ((i : ℝ) / N + r) ((j : ℝ) / N + s) := by
  have hbdd : ∀ x : X3, ‖f x‖ ≤ ‖f‖ :=
    fun x => BoundedContinuousFunction.norm_coe_le_norm f x
  have hInt : ∀ u v : ℝ,
      Integrable f (ν.map (act (aDiag (shiftR u v)))) := fun u v =>
    Integrable.of_bound ((BoundedContinuousFunction.continuous f).aestronglyMeasurable)
      ‖f‖ (Filter.Eventually.of_forall hbdd)
  have hterm : ∀ u v : ℝ,
      (∫ x, f x ∂(ν.map (act (aDiag (shiftR u v))))) = psi ν f u v := fun u v =>
    integral_map_act_aDiag_shiftR ν f u v
  have hmap : (avg ν N).map (act (aPlus r s)) =
      (((n N * n N : ℕ) : ℝ≥0∞))⁻¹ • ∑ i : Fin (n N), ∑ j : Fin (n N),
        ν.map (act (aDiag (shiftR ((i : ℝ) / N + r) ((j : ℝ) / N + s)))) := by
    rw [avg_def, Measure.map_smul _ (measurable_act _).aemeasurable]
    congr 1
    rw [Measure.map_finset_sum' (measurable_act _).aemeasurable]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Measure.map_finset_sum' (measurable_act _).aemeasurable]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Measure.map_map (measurable_act _) (measurable_act _), ← act_mul,
      aPlus_mul_aDiag_shift]
  have hinner : ∀ i : Fin (n N),
      (∫ x, f x ∂(∑ j : Fin (n N),
          ν.map (act (aDiag (shiftR ((i : ℝ) / N + r) ((j : ℝ) / N + s))))))
        = ∑ j : Fin (n N), psi ν f ((i : ℝ) / N + r) ((j : ℝ) / N + s) := by
    intro i
    rw [integral_finsetSum_measure (s := Finset.univ) (f := (f : X3 → ℝ))
      (μ := fun j : Fin (n N) =>
        ν.map (act (aDiag (shiftR ((i : ℝ) / N + r) ((j : ℝ) / N + s)))))
      (fun j _ => hInt _ _)]
    exact Finset.sum_congr rfl (fun j _ => hterm _ _)
  rw [hmap, integral_smul_measure]
  rw [integral_finsetSum_measure (s := Finset.univ) (f := (f : X3 → ℝ))
    (μ := fun i : Fin (n N) => ∑ j : Fin (n N),
      ν.map (act (aDiag (shiftR ((i : ℝ) / N + r) ((j : ℝ) / N + s)))))
    (fun i _ => Integrable.of_bound
      ((BoundedContinuousFunction.continuous f).aestronglyMeasurable) ‖f‖
      (Filter.Eventually.of_forall hbdd))]
  rw [show (∑ i : Fin (n N), ∫ x, f x ∂(∑ j : Fin (n N),
          ν.map (act (aDiag (shiftR ((i : ℝ) / N + r) ((j : ℝ) / N + s))))))
        = ∑ i : Fin (n N), ∑ j : Fin (n N),
            psi ν f ((i : ℝ) / N + r) ((j : ℝ) / N + s) from
      Finset.sum_congr rfl (fun i _ => hinner i)]
  rw [ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]

end Work.EKLComp.ErgMax
