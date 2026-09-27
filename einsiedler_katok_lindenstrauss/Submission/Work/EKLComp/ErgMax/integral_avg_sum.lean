import Mathlib
import Submission.Work.EKLComp.ErgMax.ShiftDefs

/-!
# `integral_avg_sum` — the integral against the `A⁺`-average, expanded

The averaged measure `avg ν N` is the normalised finite sum

  `avg ν N = ((n N * n N : ℕ) : ℝ≥0∞)⁻¹ • ∑_{i,j < n N} (aDiag (shift N i j))_* ν`

(`ErgMax.Basic`, `ErgMax.avg_def`).  Integrating a bounded continuous `f : X₃ →ᵇ ℝ` against it
therefore expands as a normalised double sum of the translated integrals

  `psi ν f (i/N) (j/N) = ∫ y, f (aPlus (i/N) (j/N) • y) ∂ν`.

The proof has three elementary ingredients, each isolated below:

* the integral against a scalar multiple `c • μ` of a measure is `c.toReal` times the integral
  (`MeasureTheory.integral_smul_measure`) and `(↑(n N * n N) : ℝ≥0∞)⁻¹.toReal = (↑(n N * n N) : ℝ)⁻¹`
  (`ENNReal.toReal_inv`, `ENNReal.toReal_natCast`);
* the integral against a finite sum of finite measures is the sum of the integrals
  (`MeasureTheory.integral_finsetSum_measure`, using the boundedness of `f`);
* the integral against a pushforward `(act g)_* ν` is the integral of `f ∘ act g`
  (`MeasureTheory.integral_map`), and `aDiag (shift N i j) = aPlus (i/N) (j/N)`
  (`ErgMax.aDiag_shift`) turns the latter into `psi`.
-/

open MeasureTheory
open scoped ENNReal

namespace Work.EKLComp.ErgMax

open Work.EKLContract

noncomputable section

/-- The integral of a bounded continuous function against a finite sum of finite measures is the
sum of the integrals. -/
private theorem integral_finset_sum_measure_finite {ι : Type*} [Fintype ι] (μ : ι → Measure X3)
    (hμ : ∀ i, IsFiniteMeasure (μ i)) (f : BoundedContinuousFunction X3 ℝ) :
    ∫ x, f x ∂(∑ i, μ i) = ∑ i, ∫ x, f x ∂(μ i) := by
  rw [integral_finsetSum_measure]
  intro i _
  exact BoundedContinuousFunction.integrable (μ i) f

/-- The integral against a pushforward `(act g)_* ν`. -/
private theorem integral_map_act (ν : Measure X3) (f : BoundedContinuousFunction X3 ℝ) (g : SL3) :
    ∫ x, f x ∂(ν.map (act g)) = ∫ y, f (act g y) ∂ν := by
  rw [integral_map (measurable_act g).aemeasurable]
  exact f.continuous.aestronglyMeasurable

/-- The integral against `(act (aDiag (shift N i j)))_* ν` is `psi ν f (i/N) (j/N)`. -/
private theorem integral_map_act_aDiag_shift (ν : Measure X3) (f : BoundedContinuousFunction X3 ℝ)
    (N i j : ℕ) :
    ∫ x, f x ∂(ν.map (act (aDiag (shift N i j)))) = psi ν f ((i : ℝ) / N) ((j : ℝ) / N) := by
  rw [integral_map_act, psi]
  simp only [act_apply, aDiag_shift]

theorem integral_avg_sum (ν : MeasureTheory.Measure Work.EKLContract.X3)
    [MeasureTheory.IsFiniteMeasure ν]
    (f : BoundedContinuousFunction Work.EKLContract.X3 ℝ) (N : ℕ) :
    (∫ x, f x ∂(Work.EKLComp.ErgMax.avg ν N)) =
      (((Work.EKLComp.ErgMax.n N * Work.EKLComp.ErgMax.n N : ℕ) : ℝ))⁻¹ *
        ∑ i : Fin (Work.EKLComp.ErgMax.n N), ∑ j : Fin (Work.EKLComp.ErgMax.n N),
          Work.EKLComp.ErgMax.psi ν f ((i : ℝ) / N) ((j : ℝ) / N) := by
  rw [avg_def, integral_smul_measure]
  have hc : ((((n N * n N : ℕ) : ℝ≥0∞))⁻¹).toReal = (((n N * n N : ℕ) : ℝ))⁻¹ := by
    rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [hc]
  congr 1
  calc ∫ x, f x ∂(∑ i : Fin (n N), ∑ j : Fin (n N), ν.map (act (aDiag (shift N i j))))
      = ∑ i : Fin (n N), ∫ x, f x ∂(∑ j : Fin (n N), ν.map (act (aDiag (shift N i j)))) :=
        integral_finset_sum_measure_finite _ (fun i => inferInstance) f
    _ = ∑ i : Fin (n N), ∑ j : Fin (n N), psi ν f ((i : ℝ) / N) ((j : ℝ) / N) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_finset_sum_measure_finite _ (fun j => inferInstance) f]
        exact Finset.sum_congr rfl fun j _ => integral_map_act_aDiag_shift ν f N i j

end

end Work.EKLComp.ErgMax
