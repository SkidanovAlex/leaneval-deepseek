import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.NN.Core.czB_L2_bounded_C0

namespace Work.NN.Core

open MeasureTheory

/-- Pointwise-to-integral step: if a sum of squared moduli of the components `W i` is
dominated pointwise by `A` times the sum of squared moduli of the `∂̄`-derivatives of the
Bochner--Martinelli potential plus `B` times itself, then the same inequality holds after
Lebesgue integration.  No integrability is needed: everything is nonnegative and the
argument is monotonicity of the Lebesgue integral together with the (a.e.) measurability of
the `W`-term coming from continuity. -/
theorem lintegral_normSq_sum_le {n : ℕ} {W : Fin n → Work.NN.Core.Cn n → ℂ}
    {A B : ℝ} (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hWc : ∀ i, Continuous (W i))
    (hΦ : ContDiff ℝ 1 (Work.CR.Flat.Cauchy.bmPotential W))
    (hpt : ∀ z, (∑ i, ‖W i z‖ ^ 2)
        ≤ A * (∑ j, ‖Work.CR.Flat.dCoord j (Work.CR.Flat.Cauchy.bmPotential W) z‖ ^ 2)
          + B * (∑ j, ‖W j z‖ ^ 2)) :
    (∫⁻ z, ∑ i, ENNReal.ofReal (‖W i z‖ ^ 2))
      ≤ ENNReal.ofReal A * (∫⁻ z, ∑ j, ENNReal.ofReal (‖Work.CR.Flat.dCoord j (Work.CR.Flat.Cauchy.bmPotential W) z‖ ^ 2))
        + ENNReal.ofReal B * (∫⁻ z, ∑ j, ENNReal.ofReal (‖W j z‖ ^ 2)) := by
  have _ := hΦ
  have hSnn : ∀ z, 0 ≤ ∑ i, ‖W i z‖ ^ 2 := fun z => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hTnn : ∀ z, 0 ≤ ∑ j, ‖Work.CR.Flat.dCoord j (Work.CR.Flat.Cauchy.bmPotential W) z‖ ^ 2 :=
    fun z => Finset.sum_nonneg fun j _ => sq_nonneg _
  -- Convert the pointwise real inequality into a pointwise `ℝ≥0∞` inequality.
  have hpt' : ∀ z, (∑ i, ENNReal.ofReal (‖W i z‖ ^ 2))
      ≤ ENNReal.ofReal A * (∑ j, ENNReal.ofReal (‖Work.CR.Flat.dCoord j (Work.CR.Flat.Cauchy.bmPotential W) z‖ ^ 2))
        + ENNReal.ofReal B * (∑ j, ENNReal.ofReal (‖W j z‖ ^ 2)) := by
    intro z
    have hT : ENNReal.ofReal (∑ j, ‖Work.CR.Flat.dCoord j (Work.CR.Flat.Cauchy.bmPotential W) z‖ ^ 2)
        = ∑ j, ENNReal.ofReal (‖Work.CR.Flat.dCoord j (Work.CR.Flat.Cauchy.bmPotential W) z‖ ^ 2) :=
      ENNReal.ofReal_sum_of_nonneg (fun j _ => sq_nonneg _)
    have hS : ENNReal.ofReal (∑ j, ‖W j z‖ ^ 2) = ∑ j, ENNReal.ofReal (‖W j z‖ ^ 2) :=
      ENNReal.ofReal_sum_of_nonneg (fun j _ => sq_nonneg _)
    have hL : ENNReal.ofReal (∑ i, ‖W i z‖ ^ 2) = ∑ i, ENNReal.ofReal (‖W i z‖ ^ 2) :=
      ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _)
    calc (∑ i, ENNReal.ofReal (‖W i z‖ ^ 2))
        = ENNReal.ofReal (∑ i, ‖W i z‖ ^ 2) := hL.symm
      _ ≤ ENNReal.ofReal (A * (∑ j, ‖Work.CR.Flat.dCoord j (Work.CR.Flat.Cauchy.bmPotential W) z‖ ^ 2)
            + B * (∑ j, ‖W j z‖ ^ 2)) := ENNReal.ofReal_le_ofReal (hpt z)
      _ = ENNReal.ofReal A * ENNReal.ofReal (∑ j, ‖Work.CR.Flat.dCoord j (Work.CR.Flat.Cauchy.bmPotential W) z‖ ^ 2)
            + ENNReal.ofReal B * ENNReal.ofReal (∑ j, ‖W j z‖ ^ 2) := by
          rw [ENNReal.ofReal_add (mul_nonneg hA0 (hTnn z)) (mul_nonneg hB0 (hSnn z)),
              ENNReal.ofReal_mul hA0, ENNReal.ofReal_mul hB0]
      _ = ENNReal.ofReal A * (∑ j, ENNReal.ofReal (‖Work.CR.Flat.dCoord j (Work.CR.Flat.Cauchy.bmPotential W) z‖ ^ 2))
            + ENNReal.ofReal B * (∑ j, ENNReal.ofReal (‖W j z‖ ^ 2)) := by rw [hT, hS]
  -- The `B`-term is a.e. measurable, being a constant multiple of a continuous function.
  have hmeas : AEMeasurable (fun z : Work.NN.Core.Cn n =>
      ENNReal.ofReal B * (∑ j, ENNReal.ofReal (‖W j z‖ ^ 2))) := by
    refine Measurable.aemeasurable ?_
    refine Measurable.const_mul ?_ _
    exact Finset.measurable_fun_sum _ fun j _ => ((hWc j).norm.pow 2).measurable.ennreal_ofReal
  calc (∫⁻ z, ∑ i, ENNReal.ofReal (‖W i z‖ ^ 2))
      ≤ ∫⁻ z, (ENNReal.ofReal A * (∑ j, ENNReal.ofReal (‖Work.CR.Flat.dCoord j (Work.CR.Flat.Cauchy.bmPotential W) z‖ ^ 2))
              + ENNReal.ofReal B * (∑ j, ENNReal.ofReal (‖W j z‖ ^ 2))) :=
          MeasureTheory.lintegral_mono hpt'
    _ = (∫⁻ z, ENNReal.ofReal A * (∑ j, ENNReal.ofReal (‖Work.CR.Flat.dCoord j (Work.CR.Flat.Cauchy.bmPotential W) z‖ ^ 2)))
        + ∫⁻ z, ENNReal.ofReal B * (∑ j, ENNReal.ofReal (‖W j z‖ ^ 2)) :=
          MeasureTheory.lintegral_add_right' _ hmeas
    _ = ENNReal.ofReal A * (∫⁻ z, ∑ j, ENNReal.ofReal (‖Work.CR.Flat.dCoord j (Work.CR.Flat.Cauchy.bmPotential W) z‖ ^ 2))
        + ENNReal.ofReal B * (∫⁻ z, ∑ j, ENNReal.ofReal (‖W j z‖ ^ 2)) := by
          rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
              MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end Work.NN.Core
