import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.BoseSym.Interface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseSym.MollifyAux

open MeasureTheory

/-- Translation invariance of the Lebesgue integral on configuration space: for fixed `t`, the
map `x ↦ x - t • y` preserves `volC N`. -/
theorem lintegral_sub_smul_eq_self {N : ℕ} (H : Conf N → ENNReal) (y : Conf N) (t : ℝ) :
    (∫⁻ x, H (x - t • y) ∂(volC N)) = ∫⁻ x, H x ∂(volC N) := by
  simp only [sub_eq_add_neg]
  exact MeasureTheory.lintegral_add_right_eq_self H (-(t • y))

/-- Averaging a measurable `ℝ≥0∞`-valued function over the family of translates
`x ↦ x - t • y`, `t ∈ (0,1]`, does not change its Lebesgue integral on configuration space. -/
theorem lintegral_lintegral_sub_smul {N : ℕ} {H : Conf N → ENNReal} (hH : Measurable H) (y : Conf N) :
    MeasureTheory.lintegral (volC N)
        (fun x => MeasureTheory.lintegral
          (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioc (0:ℝ) 1))
          (fun t => H (x - t • y)))
      = MeasureTheory.lintegral (volC N) H := by
  rw [MeasureTheory.lintegral_lintegral_swap]
  · simp_rw [lintegral_sub_smul_eq_self H y]
    rw [MeasureTheory.lintegral_const]
    simp [MeasureTheory.Measure.restrict_apply, Real.volume_Ioc]
  · exact hH.comp (by fun_prop) |>.aemeasurable

end Work.BoseSym.MollifyAux
