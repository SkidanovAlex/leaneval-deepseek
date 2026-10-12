import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseSym.Interface
import Submission.Work.BoseSym.MollifyAux.enorm_sub_integral_mul_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseSym.MollifyAux

open MeasureTheory Filter
open scoped ENNReal
open Work.BoseSym

/-- The symmetric form of the convolution on configuration space: `convC` is also the
average of the reflected function against `ρ`. -/
theorem convC_apply_eq {N : ℕ} (f ρ : Conf N → ℝ) (x : Conf N) :
    convC N f ρ x = ∫ y, f (x - y) * ρ y ∂(volC N) := by
  haveI : (volC N).IsNegInvariant := Pi.isNegInvariant_volume
  rw [convC, convolution_lsmul_swap]
  simp

theorem enorm_sub_convC_le {N : ℕ} {f ρ : Conf N → ℝ} (hf : Continuous f)
    (hfs : HasCompactSupport f) (hρc : Continuous ρ) (hρs : HasCompactSupport ρ)
    (hρ0 : 0 ≤ ρ) (hρ1 : intC N ρ = 1) (x : Conf N) :
    ‖f x - convC N f ρ x‖ₑ ≤
      ∫⁻ y, ENNReal.ofReal (ρ y) * ENNReal.ofReal |f x - f (x - y)| ∂(volC N) := by
  obtain ⟨M, hM⟩ := hfs.exists_bound_of_continuous hf
  have hFm : AEStronglyMeasurable (fun y : Conf N => f (x - y)) (volC N) :=
    (hf.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  rw [convC_apply_eq f ρ x]
  exact enorm_sub_integral_mul_le (F := fun y : Conf N => f (x - y)) (c := f x)
    (fun y => hρ0 y) (by simpa only [intC] using hρ1) hFm (fun y => hM (x - y))

end Work.BoseSym.MollifyAux
