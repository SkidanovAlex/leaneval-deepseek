import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseSym.Interface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Integrability of the squared gradient norm

For a `C¹` function `f` on configuration space with compact support, the
pointwise derivative `fderiv ℝ f` is again continuous and compactly supported
(the derivative vanishes off the support of `f`), hence so is the continuous
function `x ↦ ‖fderiv ℝ f x‖²`.  As Lebesgue measure on `Conf N` is finite on
compacts, the latter is integrable.

This is the elementary "smooth compactly supported functions have square
integrable gradient" fact used by the mollification layer.
-/

namespace Work.BoseSym.MollifyAux

open MeasureTheory Filter
open scoped Topology Real

/-- The derivative of a `C¹` compactly supported function is continuous. -/
lemma continuous_fderiv_of_smooth1 {N : ℕ} {f : Conf N → ℝ} (hf : Smooth1 f) :
    Continuous (fun x => fderiv ℝ f x) :=
  hf.continuous_fderiv (by norm_num)

/-- The derivative of a compactly supported function is compactly supported:
off `tsupport f` the function is locally zero, so its derivative vanishes. -/
lemma hasCompactSupport_fderiv {N : ℕ} {f : Conf N → ℝ} (hcs : HasCompactSupport f) :
    HasCompactSupport (fun x => fderiv ℝ f x) :=
  hcs.fderiv ℝ

/-- The squared norm of the derivative of a compactly supported function is
compactly supported. -/
lemma hasCompactSupport_fderiv_sq {N : ℕ} {f : Conf N → ℝ} (hcs : HasCompactSupport f) :
    HasCompactSupport (fun x => ‖fderiv ℝ f x‖ ^ 2) :=
  (hasCompactSupport_fderiv hcs).norm.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)

theorem integrable_fderiv_sq {N : ℕ} {f : Conf N → ℝ} (hf : Smooth1 f) (hcs : HasCompactSupport f) :
    MeasureTheory.Integrable (fun x => ‖fderiv ℝ f x‖ ^ 2) (volC N) := by
  have h2 : Continuous (fun x => ‖fderiv ℝ f x‖ ^ 2) :=
    (continuous_fderiv_of_smooth1 hf).norm.pow 2
  exact h2.integrable_of_hasCompactSupport (hasCompactSupport_fderiv_sq hcs)

end Work.BoseSym.MollifyAux
