import Mathlib
import Submission.Work.BoseSym.Interface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# BoseSym.Form — the `L²` norm squared as an integral

The function part of the ambient space `Amb N` is an element `p.1` of
`L2 N = Lp ℝ 2 (volC N)`, and `l2Sq p = ‖p.1‖²` is its squared norm.

The point of this file is that this squared norm can be computed as the
integral of the pointwise square of any representative:

`l2Sq p = intC N (fun x => (p.1 x)²)`.

The substantive ingredient is the general identity for a real `L²` class,

`‖f‖² = ∫ x, (f x)² ∂μ`  (`lp_norm_sq_eq_integral_sq`),

which is the `ℝ`-valued analogue of `lpNorm_eq_integral_norm_rpow_toReal`:
the `L²` norm is the square root of the integral of the squared modulus, and
squaring the square root of a nonnegative integral returns the integral.
-/

namespace Work.BoseSym.Form

open MeasureTheory Filter
open scoped Topology Real ContDiff ENNReal

set_option autoImplicit false

/-- **The squared `L²` norm of a real `L²` class is the integral of the
pointwise square of any representative.** -/
theorem lp_norm_sq_eq_integral_sq {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : Lp ℝ 2 μ) : ‖f‖ ^ 2 = ∫ x, ((f : α → ℝ) x) ^ 2 ∂μ := by
  have hf : AEStronglyMeasurable (f : α → ℝ) μ := Lp.aestronglyMeasurable f
  have hnorm : ‖f‖ = lpNorm (f : α → ℝ) 2 μ := by
    rw [Lp.norm_def, toReal_eLpNorm]
  rw [hnorm, lpNorm_eq_integral_norm_rpow_toReal (p := 2) (by norm_num) (by norm_num) hf]
  simp only [ENNReal.toReal_ofNat]
  have hA : 0 ≤ ∫ x, ‖(f : α → ℝ) x‖ ^ (2:ℝ) ∂μ :=
    integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _)
  rw [inv_eq_one_div, ← Real.sqrt_eq_rpow, Real.sq_sqrt hA]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs]

/-- The squared `L²` norm of the function part of an element of the ambient
space, as the integral of its pointwise square. -/
theorem l2Sq_eq_integral {N : ℕ} (p : Amb N) :
    l2Sq p = intC N (fun x => ((p.1 : Conf N → ℝ) x) ^ 2) := by
  rw [l2Sq, intC]
  exact lp_norm_sq_eq_integral_sq (volC N) p.1

end Work.BoseSym.Form
