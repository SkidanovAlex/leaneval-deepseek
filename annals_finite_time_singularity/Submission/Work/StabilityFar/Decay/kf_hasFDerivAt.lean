/-
# `Work.StabilityFar.Decay.kf_hasFDerivAt` — the Fréchet derivative of the Newtonian kernel

The Newtonian-potential kernel `kf b = ‖b‖⁻³ • b` of the Biot–Savart integral is
differentiable at every `b ≠ 0`, with the Fréchet derivative `kDerivCLM b` fixed in
`KernelDefs`:

`kDerivCLM b = ‖b‖⁻³ • 1 - 3‖b‖⁻⁵ (b··) b`.

The computation is the elementary chain rule: `kf` is the product of the scalar factor
`‖b‖⁻³` and the identity.  The scalar factor is handled by writing
`‖b‖⁻³ = (‖b‖²)^(-3/2)` and differentiating `(·)^(-3/2)` (`HasFDerivAt.rpow_const`) at the
image of `x ↦ ‖x‖²` (whose derivative is `2 • innerSL ℝ b`), then simplifying the resulting
scalar coefficient with `Real.rpow_natCast_mul` / `Real.rpow_neg`.
-/
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Submission.Work.StabilityFar.Decay.KernelDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.StabilityFar.Decay

open Work.LWP

/-- Scalar multiplication of a **scalar-valued** continuous linear map commutes with
`smulRight`: `(a • L).smulRight x = a • L.smulRight x`. -/
private lemma smulRight_smul_scalar (a : ℝ) (L : R3 →L[ℝ] ℝ) (x : R3) :
    (a • L).smulRight x = a • L.smulRight x := by
  ext v
  simp only [ContinuousLinearMap.smulRight_apply, smul_apply]
  simp [smul_eq_mul, mul_comm, mul_left_comm]

theorem kf_hasFDerivAt (b : Work.LWP.R3) (hb : b ≠ 0) :
    HasFDerivAt Work.StabilityFar.Decay.kf (Work.StabilityFar.Decay.kDerivCLM b) b := by
  -- The scalar identity `(-3/2) * (‖b‖²)^(-3/2 - 1) * 2 = -(3 * (‖b‖⁵)⁻¹)`.
  have hscalar : ((-3 / 2 : ℝ) * (‖b‖ ^ 2) ^ ((-3 / 2 : ℝ) - 1) * 2)
      = -(3 * (‖b‖ ^ 5)⁻¹) := by
    rw [show (-3 / 2 : ℝ) - 1 = -5 / 2 by norm_num]
    rw [← Real.rpow_natCast_mul (norm_nonneg b) 2 (-5 / 2)]
    rw [show ((2 : ℕ) : ℝ) * (-5 / 2 : ℝ) = -5 by norm_num]
    rw [Real.rpow_neg (norm_nonneg b) (5 : ℝ)]
    simp
    ring
  -- Differentiate `x ↦ ‖x‖²` and compose with `(·)^(-3/2)`.
  have hcp : HasFDerivAt (fun x : R3 => (‖x‖ ^ 2) ^ (-3 / 2 : ℝ))
      (((-3 / 2 : ℝ) * (‖b‖ ^ 2) ^ ((-3 / 2 : ℝ) - 1)) • ((2 : ℕ) • innerSL ℝ b)) b :=
    (hasStrictFDerivAt_norm_sq b).hasFDerivAt.rpow_const (Or.inl (by positivity))
  -- `(‖x‖²)^(-3/2) = (‖x‖³)⁻¹`.
  have hc : HasFDerivAt (fun x : R3 => (‖x‖ ^ (3 : ℕ))⁻¹)
      (((-3 / 2 : ℝ) * (‖b‖ ^ 2) ^ ((-3 / 2 : ℝ) - 1)) • ((2 : ℕ) • innerSL ℝ b)) b := by
    refine hcp.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun x => ?_))
    show (‖x‖ ^ (3 : ℕ))⁻¹ = (‖x‖ ^ 2) ^ (-3 / 2 : ℝ)
    rw [← Real.rpow_natCast_mul (norm_nonneg x) 2 (-3 / 2)]
    rw [show ((2 : ℕ) : ℝ) * (-3 / 2 : ℝ) = -3 by norm_num]
    rw [Real.rpow_neg (norm_nonneg x) (3 : ℝ)]
    simp
  -- Put the derivative of the scalar factor into its final shape.
  have hc' : HasFDerivAt (fun x : R3 => (‖x‖ ^ (3 : ℕ))⁻¹)
      (-(3 * (‖b‖ ^ 5)⁻¹) • innerSL ℝ b) b := by
    refine hc.congr_fderiv ?_
    rw [← hscalar]
    rw [← Nat.cast_smul_eq_nsmul (R := ℝ) 2 (innerSL ℝ b)]
    rw [smul_smul]
    norm_num
  -- Product rule with the identity.
  have hsmul := hc'.smul (hasFDerivAt_id b)
  have h1 : HasFDerivAt Work.StabilityFar.Decay.kf
      ((‖b‖ ^ (3 : ℕ))⁻¹ • (1 : R3 →L[ℝ] R3)
        + (-(3 * (‖b‖ ^ 5)⁻¹) • innerSL ℝ b).smulRight b) b :=
    hsmul.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun x => rfl))
  exact h1.congr_fderiv (by
    rw [Work.StabilityFar.Decay.kDerivCLM]
    rw [smulRight_smul_scalar]
    rw [ContinuousLinearMap.one_def]
    rw [show ((-(3 * (‖b‖ ^ 5)⁻¹)) • ((innerSL ℝ b).smulRight b))
          = -((3 * (‖b‖ ^ 5)⁻¹) • ((innerSL ℝ b).smulRight b)) from neg_smul _ _]
    rw [sub_eq_add_neg])

end Work.StabilityFar.Decay
