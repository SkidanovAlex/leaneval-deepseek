/-
# `Work.StabilityFar.Decay.KernelDefs` — the Biot–Savart kernel calculus for the far-field
second-derivative estimate

The far-field Lipschitz bound for `x ↦ fderiv ℝ (biotSavart ω) x` is the statement that
`biotSavart ω` is `C^{1,1}` in the region outside the support of `ω`.  This file fixes the
elementary objects of that computation:

* `kf b = ‖b‖⁻³ • b` — the Newtonian-potential kernel `b ↦ b/‖b‖³` whose derivative the
  Biot–Savart field is built from;
* `kDerivCLM b` — its Fréchet derivative at `b`, as a continuous linear map;
* `crossL u` — the cross product `v ↦ u × v` as a continuous linear map;
* `bsDeriv ω x` — the candidate for `fderiv ℝ (biotSavart ω) x` in the far field, the
  Bochner integral `(4π)⁻¹ ∫ a, crossL (ω a) ∘ kDerivCLM (x - a)`.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.LWP.FarField

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Filter Topology MeasureTheory
open scoped Topology NNReal ENNReal

set_option autoImplicit false

namespace Work.StabilityFar.Decay

open Work.LWP

/-- The Newtonian-potential kernel `b ↦ ‖b‖⁻³ • b` of the Biot–Savart integral. -/
noncomputable def kf (b : R3) : R3 := (‖b‖ ^ (3 : ℕ))⁻¹ • b

/-- The Fréchet derivative of `kf` at `b`, as a continuous linear map:
`v ↦ ‖b‖⁻³ • v - 3 ‖b‖⁻⁵ (b·v) b`. -/
noncomputable def kDerivCLM (b : R3) : R3 →L[ℝ] R3 :=
  (‖b‖ ^ (3 : ℕ))⁻¹ • ContinuousLinearMap.id ℝ R3
    - (3 * (‖b‖ ^ (5 : ℕ))⁻¹) • (innerSL ℝ b).smulRight b

/-- The cross product with a fixed vector `u`, as a continuous linear map `v ↦ u × v`. -/
noncomputable def crossL (u : R3) : R3 →L[ℝ] R3 :=
  LinearMap.toContinuousLinearMap <|
    ((WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toLinearMap).comp
      ((crossProduct u.ofLp).comp (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).toLinearMap)

/-- The candidate derivative of `biotSavart ω` at `x`, as the Bochner integral of the
derivatives of the Biot–Savart integrand.  In the far field `‖x‖ ≥ 2R` (with `ω` supported in
`B(0,R)`) this is genuinely `fderiv ℝ (biotSavart ω) x`. -/
noncomputable def bsDeriv (ω : R3 → R3) (x : R3) : R3 →L[ℝ] R3 :=
  (4 * Real.pi)⁻¹ • ∫ a : R3, (crossL (ω a)).comp (kDerivCLM (x - a))


/-! ## Elementary lemmas about the kernel objects -/

/-- The defining value of `crossL`: `crossL u v = u × v`. -/
theorem crossL_apply (u v : R3) : crossL u v = WithLp.toLp 2 (crossProduct u.ofLp v.ofLp) := rfl

/-- `crossL` is additive in its parameter. -/
theorem crossL_add (u u' : R3) : crossL (u + u') = crossL u + crossL u' := by
  ext v
  simp only [crossL_apply, ContinuousLinearMap.add_apply, WithLp.ofLp_add]
  rw [map_add]
  rfl

/-- `crossL` is homogeneous in its parameter. -/
theorem crossL_smul (c : ℝ) (u : R3) : crossL (c • u) = c • crossL u := by
  ext v
  simp only [crossL_apply, ContinuousLinearMap.smul_apply, WithLp.ofLp_smul]
  rw [map_smul]
  rfl

/-- The underlying vector of `kf`. -/
theorem kf_ofLp (b : R3) : (kf b).ofLp = (‖b‖ ^ (3 : ℕ))⁻¹ • b.ofLp := by
  simp [kf]

/-- The Biot–Savart integrand is the cross product kernel applied to `kf`. -/
theorem bsK_eq_crossL (ω : R3 → R3) (x a : R3) :
    Work.LWP.BiotSavart.bsK ω x a = crossL (ω a) (kf (x - a)) := by
  rw [Work.LWP.BiotSavart.bsK.eq_def, crossL_apply, kf_ofLp, map_smul]
  rfl

end Work.StabilityFar.Decay
