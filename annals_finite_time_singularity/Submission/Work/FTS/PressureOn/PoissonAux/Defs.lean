/-
# `Work.FTS.PressureOn` — auxiliary profiles for the weak Poisson identity

This module holds the *definitions* used by `Work.FTS.PressureOn.weakPoisson` (the weak form of
the Poisson equation for the pressure potential) and by the auxiliary lemmas about them proved in
the sibling files of `Submission/Work/FTS/PressureOn/PoissonAux/`.

The weak Poisson identity is

  `∫ x, pressurePotential f x * laplaceTrace φ x = ∫ x, inner ℝ (f x) (gradient φ x)`,

whose kernel-level content is the classical `Δ(1/(4π‖x‖)) = -δ₀`: for a smooth compactly supported
`ψ`, `∫ x, (4π‖x‖)⁻¹ * laplaceTrace ψ x = -ψ 0`, together with the gradient version, obtained by
differentiating in the centre (equivalently, by a first-order integration by parts against the
truncated kernel).

The standard proof truncates the singular kernel near the origin: with a smooth profile `χ` equal
to `1` on `(-∞,1]` and to `0` on `[2,∞)`, the function `x ↦ (1-χ(‖x‖²/ε²))/(4π‖x‖)` is smooth and
compact near the origin (it is *constant* in a neighbourhood of `0`, which is why it is smooth even
though `‖·‖` is not differentiable at the origin); for `x ≠ 0` its Laplacian equals
`newtonKernel x * ρ_ε''(‖x‖)` where `ρ_ε(r) = 1 - χ(r²/ε²)`: the terms involving `(4πr)⁻¹` cancel
because that function is harmonic on `(0,∞)`.  This is the `massKernel` below, whose total mass is
`-1` and whose mass concentrates at the origin.

## Main definitions

* `radialCut` — the smooth profile `t ↦ χ(t)`, `1` on `(-∞,1]` and `0` on `[2,∞)`;
* `kernelCut`, `smallCut`, `outerCut` — its rescalings in `‖x‖²/ε²`;
* `rhoProfile`, `cutKernelProfile` — the one-dimensional profiles of the truncations;
* `massKernel` — the Laplacian of the truncated Newtonian kernel, away from the origin.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.PressureOn.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set MeasureTheory Metric
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn

/-! ## The profile `χ` -/

/-- The smooth profile `χ(t) = smoothTransition (2 - t)`: it is `1` for `t ≤ 1`, `0` for `t ≥ 2`,
and takes its values in `[0,1]`. -/
noncomputable def radialCut (t : ℝ) : ℝ := Real.smoothTransition (2 - t)

theorem radialCut_eq_one {t : ℝ} (ht : t ≤ 1) : radialCut t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem radialCut_eq_zero {t : ℝ} (ht : 2 ≤ t) : radialCut t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem radialCut_nonneg (t : ℝ) : 0 ≤ radialCut t := Real.smoothTransition.nonneg _

theorem radialCut_le_one (t : ℝ) : radialCut t ≤ 1 := Real.smoothTransition.le_one _

theorem contDiff_radialCut (n : ℕ∞) : ContDiff ℝ n radialCut :=
  (Real.smoothTransition.contDiff (n := n)).comp (contDiff_const.sub contDiff_id)

theorem continuous_radialCut : Continuous radialCut := (contDiff_radialCut 0).continuous

theorem radialCut_ne_zero_iff_lt_two (t : ℝ) : radialCut t ≠ 0 ↔ t < 2 := by
  constructor
  · intro h
    by_contra h2
    exact h (radialCut_eq_zero (not_lt.mp h2))
  · intro h hc
    have h0 : (2 : ℝ) - t ≤ 0 := Real.smoothTransition.zero_iff_nonpos.mp hc
    linarith

/-- The profile is supported in `(-∞,2]`. -/
theorem support_radialCut_subset : Function.support radialCut ⊆ Set.Iic 2 := fun t ht =>
  le_of_lt ((radialCut_ne_zero_iff_lt_two t).mp ht)

/-! ## The rescaled cutoffs in `ℝ³` -/

/-- `kernelCut ε x = χ(‖x‖²/ε²)`: `1` for `‖x‖ ≤ ε` and `0` for `√2 ε ≤ ‖x‖`. -/
noncomputable def kernelCut (ε : ℝ) (x : R3) : ℝ := radialCut (‖x‖ ^ 2 / ε ^ 2)

/-- `smallCut ε x = 1 - χ(‖x‖²/ε²)`: `0` for `‖x‖ ≤ ε` and `1` for `√2 ε ≤ ‖x‖`.  It is the
cutoff that removes the singularity of the Newtonian kernel at the origin. -/
noncomputable def smallCut (ε : ℝ) (x : R3) : ℝ := 1 - radialCut (‖x‖ ^ 2 / ε ^ 2)

/-- `outerCut R x = χ(‖x‖²/R²)`: `1` for `‖x‖ ≤ R` and `0` for `√2 R ≤ ‖x‖`. -/
noncomputable def outerCut (R : ℝ) (x : R3) : ℝ := radialCut (‖x‖ ^ 2 / R ^ 2)

@[simp] theorem kernelCut_apply (ε : ℝ) (x : R3) : kernelCut ε x = radialCut (‖x‖ ^ 2 / ε ^ 2) :=
  rfl

@[simp] theorem smallCut_apply (ε : ℝ) (x : R3) :
    smallCut ε x = 1 - radialCut (‖x‖ ^ 2 / ε ^ 2) := rfl

@[simp] theorem outerCut_apply (R : ℝ) (x : R3) : outerCut R x = radialCut (‖x‖ ^ 2 / R ^ 2) := rfl

theorem contDiff_kernelCut (ε : ℝ) (hε : 0 < ε) (n : ℕ∞) : ContDiff ℝ n (kernelCut ε) :=
  (contDiff_radialCut n).comp ((contDiff_norm_sq (𝕜 := ℝ) (n := n)).div_const (ε ^ 2))

theorem contDiff_smallCut (ε : ℝ) (hε : 0 < ε) (n : ℕ∞) : ContDiff ℝ n (smallCut ε) :=
  contDiff_const.sub (contDiff_kernelCut ε hε n)

theorem contDiff_outerCut (R : ℝ) (hR : 0 < R) (n : ℕ∞) : ContDiff ℝ n (outerCut R) :=
  (contDiff_radialCut n).comp ((contDiff_norm_sq (𝕜 := ℝ) (n := n)).div_const (R ^ 2))

theorem kernelCut_sq_apply (ε : ℝ) (x : R3) : kernelCut ε x = radialCut (‖x‖ ^ 2 / ε ^ 2) := rfl

theorem radialCut_sq_eq_one {ε : ℝ} (hε : 0 < ε) {x : R3} (hx : ‖x‖ ≤ ε) :
    radialCut (‖x‖ ^ 2 / ε ^ 2) = 1 := by
  refine radialCut_eq_one ?_
  rw [div_le_one (by positivity)]
  nlinarith [norm_nonneg x]

theorem radialCut_sq_eq_zero {ε : ℝ} (hε : 0 < ε) {x : R3} (hx : 2 * ε ^ 2 ≤ ‖x‖ ^ 2) :
    radialCut (‖x‖ ^ 2 / ε ^ 2) = 0 := by
  refine radialCut_eq_zero ?_
  rw [le_div_iff₀ (by positivity)]
  linarith

theorem kernelCut_eq_one {ε : ℝ} (hε : 0 < ε) {x : R3} (hx : ‖x‖ ≤ ε) : kernelCut ε x = 1 :=
  radialCut_sq_eq_one hε hx

theorem kernelCut_eq_zero {ε : ℝ} (hε : 0 < ε) {x : R3} (hx : 2 * ε ^ 2 ≤ ‖x‖ ^ 2) :
    kernelCut ε x = 0 :=
  radialCut_sq_eq_zero hε hx

theorem smallCut_eq_zero {ε : ℝ} (hε : 0 < ε) {x : R3} (hx : ‖x‖ ≤ ε) : smallCut ε x = 0 := by
  rw [smallCut_apply, radialCut_sq_eq_one hε hx, sub_self]

theorem smallCut_eq_one {ε : ℝ} (hε : 0 < ε) {x : R3} (hx : 2 * ε ≤ ‖x‖) : smallCut ε x = 1 := by
  rw [smallCut_apply, radialCut_sq_eq_zero hε (by nlinarith [norm_nonneg x]), sub_zero]

theorem outerCut_eq_one {R : ℝ} (hR : 0 < R) {x : R3} (hx : ‖x‖ ≤ R) : outerCut R x = 1 := by
  refine radialCut_eq_one ?_
  rw [div_le_one (by positivity)]
  nlinarith [norm_nonneg x]

theorem outerCut_eq_zero {R : ℝ} (hR : 0 < R) {x : R3} (hx : 2 * R ≤ ‖x‖) : outerCut R x = 0 := by
  refine radialCut_eq_zero ?_
  rw [le_div_iff₀ (by positivity)]
  nlinarith [norm_nonneg x]
theorem kernelCut_nonneg (ε : ℝ) (x : R3) : 0 ≤ kernelCut ε x := radialCut_nonneg _

theorem kernelCut_le_one (ε : ℝ) (x : R3) : kernelCut ε x ≤ 1 := radialCut_le_one _

theorem smallCut_nonneg (ε : ℝ) (x : R3) : 0 ≤ smallCut ε x := by
  rw [smallCut_apply]; linarith [radialCut_le_one (‖x‖ ^ 2 / ε ^ 2)]

theorem smallCut_le_one (ε : ℝ) (x : R3) : smallCut ε x ≤ 1 := by
  rw [smallCut_apply]; linarith [radialCut_nonneg (‖x‖ ^ 2 / ε ^ 2)]

theorem outerCut_nonneg (R : ℝ) (x : R3) : 0 ≤ outerCut R x := radialCut_nonneg _

theorem outerCut_le_one (R : ℝ) (x : R3) : outerCut R x ≤ 1 := radialCut_le_one _

theorem hasCompactSupport_outerCut {R : ℝ} (hR : 0 < R) : HasCompactSupport (outerCut R) := by
  refine HasCompactSupport.of_support_subset_isCompact (K := closedBall 0 (2 * R))
    (isCompact_closedBall 0 (2 * R)) ?_
  intro x hx
  rw [mem_closedBall, dist_zero_right]
  by_contra h
  push Not at h
  exact hx (outerCut_eq_zero hR (le_of_lt h))

/-! ## The one-dimensional profiles -/

/-- The one-dimensional profile `ρ_ε(r) = 1 - χ(r²/ε²)`, so that
`smallCut ε x = rhoProfile ε ‖x‖`. -/
noncomputable def rhoProfile (ε : ℝ) (r : ℝ) : ℝ := 1 - radialCut (r ^ 2 / ε ^ 2)

@[simp] theorem rhoProfile_apply (ε r : ℝ) : rhoProfile ε r = 1 - radialCut (r ^ 2 / ε ^ 2) := rfl

theorem smallCut_eq_rhoProfile (ε : ℝ) (x : R3) : smallCut ε x = rhoProfile ε ‖x‖ := rfl

theorem rhoProfile_eq_zero {ε : ℝ} (hε : 0 < ε) {r : ℝ} (hr : r ^ 2 ≤ ε ^ 2) :
    rhoProfile ε r = 0 := by
  rw [rhoProfile_apply, radialCut_eq_one (by
    rw [div_le_one (by positivity)]
    exact hr), sub_self]

theorem rhoProfile_eq_one {ε : ℝ} (hε : 0 < ε) {r : ℝ} (hr : 2 * ε ^ 2 ≤ r ^ 2) :
    rhoProfile ε r = 1 := by
  rw [rhoProfile_apply, radialCut_eq_zero (by
    rw [le_div_iff₀ (by positivity)]
    linarith), sub_zero]

/-- The one-dimensional profile of the truncated Newtonian potential:
`cutKernelProfile ε r = (1 - χ(r²/ε²))/(4πr)`, so that
`cutKernelProfile ε ‖x‖ = smallCut ε x * newtonKernel x`. -/
noncomputable def cutKernelProfile (ε : ℝ) (r : ℝ) : ℝ :=
  rhoProfile ε r * (4 * Real.pi * r)⁻¹

theorem cutKernelProfile_eq (ε : ℝ) (x : R3) :
    cutKernelProfile ε ‖x‖ = smallCut ε x * newtonKernel x := rfl

/-- **The mass kernel** `massKernel ε x = (4π‖x‖)⁻¹ ρ_ε''(‖x‖)`: the (classical) Laplacian of the
truncated Newtonian kernel `x ↦ smallCut ε x * (4π‖x‖)⁻¹`, away from the origin, where
`ρ_ε(r) = 1 - χ(r²/ε²)`. -/
noncomputable def massKernel (ε : ℝ) (x : R3) : ℝ :=
  newtonKernel x * deriv (deriv (rhoProfile ε)) ‖x‖

theorem massKernel_eq (ε : ℝ) (x : R3) :
    massKernel ε x = newtonKernel x * deriv (deriv (rhoProfile ε)) ‖x‖ := rfl

end Work.FTS.PressureOn
