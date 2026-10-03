import Mathlib
import Submission.Work.Repel.Koebe.Setup

/-!
# A boundary curve staying inside the disc of radius `‖ζ‖` has winding number `0`

Let `g` be holomorphic on the exterior `{1 < ‖z‖}` of the unit disc, let `1 < r` and suppose that
`‖g z‖ < ‖ζ‖` for every `z` on the circle `‖z‖ = r`.  Then the winding number of the curve
`z ↦ g z` over that circle about `ζ` vanishes:

`wind g r ζ = 0`.

## Proof

The integral defining `wind g r ζ` involves only the values of `g` on the circle `‖z‖ = r`, and
`‖g z‖ < ‖ζ‖` says precisely that the image curve lies in the open disc of radius `‖ζ‖` about `0`,
i.e. that `ζ` lies in the unbounded component of the complement of the curve.  Instead of invoking
any separation theorem we use the logarithm: on the circle we have

`Re ((g z - ζ)/ζ) = Re (g z/ζ) - 1 ≤ ‖g z‖/‖ζ‖ - 1 < 0`,

so the image of `g - ζ` lies in the open half plane `{w | Re (w/ζ) < 0}`, which does not meet
`(-∞, 0]` after rotation: `w ↦ -w/ζ` sends it into the slit plane on which `Complex.log` is
analytic with derivative `u⁻¹`.  Hence the function

`Φ z = log (-(g z - ζ)/ζ) = log ((g z - ζ) * (-ζ⁻¹))`

is a local primitive of the integrand `(deriv g)/(g - ζ)` near the circle (a global analytic
primitive on a neighbourhood of the circle, so no separation statement is needed).  A closed
integral of a derivative vanishes:

* `circleIntegral_eq_zero_of_hasDerivAt` — if `f` is continuous on the circle and `f` is the
  derivative of `Φ` at every point of the circle, then `∮_{C(c,R)} f = 0`, by the fundamental
  theorem of calculus applied to `θ ↦ Φ (circleMap c R θ)` (the map is `2π`-periodic).

The degenerate case `ζ = 0` is vacuous: `‖g z‖ < ‖0‖ = 0` is impossible on a nonempty circle.
-/

open MeasureTheory Filter Topology
open scoped Topology

namespace Work.Repel.Koebe

/-- If `‖g z‖ < ‖ζ‖` and `ζ ≠ 0` then `(g z)/ζ` has real part `< 1`. -/
lemma re_lt_one_of_norm_lt {g : ℂ → ℂ} {ζ z : ℂ} (hζ : ζ ≠ 0) (h : ‖g z‖ < ‖ζ‖) :
    (g z * ζ⁻¹).re < 1 := by
  have hζpos : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ
  have hle : (g z * ζ⁻¹).re ≤ ‖g z * ζ⁻¹‖ := Complex.re_le_norm _
  rw [norm_mul, norm_inv] at hle
  have h2 : ‖g z‖ * ‖ζ‖⁻¹ < 1 := by
    rw [← div_eq_mul_inv, div_lt_one hζpos]; exact h
  linarith

/-- If `‖g z‖ < ‖ζ‖` and `ζ ≠ 0` then `g z ≠ ζ`. -/
lemma sub_ne_zero_of_norm_lt {g : ℂ → ℂ} {ζ z : ℂ} (hζ : ζ ≠ 0) (h : ‖g z‖ < ‖ζ‖) :
    g z - ζ ≠ 0 := by
  intro h0
  have hlt := re_lt_one_of_norm_lt (g := g) hζ h
  have : (g z * ζ⁻¹).re = 1 := by
    rw [show g z = ζ from sub_eq_zero.mp h0, mul_inv_cancel₀ hζ]; simp
  linarith

/-- **The logarithmic primitive.**  If `‖g z‖ < ‖ζ‖` then `u ↦ log ((g u - ζ) * (-ζ⁻¹))` has
derivative `(deriv g z)/(g z - ζ)` at `z`, whenever `g` has derivative `deriv g z` there. -/
lemma hasDerivAt_logArg {g : ℂ → ℂ} {ζ z : ℂ} (hζ : ζ ≠ 0) (h : ‖g z‖ < ‖ζ‖)
    (hgz : HasDerivAt g (deriv g z) z) :
    HasDerivAt (fun u : ℂ => Complex.log ((g u - ζ) * (-ζ⁻¹))) (deriv g z / (g z - ζ)) z := by
  have hlt := re_lt_one_of_norm_lt (g := g) hζ h
  have hw : g z - ζ ≠ 0 := sub_ne_zero_of_norm_lt (g := g) hζ h
  have hmem : (g z - ζ) * (-ζ⁻¹) ∈ Complex.slitPlane := by
    refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
    have hre : ((g z - ζ) * (-ζ⁻¹)).re = 1 - (g z * ζ⁻¹).re := by
      have : (g z - ζ) * (-ζ⁻¹) = 1 - g z * ζ⁻¹ := by field_simp; ring
      rw [this]; simp
    rw [hre]; linarith
  have hinner : HasDerivAt (fun u : ℂ => (g u - ζ) * (-ζ⁻¹)) (deriv g z * (-ζ⁻¹)) z :=
    (hgz.sub_const ζ).mul_const (-ζ⁻¹)
  have hlog := (Complex.hasDerivAt_log hmem).comp z hinner
  have hsimp : ζ * (g z - ζ)⁻¹ * (deriv g z * ζ⁻¹) = deriv g z / (g z - ζ) := by
    field_simp
  simpa [Function.comp_def, hsimp] using hlog

/-- Continuity of the winding integrand `z ↦ (deriv g z)/(g z - ζ)` at points where `g z ≠ ζ`. -/
lemma continuousAt_wind_integrand {g : ℂ → ℂ} {ζ z : ℂ} (hζ : ζ ≠ 0) (h : ‖g z‖ < ‖ζ‖)
    (hgz : AnalyticAt ℂ g z) :
    ContinuousAt (fun z : ℂ => deriv g z / (g z - ζ)) z :=
  ((hgz.deriv.continuousAt).div (hgz.continuousAt.sub continuousAt_const)
    (sub_ne_zero_of_norm_lt (g := g) hζ h))

/-- **A closed circle integral of a derivative vanishes.**  If `f` is continuous on the circle
`C(c,R)` and `f` is the derivative of `Φ` at every point of that circle, then `∮_{C(c,R)} f = 0`:
the parametrised integral is the integral of the total derivative of `θ ↦ Φ (circleMap c R θ)`,
which is `2π`-periodic. -/
lemma circleIntegral_eq_zero_of_hasDerivAt {f Φ : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hfc : ∀ θ : ℝ, ContinuousAt f (circleMap c R θ))
    (h : ∀ θ : ℝ, HasDerivAt Φ (f (circleMap c R θ)) (circleMap c R θ)) :
    circleIntegral f c R = 0 := by
  have hderiv : ∀ θ ∈ Set.uIcc 0 (2 * Real.pi),
      HasDerivAt (fun θ : ℝ => Φ (circleMap c R θ))
        (deriv (circleMap c R) θ • f (circleMap c R θ)) θ := by
    intro θ _
    have h1 : HasDerivAt (circleMap c R) (deriv (circleMap c R) θ) θ := by
      have hd : DifferentiableAt ℝ (circleMap c R) θ := by
        unfold circleMap; fun_prop
      exact hd.hasDerivAt
    have h2 := (h θ).comp θ h1
    simpa [Function.comp_def, smul_eq_mul, mul_comm] using h2
  have hint : IntervalIntegrable (fun θ : ℝ => deriv (circleMap c R) θ • f (circleMap c R θ))
      volume 0 (2 * Real.pi) := by
    apply ContinuousOn.intervalIntegrable
    intro θ hθ
    have hcm : ContinuousAt (circleMap c R) θ := by unfold circleMap; fun_prop
    have hder : ContinuousAt (fun θ : ℝ => deriv (circleMap c R) θ) θ := by
      have he : (fun θ : ℝ => deriv (circleMap c R) θ) = fun θ => circleMap 0 R θ * Complex.I := by
        funext θ; exact deriv_circleMap c R θ
      rw [he]; fun_prop
    exact ((hder.smul ((hfc θ).comp hcm))).continuousWithinAt
  rw [circleIntegral, intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hper : circleMap c R (2 * Real.pi) = circleMap c R 0 := by
    simpa using (periodic_circleMap c R 0)
  rw [hper, sub_self]

/-- **Winding number zero when the curve avoids the disc of radius `‖ζ‖`.**  If `g` is holomorphic
on `{1 < ‖z‖}`, `1 < r` and `‖g z‖ < ‖ζ‖` for all `z` with `‖z‖ = r`, then the winding number of
the curve `z ↦ g z` about `ζ` along `‖z‖ = r` is `0`. -/
theorem wind_eq_zero_of_norm_lt {g : ℂ → ℂ} {ζ : ℂ} {r : ℝ} (hr : 1 < r)
    (hg : ∀ z : ℂ, 1 < ‖z‖ → AnalyticAt ℂ g z)
    (hbd : ∀ z : ℂ, ‖z‖ = r → ‖g z‖ < ‖ζ‖) :
    wind g r ζ = 0 := by
  have hr0 : 0 < r := by linarith
  rcases eq_or_ne ζ 0 with rfl | hζ
  · exfalso
    have h := hbd (r : ℂ) (by simp [abs_of_pos hr0])
    have h0 : ‖g (r : ℂ)‖ < 0 := by simpa using h
    linarith [norm_nonneg (g (r : ℂ))]
  · rw [wind]
    have key : ∀ θ : ℝ, HasDerivAt (fun u : ℂ => Complex.log ((g u - ζ) * (-ζ⁻¹)))
        ((fun z : ℂ => deriv g z / (g z - ζ)) (circleMap 0 r θ)) (circleMap 0 r θ) := by
      intro θ
      have hzn : ‖circleMap 0 r θ‖ = r := by rw [norm_circleMap_zero, abs_of_pos hr0]
      have h1z : 1 < ‖circleMap 0 r θ‖ := by rw [hzn]; exact hr
      have hh : ‖g (circleMap 0 r θ)‖ < ‖ζ‖ := hbd _ hzn
      exact hasDerivAt_logArg hζ hh ((hg _ h1z).differentiableAt.hasDerivAt)
    have hcont : ∀ θ : ℝ, ContinuousAt (fun z : ℂ => deriv g z / (g z - ζ)) (circleMap 0 r θ) := by
      intro θ
      have hzn : ‖circleMap 0 r θ‖ = r := by rw [norm_circleMap_zero, abs_of_pos hr0]
      have h1z : 1 < ‖circleMap 0 r θ‖ := by rw [hzn]; exact hr
      exact continuousAt_wind_integrand hζ (hbd _ hzn) (hg _ h1z)
    rw [circleIntegral_eq_zero_of_hasDerivAt hcont key, mul_zero]

end Work.Repel.Koebe
