import Mathlib
import Submission.Work.RPB.B1.AreaPosDefs
import Submission.Work.RPB.B1.windInt_continuousOn

/-!
# `windInt` is continuous off the curve and vanishes far away

This file proves

`Work.RPB.B1.windInt_continuousOn_and_zero_far`: for a `C^1`, `2π`-periodic curve `u : ℝ → ℂ`,

* `windInt u` is continuous on the complement of `Set.range u`, and
* `windInt u q = 0` as soon as `‖q‖` exceeds a bound `M` on `‖u‖`.

The continuity half is proved in `Submission.Work.RPB.B1.windInt_continuousOn` (continuity of a
parameter integral, by dominated convergence over the compact interval `[0, 2π]`).

The vanishing half is the content of this file.  If `‖u t‖ ≤ M < ‖q‖` then `‖u t / q‖ < 1`, so the
curve `t ↦ 1 - u t / q` stays inside the disc of radius `1` centred at `1`, hence inside the slit
plane, and the principal logarithm `t ↦ log (1 - u t / q)` is a primitive of the winding integrand:
its derivative is `u'(t) / (u(t) - q)`.  By `2π`-periodicity that primitive takes the same value at
`2π` and at `0`, so the fundamental theorem of calculus gives `∮_0^{2π} u'/(u - q) = 0`, and taking
imaginary parts (a continuous linear map) kills the winding integral itself.
-/

set_option autoImplicit false

noncomputable section

open scoped Interval
open MeasureTheory

namespace Work.RPB.B1

/-- Algebraic normal form for the logarithmic-derivative computation:
`(-(c/q)) / (1 - z/q) = c/(z - q)` for `q ≠ 0` and `z ≠ q`. -/
private lemma neg_div_div_sub (c z q : ℂ) (hq : q ≠ 0) (hz : z - q ≠ 0) :
    (-(c / q)) / (1 - z / q) = c / (z - q) := by
  have hne : (q - z) ≠ 0 := by
    have h := neg_ne_zero.mpr hz
    rwa [neg_sub] at h
  have h1 : (1 : ℂ) - z / q = (q - z) / q := by field_simp
  rw [h1]
  field_simp
  ring

/-- **The logarithmic primitive kills the winding integral.**  If `u` is `C^1` and `2π`-periodic and
`1 - u t / q` lies in the slit plane for every `t` (in particular `u t ≠ q` for every `t`), then
`∮_0^{2π} u'(t) / (u t - q) dt = 0`.

Indeed `t ↦ log (1 - u t / q)` is a primitive of the integrand (its derivative is
`(-(u' t / q)) / (1 - u t / q) = u' t / (u t - q)`), and by periodicity it has the same value at
`2π` and at `0`. -/
theorem integral_deriv_div_sub_eq_zero_of_slitPlane (u : ℝ → ℂ) (hu : ContDiff ℝ 1 u)
    (hper : ∀ t, u (t + 2 * Real.pi) = u t) {q : ℂ} (hq : q ≠ 0)
    (hslit : ∀ t, 1 - u t / q ∈ Complex.slitPlane) :
    ∫ t in (0 : ℝ)..(2 * Real.pi), deriv u t / (u t - q) = 0 := by
  have hsub : ∀ t, u t - q ≠ 0 := by
    intro t h
    have hne := Complex.slitPlane_ne_zero (hslit t)
    have hutq : u t = q := sub_eq_zero.mp h
    rw [hutq, div_self hq, sub_self] at hne
    exact hne rfl
  set F : ℝ → ℂ := fun t => Complex.log (1 - u t / q) with hFdef
  have hderiv : ∀ x, HasDerivAt F (deriv u x / (u x - q)) x := by
    intro x
    have hdu : HasDerivAt u (deriv u x) x :=
      (hu.differentiable one_ne_zero).differentiableAt.hasDerivAt
    have h1 : HasDerivAt (fun t => (1 : ℂ) - u t / q) (-(deriv u x / q)) x :=
      (hdu.div_const q).const_sub 1
    have h2 := h1.clog_real (hslit x)
    rw [hFdef]
    rw [show (-(deriv u x / q)) / (1 - u x / q) = deriv u x / (u x - q) from
      neg_div_div_sub _ _ _ hq (hsub x)] at h2
    exact h2
  have hint : IntervalIntegrable (fun t => deriv u t / (u t - q)) volume (0 : ℝ) (2 * Real.pi) := by
    have hc1 : Continuous (deriv u) := hu.continuous_deriv le_rfl
    refine ContinuousOn.intervalIntegrable ?_
    exact ContinuousOn.div hc1.continuousOn (hu.continuous.sub continuous_const).continuousOn
      (fun x _ => hsub x)
  have hFTC : ∫ t in (0 : ℝ)..(2 * Real.pi), deriv u t / (u t - q) = F (2 * Real.pi) - F 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x) hint
  have hFeq : F (2 * Real.pi) = F 0 := by
    have hp : u (2 * Real.pi) = u 0 := by simpa using hper 0
    simp only [hFdef, hp]
  rw [hFTC, hFeq, sub_self]

/-- **The winding integral vanishes outside a disc containing the curve.**  If `‖u t‖ ≤ M` for all
`t` and `M < ‖q‖`, then `windInt u q = 0`. -/
theorem windInt_eq_zero_of_norm_lt (u : ℝ → ℂ) (hu : ContDiff ℝ 1 u)
    (hper : ∀ t, u (t + 2 * Real.pi) = u t) {M : ℝ} (hM : ∀ t, ‖u t‖ ≤ M) {q : ℂ}
    (hq : M < ‖q‖) : windInt u q = 0 := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (u 0)) (hM 0)
  have hqpos : 0 < ‖q‖ := lt_of_le_of_lt hM0 hq
  have hq0 : q ≠ 0 := norm_pos_iff.mp hqpos
  have hslit : ∀ t, 1 - u t / q ∈ Complex.slitPlane := by
    intro t
    have hlt : ‖-(u t / q)‖ < 1 := by
      rw [norm_neg, norm_div, div_lt_one hqpos]
      exact lt_of_le_of_lt (hM t) hq
    have hh := Complex.mem_slitPlane_of_norm_lt_one (z := -(u t / q)) hlt
    simpa [sub_eq_add_neg] using hh
  have hsub : ∀ t, u t - q ≠ 0 := by
    intro t h
    have hne := Complex.slitPlane_ne_zero (hslit t)
    have hutq : u t = q := sub_eq_zero.mp h
    rw [hutq, div_self hq0, sub_self] at hne
    exact hne rfl
  have hint : IntervalIntegrable (fun t => deriv u t / (u t - q)) volume (0 : ℝ) (2 * Real.pi) := by
    have hc1 : Continuous (deriv u) := hu.continuous_deriv le_rfl
    refine ContinuousOn.intervalIntegrable ?_
    exact ContinuousOn.div hc1.continuousOn (hu.continuous.sub continuous_const).continuousOn
      (fun x _ => hsub x)
  have him : ∫ t in (0 : ℝ)..(2 * Real.pi), (deriv u t / (u t - q)).im = 0 := by
    have hcomp :=
      Complex.imCLM.intervalIntegral_comp_comm (f := fun t => deriv u t / (u t - q)) hint
    simp only [Complex.imCLM_apply] at hcomp
    rw [hcomp, integral_deriv_div_sub_eq_zero_of_slitPlane u hu hper hq0 hslit]
    simp
  rw [windInt, him, mul_zero]

theorem windInt_continuousOn_and_zero_far (u : ℝ → ℂ) (hu : ContDiff ℝ 1 u)
    (hper : ∀ t, u (t + 2 * Real.pi) = u t) :
    ContinuousOn (Work.RPB.B1.windInt u) ((Set.range u)ᶜ) ∧
      ∀ M : ℝ, (∀ t, ‖u t‖ ≤ M) → ∀ q : ℂ, M < ‖q‖ → Work.RPB.B1.windInt u q = 0 := by
  exact ⟨windInt_continuousOn u hu hper,
    fun M hM q hq => windInt_eq_zero_of_norm_lt u hu hper hM hq⟩

end Work.RPB.B1
