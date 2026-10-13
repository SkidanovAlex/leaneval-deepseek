/-
# The projector `𝕡` kills the `L₁₂(·)(0)`-component

`Work.Coercivity.Proj α f = f - (Γ(θ)/c)(2z²/(1+z)³) L₁₂(f)(0)` is the projector of
Elgindi's §"Linearization with angular transport": its purpose is to remove the value of
`L₁₂(·)` at the origin.  This file proves exactly that.

Write `AK α z θ = (Γ(θ)/c) 2z²/(1+z)³`, so that `𝕡 f = f - L₁₂(f)(0)·AK α` pointwise, and
note `AK α` is a *separable* profile `a(z)b(θ)`.  Then

* `Proj_L12dens` : for `s > 0` the angular density of `𝕡 f` is the density of `f` minus
  the constant `L₁₂(f)(0)` times `2s/(1+s)³`.  The reason is that the θ-integral of the
  correction is `∫_{Iθ} K(θ)Γ(θ)/c = c/c = 1` (definition of `c`) together with
  `(2s²/(1+s)³)/s = 2s/(1+s)³`;
* `integral_Ioi_two_mul_div_cube`, `integrableOn_two_mul_div_cube` : the correction profile
  `2s/(1+s)³` is integrable on `(0,∞)` with integral `1` (antiderivative
  `s ↦ -2/(1+s) + 1/(1+s)²`, which vanishes at `+∞` and equals `-1` at `s = 0`);
* `Proj_L12f_zero` : integrating the density identity,
  `L₁₂(𝕡 f)(0) = L₁₂(f)(0) - L₁₂(f)(0)·1 = 0`.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.FM.Core

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## The angular data -/

/-- The angular interval `Iθ` is measurable (it is `Icc 0 (π/2)`). -/
private theorem measurableSet_Iθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc

/-- The angular average of the projector's angular profile is `1`:
`∫_{Iθ} K(θ)Γ(θ)/c = c/c = 1`. -/
theorem integral_KGam_div_c (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.Gam α θ / Work.Spaces.c α) = 1 := by
  have hc : Work.Spaces.c α ≠ 0 := c_ne_zero hα hα1
  rw [MeasureTheory.integral_div]
  have hcint : (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.Gam α θ)
      = Work.Spaces.c α := by
    rw [Work.Spaces.c]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Iθ (fun θ _ => mul_comm _ _)
  rw [hcint, div_self hc]

/-! ## The density identity -/

/-- **The angular density of the projected profile.**  For `s > 0`,
`L₁₂dens(𝕡 f)(s) = L₁₂dens(f)(s) - L₁₂(f)(0)·2s/(1+s)³`.

Indeed `𝕡 f = f - L₁₂(f)(0)·AK α` pointwise, with
`AK α z θ = (Γ(θ)/c) 2z²/(1+z)³`; integrating the correction against `K(θ)/s` gives
`L₁₂(f)(0)·(2s²/(1+s)³)/s · ∫_{Iθ} K(θ)Γ(θ)/c = L₁₂(f)(0)·2s/(1+s)³`. -/
theorem Proj_L12dens (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (h2 : ∀ s ∈ Set.Ioi (0:ℝ),
      MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * f s θ / s) Work.Spaces.Iθ)
    {s : ℝ} (hs : s ∈ Set.Ioi (0:ℝ)) :
    Work.FM.L12dens Work.Spaces.K (Work.Coercivity.Proj α f) s
      = Work.FM.L12dens Work.Spaces.K f s
        - Work.Coercivity.L12f f 0 * (2 * s / (1 + s) ^ 3) := by
  have hspos : (0 : ℝ) < s := hs
  have hs0 : s ≠ 0 := ne_of_gt hspos
  have h1s : (1 : ℝ) + s ≠ 0 := by positivity
  have hc : Work.Spaces.c α ≠ 0 := c_ne_zero hα hα1
  -- the correction slice is integrable (it is a constant multiple of `ΓK`)
  have hcorr : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Coercivity.L12f f 0 * (2 * s / (1 + s) ^ 3))
        * (Work.Spaces.K θ * Work.Spaces.Gam α θ / Work.Spaces.c α)) Work.Spaces.Iθ :=
    MeasureTheory.IntegrableOn.congr_fun
      ((Work.Spaces.CAux.integrableOn_GamK α hα).const_mul
        (Work.Coercivity.L12f f 0 * (2 * s / (1 + s) ^ 3) / Work.Spaces.c α))
      (fun θ _ => by first | (field_simp; ring) | field_simp | ring)
      measurableSet_Iθ
  have hGval := integral_KGam_div_c α hα hα1
  change ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Coercivity.Proj α f s θ / s
      = (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * f s θ / s)
        - Work.Coercivity.L12f f 0 * (2 * s / (1 + s) ^ 3)
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Iθ (show Set.EqOn
      (fun θ => Work.Spaces.K θ * Work.Coercivity.Proj α f s θ / s)
      (fun θ => Work.Spaces.K θ * f s θ / s
        - (Work.Coercivity.L12f f 0 * (2 * s / (1 + s) ^ 3))
          * (Work.Spaces.K θ * Work.Spaces.Gam α θ / Work.Spaces.c α))
      Work.Spaces.Iθ from fun θ _ => by
        simp only [Proj_eq]
        first | (field_simp; ring) | field_simp | ring)]
  rw [MeasureTheory.integral_sub (h2 s hs) hcorr, MeasureTheory.integral_const_mul, hGval,
    mul_one]

/-! ## The improper integral `∫_0^∞ 2s/(1+s)³ ds = 1` -/

/-- `d/ds (-2/(1+s) + 1/(1+s)²) = 2s/(1+s)³` for `s ≥ 0`. -/
theorem hasDerivAt_frac (x : ℝ) (hx : 0 ≤ x) :
    HasDerivAt (fun t : ℝ => -2 / (1 + t) + 1 / (1 + t) ^ 2) (2 * x / (1 + x) ^ 3) x := by
  have hx1 : (1 : ℝ) + x ≠ 0 := by positivity
  have h1 : HasDerivAt (fun t : ℝ => -2 / (1 + t)) (2 / (1 + x) ^ 2) x := by
    simpa using Work.FM.hasDerivAt_div_add_const (-2) 1 x hx1
  have h2 : HasDerivAt (fun t : ℝ => 1 / (1 + t) ^ 2) (-2 / (1 + x) ^ 3) x := by
    have hnum : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 x := hasDerivAt_const x 1
    have hden : HasDerivAt (fun t : ℝ => (1 + t) ^ 2) (2 * (1 + x)) x :=
      Work.FM.hasDerivAt_one_add_sq x
    have h := hnum.div hden (pow_ne_zero 2 hx1)
    convert h using 1
    first | (field_simp; ring) | field_simp | ring
  have h3 : HasDerivAt (fun t : ℝ => -2 / (1 + t) + 1 / (1 + t) ^ 2)
      (2 / (1 + x) ^ 2 + -2 / (1 + x) ^ 3) x := h1.add h2
  have hve : 2 / (1 + x) ^ 2 + -2 / (1 + x) ^ 3 = 2 * x / (1 + x) ^ 3 := by
    first | (field_simp; ring) | field_simp | ring
  rw [hve] at h3
  exact h3

/-- The antiderivative `-2/(1+s) + 1/(1+s)²` tends to `0` at `+∞`. -/
theorem tendsto_frac :
    Tendsto (fun t : ℝ => -2 / (1 + t) + 1 / (1 + t) ^ 2) atTop (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => (1 : ℝ) + t) atTop atTop :=
    tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id
  have h2 : Tendsto (fun t : ℝ => ((1 : ℝ) + t)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp h1
  have h3 : Tendsto (fun t : ℝ => ((1 : ℝ) + t)⁻¹ ^ 2) atTop (𝓝 0) := by
    simpa using h2.pow 2
  have h4 := (h2.const_mul (-2 : ℝ)).add h3
  simpa [div_eq_mul_inv, inv_pow] using h4

/-- `2s/(1+s)³` is nonnegative on `(0,∞)`. -/
theorem two_mul_div_cube_nonneg {x : ℝ} (hx : x ∈ Set.Ioi (0:ℝ)) :
    0 ≤ 2 * x / (1 + x) ^ 3 := by
  have hx' : (0 : ℝ) < x := hx
  have hx1 : (0 : ℝ) < 1 + x := by linarith
  positivity

/-- The improper integral `∫_0^∞ 2s/(1+s)³ ds = 1`. -/
theorem integral_Ioi_two_mul_div_cube :
    ∫ s in Set.Ioi (0 : ℝ), 2 * s / (1 + s) ^ 3 = 1 := by
  have key := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg'
    (g := fun t : ℝ => -2 / (1 + t) + 1 / (1 + t) ^ 2)
    (g' := fun t : ℝ => 2 * t / (1 + t) ^ 3) (a := 0) (l := 0)
    (fun x hx => hasDerivAt_frac x hx) (fun x hx => two_mul_div_cube_nonneg hx) tendsto_frac
  rw [key]
  norm_num

/-- The correction profile `s ↦ 2s/(1+s)³` is integrable on `(0,∞)` (its integral is `1`,
see `integral_Ioi_two_mul_div_cube`). -/
theorem integrableOn_two_mul_div_cube :
    MeasureTheory.IntegrableOn (fun s : ℝ => 2 * s / (1 + s) ^ 3) (Set.Ioi 0) := by
  have key := MeasureTheory.integrableOn_Ioi_deriv_of_nonneg'
    (g := fun t : ℝ => -2 / (1 + t) + 1 / (1 + t) ^ 2)
    (g' := fun t : ℝ => 2 * t / (1 + t) ^ 3) (a := 0) (l := 0)
    (fun x hx => hasDerivAt_frac x hx) (fun x hx => two_mul_div_cube_nonneg hx) tendsto_frac
  exact MeasureTheory.IntegrableOn.congr_fun key (fun x _ => rfl) measurableSet_Ioi

/-! ## The main theorem -/

/-- **The projector removes the value of `L₁₂` at the origin**:
`L₁₂(𝕡 f)(0) = 0`. -/
theorem Proj_L12f_zero (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (h1 : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K f) (Set.Ioi 0))
    (h2 : ∀ s ∈ Set.Ioi (0:ℝ),
      MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * f s θ / s) Work.Spaces.Iθ)
    (h3 : MeasureTheory.IntegrableOn
      (Work.FM.L12dens Work.Spaces.K (Work.Coercivity.Proj α f)) (Set.Ioi 0)) :
    Work.Coercivity.L12f (Work.Coercivity.Proj α f) 0 = 0 := by
  have hdens : ∀ s ∈ Set.Ioi (0:ℝ),
      Work.FM.L12dens Work.Spaces.K (Work.Coercivity.Proj α f) s
        = Work.FM.L12dens Work.Spaces.K f s
          - Work.Coercivity.L12f f 0 * (2 * s / (1 + s) ^ 3) :=
    fun s hs => Proj_L12dens α hα hα1 f h2 hs
  have hcorr : MeasureTheory.IntegrableOn
      (fun s : ℝ => Work.Coercivity.L12f f 0 * (2 * s / (1 + s) ^ 3)) (Set.Ioi 0) :=
    (integrableOn_two_mul_div_cube.const_mul _)
  have hmain : (∫ s in Set.Ioi (0:ℝ),
        Work.FM.L12dens Work.Spaces.K (Work.Coercivity.Proj α f) s)
      = ∫ s in Set.Ioi (0:ℝ), (Work.FM.L12dens Work.Spaces.K f s
          - Work.Coercivity.L12f f 0 * (2 * s / (1 + s) ^ 3)) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hdens
  change ∫ s in Set.Ioi (0:ℝ), Work.FM.L12dens Work.Spaces.K (Work.Coercivity.Proj α f) s
    = 0
  rw [hmain, MeasureTheory.integral_sub h1 hcorr, MeasureTheory.integral_const_mul,
    integral_Ioi_two_mul_div_cube, mul_one]
  change Work.Coercivity.L12f f 0 - Work.Coercivity.L12f f 0 = 0
  ring

end Work.Coercivity
