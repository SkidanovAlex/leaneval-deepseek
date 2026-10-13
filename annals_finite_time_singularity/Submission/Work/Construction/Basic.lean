/-
# The CONSTRUCTION area: elementary API of the profile `F_*`, the singular part `Θ` and `AK`

Basic calculus and algebra about the objects defined in `Submission/Work/Construction/Defs.lean`:

* `mul_L12dens_eq_FK`  : `z ∂_z L₁₂(F) = - (F,K)_{L²_θ}` (the sign comes from `L₁₂dens`);
* `pth_Fstar_eq`, `Dz_Fstar_eq`, `Fstar_sub_DzFstar`, `Fstar_stationary_identity` : the
  derivatives of the profile `F_*` and the identity `F_* + z∂_zF_* - (1/α)L₁₂(F_*)F_* = 0`
  of the paper (tex 1347);
* `pth_Theta_eq`, `Dz_Theta_eq` : the derivatives of the singular part
  `Θ = (1/(4α)) sin(2θ) L₁₂(F)`;
* `L12dens_AK`, `L12_AK_eq_one` : `L₁₂(Γ(θ)/c · 2z²/(1+z)³)(0) = 1`, the identity that makes
  the projector `𝕡` kernel-preserving.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Submission.Work.Construction.Defs
import Submission.Work.Construction.L12_Fstar_eq
import Submission.Work.FM.Core
import Submission.Work.FM.Core2
import Submission.Work.Spaces.c_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Construction

set_option autoImplicit false

/-! ## General helpers for the derivatives of a separated function `a(z) · b(θ)` -/

theorem deriv_const_mul_fun {a : ℝ} {b : ℝ → ℝ} (x : ℝ) :
    deriv (fun t : ℝ => a * b t) x = a * deriv b x := deriv_const_mul_field a

theorem deriv_mul_const_fun {a : ℝ} {b : ℝ → ℝ} (x : ℝ) :
    deriv (fun t : ℝ => b t * a) x = deriv b x * a := deriv_mul_const_field a

/-- `∂_θ (a(z) b(θ)) = a(z) ∂_θ b(θ)`. -/
theorem pth_mul_radial {a b : ℝ → ℝ} (z θ : ℝ) :
    Work.Spaces.pth (fun z θ => a z * b θ) z θ = a z * deriv b θ := by
  rw [Work.Spaces.pth]
  beta_reduce
  exact deriv_const_mul_fun θ

/-- `∂_z (a(z) b(θ)) = (∂_z a(z)) b(θ)`. -/
theorem pz_mul_radial {a b : ℝ → ℝ} (z θ : ℝ) :
    Work.Spaces.pz (fun z θ => a z * b θ) z θ = deriv a z * b θ := by
  rw [Work.Spaces.pz]
  beta_reduce
  exact deriv_mul_const_fun (a := b θ) (b := a) z

/-- `∂_θ sin(2θ) = 2 cos(2θ)`. -/
theorem deriv_sin_two (θ : ℝ) : deriv (fun t : ℝ => Real.sin (2 * t)) θ
    = 2 * Real.cos (2 * θ) := by
  have h1 : HasDerivAt (fun t : ℝ => 2 * t) 2 θ := by
    simpa using (hasDerivAt_id' (𝕜 := ℝ) θ).const_mul (2 : ℝ)
  have h : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (Real.cos (2 * θ) * 2) θ :=
    (Real.hasDerivAt_sin (2 * θ)).comp θ h1
  rw [h.deriv]
  ring

/-! ## `z ∂_z L₁₂(F)(z) = - (F,K)_{L²_θ}(z)` -/

theorem mul_L12dens_eq_FK {F : ℝ → ℝ → ℝ} {z : ℝ} (hz : z ≠ 0) :
    z * L12dens F z = FK F z := by
  rw [L12dens, FK, Work.FM.L12dens]
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun (s := Work.Spaces.Iθ) measurableSet_Icc
    (fun θ _ => ?_)
  first | (field_simp; ring) | field_simp | ring

/-! ## The derivatives of the profile `F_*` -/

theorem pth_Fstar_eq {α z θ : ℝ} (hα : 0 < α) :
    Work.Spaces.pth (Fstar α) z θ
      = α * (deriv (fun t : ℝ => Work.Spaces.Gam α t) θ / Work.Spaces.c α)
        * Work.FM.Fstar z := by
  have hfun : Fstar α = fun z θ => ((α / Work.Spaces.c α) * Work.FM.Fstar z)
      * Work.Spaces.Gam α θ := by
    funext z θ; rw [Fstar]; ring
  rw [hfun, pth_mul_radial]
  ring

theorem Dz_Fstar_eq {α z θ : ℝ} (hα : 0 < α) (hz : -1 < z) :
    Work.Spaces.Dz (Fstar α) z θ
      = α * (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z * (1 - z) / (1 + z) ^ 3) := by
  have hfun : Fstar α = fun z θ => Work.FM.Fstar z
      * (α * (Work.Spaces.Gam α θ / Work.Spaces.c α)) := by
    funext z θ; rw [Fstar]; ring
  rw [Work.Spaces.Dz, hfun, pz_mul_radial, Work.FM.deriv_Fstar z hz]
  ring

/-- `F_* - z∂_zF_* = 2α · (Γ/c) · 2z²/(1+z)³ = 2α · AK`; this is the combination that
appears when the modulation constant `λ` is chosen (tex 1357). -/
theorem Fstar_sub_DzFstar {α z θ : ℝ} (hα : 0 < α) (hz : -1 < z) :
    Fstar α z θ - Work.Spaces.Dz (Fstar α) z θ = 2 * α * AK α z θ := by
  have h1z : (1 : ℝ) + z ≠ 0 := ne_of_gt (by linarith)
  rw [Dz_Fstar_eq hα hz, AK, Fstar, Work.FM.Fstar]
  rcases eq_or_ne (Work.Spaces.c α) 0 with hc | hc
  · simp [hc]
  · field_simp
    ring

/-- **The paper's identity (tex 1347)**: `F_* + z∂_zF_* - (1/α)L₁₂(F_*)F_* = 0`. -/
theorem Fstar_stationary_identity {α z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 ≤ z) :
    Fstar α z θ + Work.Spaces.Dz (Fstar α) z θ
      - (1 / α) * L12 (Fstar α) z * Fstar α z θ = 0 := by
  have hc : Work.Spaces.c α ≠ 0 := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    intro h0; rw [h0] at h; norm_num at h
  have h1z : (1 : ℝ) + z ≠ 0 := ne_of_gt (by linarith)
  rw [Dz_Fstar_eq hα (by linarith), L12_Fstar_eq hα hα1 hz, Fstar, Work.FM.Fstar]
  first | (field_simp; ring) | field_simp | ring

/-! ## The derivatives of the singular part `Θ` -/

/-- `∂_θ Θ = (1/(2α)) cos(2θ) L₁₂(F)`. -/
theorem pth_Theta_eq {α : ℝ} (hα : 0 < α) {F : ℝ → ℝ → ℝ} (z θ : ℝ) :
    Work.Spaces.pth (Theta α F) z θ = (1 / (2 * α)) * Real.cos (2 * θ) * L12 F z := by
  have hfun : Theta α F = fun z θ => L12 F z * ((1 / (4 * α)) * Real.sin (2 * θ)) := by
    funext z θ; rw [Theta, s2]; ring
  rw [hfun, pth_mul_radial]
  have hsin : deriv (fun t : ℝ => (1 / (4 * α)) * Real.sin (2 * t)) θ
      = (1 / (4 * α)) * (2 * Real.cos (2 * θ)) := by
    rw [deriv_const_mul_field (v := fun s : ℝ => Real.sin (2 * s)) (u := (1 / (4 * α))),
      deriv_sin_two]
  rw [hsin]
  first | (field_simp; ring) | field_simp | ring

/-- `z∂_z Θ = -(1/(4α)) sin(2θ) (F,K)_{L²_θ}`, i.e. `∂_z L₁₂(F) = -L₁₂density(F)`. -/
theorem Dz_Theta_eq {α z θ : ℝ} {F : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hint : MeasureTheory.IntegrableOn (L12dens F) (Set.Ioi 0))
    (hcont : ContinuousAt (L12dens F) z) (hz : 0 < z) :
    Work.Spaces.Dz (Theta α F) z θ
      = -(1 / (4 * α)) * s2 θ * FK F z := by
  have hder : HasDerivAt (fun r : ℝ => L12 F r) (-(L12dens F z)) z :=
    Work.FM.hasDerivAt_L12 hint hcont hz
  have hfun : Theta α F = fun z θ => L12 F z * ((1 / (4 * α)) * s2 θ) := by
    funext z θ; rw [Theta]; ring
  have hpz : Work.Spaces.pz (Theta α F) z θ = -(L12dens F z) * ((1 / (4 * α)) * s2 θ) := by
    rw [hfun, pz_mul_radial, hder.deriv]
  rw [Work.Spaces.Dz, hpz,
    show z * (-(L12dens F z) * ((1 / (4 * α)) * s2 θ))
      = -(1 / (4 * α)) * s2 θ * (z * L12dens F z) by ring,
    mul_L12dens_eq_FK (ne_of_gt hz)]

/-! ## The projector profile `AK` -/

theorem L12dens_AK {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (s : ℝ) :
    L12dens (AK α) s = 2 * s / (1 + s) ^ 3 := by
  have hc : Work.Spaces.c α ≠ 0 := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    intro h0; rw [h0] at h; norm_num at h
  rw [L12dens, Work.FM.L12dens]
  rcases eq_or_ne s 0 with rfl | hs
  · simp [AK]
  · have hpoint : (fun θ : ℝ => Work.Spaces.K θ * AK α s θ / s)
        = fun θ : ℝ => ((Work.Spaces.Gam α θ * Work.Spaces.K θ) / Work.Spaces.c α)
            * (2 * s / (1 + s) ^ 3) := by
      funext θ
      rw [AK]
      first | (field_simp; ring) | field_simp | ring
    rw [hpoint, MeasureTheory.integral_mul_const]
    have hcint : (∫ a in Set.Icc 0 (Real.pi / 2),
        Work.Spaces.Gam α a * Work.Spaces.K a / Work.Spaces.c α) = 1 := by
      rw [MeasureTheory.integral_div]
      have hval : (∫ a in Set.Icc 0 (Real.pi / 2), Work.Spaces.Gam α a * Work.Spaces.K a)
          = Work.Spaces.c α := rfl
      rw [hval, div_self hc]
    rw [hcint, one_mul]

/-- The improper integral `∫_0^∞ 2s/(1+s)³ ds = 1`. -/
theorem integral_Ioi_two_mul_div_cube :
    ∫ s in Set.Ioi (0 : ℝ), 2 * s / (1 + s) ^ 3 = 1 := by
  have key := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg'
    (g := fun t : ℝ => -2 / (1 + t) + 1 / (1 + t) ^ 2)
    (g' := fun t : ℝ => 2 * t / (1 + t) ^ 3) (a := 0) (l := 0) ?_ ?_ ?_
  · rw [key]
    norm_num
  · intro x hx
    have hx0 : 0 ≤ x := hx
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
  · intro x hx
    have hx0 : 0 < x := hx
    have hx1 : (0 : ℝ) < 1 + x := by linarith
    positivity
  · have h1 : Tendsto (fun t : ℝ => (1 : ℝ) + t) atTop atTop :=
      tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id
    have h2 : Tendsto (fun t : ℝ => ((1 : ℝ) + t)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp h1
    have h3 : Tendsto (fun t : ℝ => ((1 : ℝ) + t)⁻¹ ^ 2) atTop (𝓝 0) := by
      simpa using h2.pow 2
    have h4 := (h2.const_mul (-2 : ℝ)).add h3
    simpa [div_eq_mul_inv, inv_pow] using h4

/-- **`L₁₂(AK)(0) = 1`**: the projector profile `(Γ/c) 2z²/(1+z)³` is the (unique) radial
profile whose `L₁₂`-value at `0` is `1`, so that `𝕡` removes the `L₁₂(·)(0)`-component. -/
theorem L12_AK_eq_one {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    L12 (AK α) 0 = 1 := by
  rw [L12, Work.FM.L12]
  rw [MeasureTheory.setIntegral_congr_fun (s := Set.Ioi 0) measurableSet_Ioi
    (fun s _ => show Work.FM.L12dens Work.Spaces.K (AK α) s = 2 * s / (1 + s) ^ 3
      from L12dens_AK hα hα1 s)]
  exact integral_Ioi_two_mul_div_cube

end Work.Construction
