/-
# The fundamental model: derivative of `L₁₂^K` and the self-similar family solving the model
-/

import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FM.Defs
import Submission.Work.FM.Core

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Work.FM

/-! ## `∂_ρ L₁₂^K(f) = - L12dens K f` -/

theorem hasDerivAt_L12 {K : ℝ → ℝ} {f : ℝ → ℝ → ℝ} {a ρ : ℝ}
    (hint : IntegrableOn (L12dens K f) (Ioi a))
    (hcont : ContinuousAt (L12dens K f) ρ) (ha : a < ρ) :
    HasDerivAt (fun ρ => L12 K f ρ) (-(L12dens K f ρ)) ρ := by
  have hInt : IntervalIntegrable (L12dens K f) volume a ρ := by
    rw [intervalIntegrable_iff, uIoc_of_le ha.le]
    exact hint.mono_set Ioc_subset_Ioi_self
  have hmeas : StronglyMeasurableAtFilter (L12dens K f) (𝓝 ρ) volume :=
    ⟨Ioi a, Ioi_mem_nhds ha, hint.aestronglyMeasurable⟩
  have hd := intervalIntegral.integral_hasDerivAt_right hInt hmeas hcont
  have hc : HasDerivAt (fun _ : ℝ => ∫ s in Ioi a, L12dens K f s) 0 ρ :=
    hasDerivAt_const ρ _
  have hsub := hc.sub hd
  have hev : (fun u : ℝ => L12 K f u)
      =ᶠ[𝓝 ρ] (fun u => (∫ s in Ioi a, L12dens K f s) - ∫ s in a..u, L12dens K f s) := by
    filter_upwards [Ioi_mem_nhds ha] with u hu
    rw [L12]
    have h1 : IntegrableOn (L12dens K f) (Ioi u) := hint.mono_set (Ioi_subset_Ioi hu.le)
    have hgoal : (∫ s in a..u, L12dens K f s) + (∫ s in Ioi u, L12dens K f s)
        = ∫ s in Ioi a, L12dens K f s :=
      intervalIntegral.integral_interval_add_Ioi (f := L12dens K f) (a := a) (b := u) hint h1
    linarith
  have hfun : ((fun x : ℝ => ∫ s in Ioi a, L12dens K f s) - fun u => ∫ x in a..u, L12dens K f x)
      = fun u : ℝ => (∫ s in Ioi a, L12dens K f s) - ∫ s in a..u, L12dens K f s := by
    funext u; simp [Pi.sub_apply]
  rw [hev.hasDerivAt_iff, ← hfun]
  convert hsub using 1 <;> (first | ring_nf | (funext u; simp))

/-! ## The self-similar profile as a function of `t` -/

/-- The self-similar family, in the form in which it is differentiated in `t`. -/
theorem selfSim_eq_inv {K Γ : ℝ → ℝ} {α ρ θ t : ℝ} (hρ : 0 ≤ ρ) (ht : t < 1) :
    selfSim K Γ α ρ θ t = 2 * α * (Γ θ / cK K Γ) * ρ ^ α / (1 - t + ρ ^ α) ^ 2 := by
  have h1t : (1 : ℝ) - t ≠ 0 := by linarith
  have hD : 1 - t + ρ ^ α ≠ 0 := by
    have h : 0 < 1 - t := by linarith
    have h2 : 0 ≤ ρ ^ α := Real.rpow_nonneg hρ α
    positivity
  unfold selfSim Fstarp
  first | (field_simp; ring) | field_simp | ring_nf

/-- `d/dt (c/(1-t+A)²) = 2c/(1-t+A)³`. -/
theorem hasDerivAt_const_div_sq (c A t : ℝ) (h : 1 - t + A ≠ 0) :
    HasDerivAt (fun y : ℝ => c / (1 - y + A) ^ 2) (2 * c / (1 - t + A) ^ 3) t := by
  have hlin : HasDerivAt (fun y : ℝ => 1 - y + A) (-1) t := by
    have hh : HasDerivAt (fun y : ℝ => y) 1 t := hasDerivAt_id' (𝕜 := ℝ) t
    have h2 := ((hasDerivAt_const t (1 : ℝ)).sub hh).add_const A
    convert h2 using 1 <;> (first | (funext y; simp) | ring_nf)
  have hsq : HasDerivAt (fun y : ℝ => (1 - y + A) ^ 2) (-(2 * (1 - t + A))) t := by
    have h2 := hlin.pow 2
    convert h2 using 1 <;> (first | (funext y; simp) | ring_nf)
  have hne : (1 - t + A) ^ 2 ≠ 0 := pow_ne_zero 2 h
  have hinv : HasDerivAt (fun y : ℝ => ((1 - y + A) ^ 2)⁻¹)
      (-(-(2 * (1 - t + A))) / ((1 - t + A) ^ 2) ^ 2) t := hsq.inv hne
  have hmul := hinv.const_mul c
  have hfun : (fun y : ℝ => c / (1 - y + A) ^ 2) = fun y => c * ((1 - y + A) ^ 2)⁻¹ := by
    funext y; rw [div_eq_mul_inv]
  rw [hfun]
  have hval : c * (-(-(2 * (1 - t + A))) / ((1 - t + A) ^ 2) ^ 2) = 2 * c / (1 - t + A) ^ 3 := by
    first | (field_simp; ring) | field_simp | ring_nf
  rw [hval] at hmul
  exact hmul

/-- The derivative in `t` of the self-similar family, in the form needed for the
model equation (`∂_t f = f · L₁₂^K(f)`). -/
theorem hasDerivAt_selfSim {K Γ : ℝ → ℝ} {α ρ θ t : ℝ} (hρ : 0 ≤ ρ) (ht : t < 1) :
    HasDerivAt (fun s => selfSim K Γ α ρ θ s)
      (selfSim K Γ α ρ θ t * (2 / (1 - t + ρ ^ α))) t := by
  have hD : 1 - t + ρ ^ α ≠ 0 := by
    have h : 0 < 1 - t := by linarith
    have h2 : 0 ≤ ρ ^ α := Real.rpow_nonneg hρ α
    positivity
  have key := hasDerivAt_const_div_sq (2 * α * (Γ θ / cK K Γ) * ρ ^ α) (ρ ^ α) t hD
  have hev : (fun s : ℝ => selfSim K Γ α ρ θ s)
      =ᶠ[𝓝 t] fun s => 2 * α * (Γ θ / cK K Γ) * ρ ^ α / (1 - s + ρ ^ α) ^ 2 := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact selfSim_eq_inv hρ hs
  rw [hev.hasDerivAt_iff]
  rw [show selfSim K Γ α ρ θ t * (2 / (1 - t + ρ ^ α))
      = 2 * (2 * α * (Γ θ / cK K Γ) * ρ ^ α) / (1 - t + ρ ^ α) ^ 3 from by
    rw [selfSim_eq_inv hρ ht]
    first | (field_simp; ring) | field_simp | ring_nf]
  exact key

/-- **The self-similar family solves the fundamental model** (Lemma `FMSelfSimilar`
of the paper), conditional on the evaluation of `L₁₂^K` on the family. -/
theorem isModelSolution_selfSim_of_L12 {K Γ : ℝ → ℝ} {α : ℝ}
    (hL12 : ∀ ρ, 0 ≤ ρ → ∀ t, t < 1 →
      L12 K (fun s θ => selfSim K Γ α s θ t) ρ = 2 / (1 - t + ρ ^ α)) :
    IsModelSolution K (selfSim K Γ α) := by
  intro ρ θ t hρ ht
  rw [hL12 ρ hρ t ht]
  exact hasDerivAt_selfSim hρ ht

/-- `d/dt (c/(1-t+A)) = c/(1-t+A)²`. -/
theorem hasDerivAt_const_div_lin (c A t : ℝ) (h : 1 - t + A ≠ 0) :
    HasDerivAt (fun y : ℝ => c / (1 - y + A)) (c / (1 - t + A) ^ 2) t := by
  have hlin : HasDerivAt (fun y : ℝ => 1 - y + A) (-1) t := by
    have hh : HasDerivAt (fun y : ℝ => y) 1 t := hasDerivAt_id' (𝕜 := ℝ) t
    have h2 := ((hasDerivAt_const t (1 : ℝ)).sub hh).add_const A
    convert h2 using 1 <;> (first | (funext y; simp) | ring_nf)
  have hinv : HasDerivAt (fun y : ℝ => (1 - y + A)⁻¹) (-(-1) / (1 - t + A) ^ 2) t :=
    hlin.inv h
  have hmul := hinv.const_mul c
  rw [show (fun y : ℝ => c / (1 - y + A)) = fun y => c * (1 - y + A)⁻¹ from by
    funext y; rw [div_eq_mul_inv]]
  rw [show c * (-(-1) / (1 - t + A) ^ 2) = c / (1 - t + A) ^ 2 from by ring] at hmul
  exact hmul

/-- The per-`ρ` Riccati equation for the self-similar family: the quantity
`L₁₂^K(f)(ρ,·)` blows up like `2/(1-t+ρ^α)`, and satisfies `v' = v²/2`
(paper line 463 specialised to Lemma `FMSelfSimilar`). -/
theorem hasDerivAt_L12_selfSim_of_L12 {K Γ : ℝ → ℝ} {α ρ t : ℝ} (hρ : 0 ≤ ρ) (ht : t < 1)
    (hL12 : ∀ s, s < 1 → L12 K (fun r θ => selfSim K Γ α r θ s) ρ = 2 / (1 - s + ρ ^ α)) :
    HasDerivAt (fun s => L12 K (fun r θ => selfSim K Γ α r θ s) ρ)
      (L12 K (fun r θ => selfSim K Γ α r θ t) ρ ^ 2 / 2) t := by
  have hD : 1 - t + ρ ^ α ≠ 0 := by
    have h : 0 < 1 - t := by linarith
    have h2 : 0 ≤ ρ ^ α := Real.rpow_nonneg hρ α
    positivity
  have hev : (fun s => L12 K (fun r θ => selfSim K Γ α r θ s) ρ)
      =ᶠ[𝓝 t] fun s => 2 / (1 - s + ρ ^ α) := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact hL12 s hs
  rw [hev.hasDerivAt_iff, hL12 t ht]
  rw [show (2 / (1 - t + ρ ^ α)) ^ 2 / 2 = 2 / (1 - t + ρ ^ α) ^ 2 from by
    first | (field_simp; ring) | field_simp | ring_nf]
  exact hasDerivAt_const_div_lin 2 (ρ ^ α) t hD

/-- The blow-up of the fundamental-model solution at `t → 1`: the second factor of
the paper's `d/dt L₁₂^K(f)(0) = ½ (L₁₂^K(f)(0))²`. -/
theorem selfSim_blowup_of_L12 {K Γ : ℝ → ℝ} {α : ℝ}
    (hL12 : ∀ t, t < 1 → L12 K (fun s θ => selfSim K Γ α s θ t) 0 = 2 / (1 - t)) :
    Tendsto (fun t => L12 K (fun s θ => selfSim K Γ α s θ t) 0) (nhdsWithin 1 (Iio 1)) atTop := by
  have hev : (fun t => L12 K (fun s θ => selfSim K Γ α s θ t) 0)
      =ᶠ[nhdsWithin 1 (Iio 1)] fun t => 2 / (1 - t) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hL12 t ht
  exact tendsto_two_div_one_sub.congr' hev.symm

end Work.FM
