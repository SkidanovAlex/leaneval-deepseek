/-
# The fundamental model: the self-similar evaluation `L₁₂^K(f)(ρ,t) = 2/(1-t+ρ^α)`
-/

import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Submission.Work.FM.Defs
import Submission.Work.FM.Core
import Submission.Work.FM.Core2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Work.FM

/-! ## Monotonicity in `ρ` -/

theorem L12_antitone {K : ℝ → ℝ} {f : ℝ → ℝ → ℝ} {ρ₁ ρ₂ : ℝ}
    (hK : ∀ θ ∈ Icc 0 (Real.pi / 2), 0 ≤ K θ) (hf : ∀ s θ, 0 ≤ f s θ)
    (hρ₁ : 0 ≤ ρ₁) (h : ρ₁ ≤ ρ₂)
    (hint : IntegrableOn (L12dens K f) (Ioi ρ₁)) :
    L12 K f ρ₂ ≤ L12 K f ρ₁ := by
  rw [L12]
  refine setIntegral_mono_set (μ := volume) hint ?_ ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [L12dens]
    refine setIntegral_nonneg measurableSet_Icc (fun θ hθ => ?_)
    have hs0 : 0 < s := lt_of_le_of_lt hρ₁ hs
    exact div_nonneg (mul_nonneg (hK θ hθ) (hf s θ)) hs0.le
  · exact Filter.Eventually.of_forall fun x hx => Ioi_subset_Ioi h hx

/-! ## The energy identity `∫_ρ^∞ h V = V(ρ)²/2` behind the Riccati equation -/

theorem integral_Ioi_mul_of_hasDerivAt {V h : ℝ → ℝ} {ρ : ℝ}
    (hV : ∀ s ∈ Ioi ρ, HasDerivAt V (-(h s)) s)
    (hVρ : ContinuousWithinAt V (Ici ρ) ρ)
    (hintV : IntegrableOn (fun s => V s ^ 2) (Ioi ρ))
    (hint : IntegrableOn (fun s => h s * V s) (Ioi ρ))
    (htend : Tendsto V atTop (𝓝 0)) :
    ∫ s in Ioi ρ, h s * V s = V ρ ^ 2 / 2 := by
  have hderiv : ∀ s ∈ Ioi ρ, HasDerivAt (fun x : ℝ => -(V x ^ 2) / 2) (h s * V s) s := by
    intro s hs
    have h1 : HasDerivAt (fun x : ℝ => V x ^ 2) (-(2 * V s * h s)) s := by
      have h2 := (hV s hs).pow 2
      convert h2 using 1 <;> (first | (funext x; simp) | ring_nf)
    have h3 : HasDerivAt (fun x : ℝ => -(V x ^ 2) / 2) (-(-(2 * V s * h s)) / 2) s :=
      h1.neg.div_const 2
    convert h3 using 1 <;> (first | (funext x; simp) | ring_nf)
  have hcont : ContinuousWithinAt (fun x : ℝ => -(V x ^ 2) / 2) (Ici ρ) ρ := by
    have h1 : ContinuousWithinAt (fun x : ℝ => V x ^ 2) (Ici ρ) ρ := hVρ.pow 2
    have h2 : ContinuousWithinAt (fun x : ℝ => -(V x ^ 2) / 2) (Ici ρ) ρ :=
      (h1.neg).div_const 2
    convert h2 using 1 <;> (first | (funext x; simp) | ring_nf)
  have hInt : IntegrableOn (fun x : ℝ => -(V x ^ 2) / 2) (Ioi ρ) := hintV.neg.div_const 2
  have htend' : Tendsto (fun x : ℝ => -(V x ^ 2) / 2) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => V x ^ 2) atTop (𝓝 0) := by simpa using htend.pow 2
    have h2 : Tendsto (fun x : ℝ => -(V x ^ 2) / 2) atTop (𝓝 0) := by
      simpa using (h1.neg).div_const 2
    exact h2
  have key := integral_Ioi_of_hasDerivAt_of_tendsto (f := fun x : ℝ => -(V x ^ 2) / 2)
    (f' := fun x : ℝ => h x * V x) (a := ρ) (m := 0) hcont hderiv hint htend'
  rw [key]
  ring

/-! ## The substitution integral of the self-similar profile -/

theorem integral_Ioi_Fstarp_rpow {α ρ t : ℝ} (hα : 0 < α) (hρ : 0 ≤ ρ) (ht : t < 1) :
    ∫ s in Ioi ρ, Fstarp (s ^ α / (1 - t)) / s
      = (1 / α) * ((1 - t) / ((1 - t) + ρ ^ α)) := by
  have h1t : 0 < 1 - t := by linarith
  have hρa : 0 ≤ ρ ^ α := Real.rpow_nonneg hρ α
  have hρane : ρ ^ α ≠ 0 ∨ 0 < α := Or.inr hα
  -- Step 1: the substitution `s ↦ s^α`
  have hsub := integral_comp_rpow_Ioi_of_pos' (E := ℝ) (g := fun u : ℝ => Fstarp (u / (1 - t)) / (α * u))
    (p := α) hα (c := ρ ^ α) hρa
  rw [show (ρ ^ α) ^ α⁻¹ = ρ from by
    rw [← Real.rpow_mul hρ, mul_inv_cancel₀ hα.ne', Real.rpow_one]] at hsub
  have hpt : ∀ x ∈ Ioi ρ, (α * x ^ (α - 1)) • (Fstarp (x ^ α / (1 - t)) / (α * x ^ α))
      = Fstarp (x ^ α / (1 - t)) / x := by
    intro x hx
    have hx0 : 0 < x := lt_of_le_of_lt hρ hx.out
    rw [smul_eq_mul,
      show x ^ (α - 1) = x ^ α / x from by rw [Real.rpow_sub hx0, Real.rpow_one]]
    first | (field_simp; ring) | field_simp | ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioi hpt] at hsub
  rw [hsub]
  -- Step 2: the antiderivative of `u ↦ Fstarp (u/(1-t))/(α u)` on `Ioi (ρ^α)`
  have hden : (1 : ℝ) + ρ ^ α / (1 - t) ≠ 0 := by
    have h : 0 ≤ ρ ^ α / (1 - t) := div_nonneg hρa h1t.le
    positivity
  have hcont : ContinuousWithinAt (fun u : ℝ => -(1 / α) / (1 + u / (1 - t))) (Ici (ρ ^ α)) (ρ ^ α) := by
    have h1 : ContinuousWithinAt (fun u : ℝ => u / (1 - t)) (Ici (ρ ^ α)) (ρ ^ α) :=
      (continuousWithinAt_id.div_const _)
    have h2 : ContinuousWithinAt (fun u : ℝ => 1 + u / (1 - t)) (Ici (ρ ^ α)) (ρ ^ α) :=
      continuousWithinAt_const.add h1
    exact continuousWithinAt_const.div h2 hden
  have hderiv : ∀ u ∈ Ioi (ρ ^ α),
      HasDerivAt (fun v : ℝ => -(1 / α) / (1 + v / (1 - t))) (Fstarp (u / (1 - t)) / (α * u)) u := by
    intro u hu
    have h0 : 0 < u := lt_of_le_of_lt hρa hu.out
    have hd : (1 : ℝ) + u / (1 - t) ≠ 0 := by
      have h : 0 < u / (1 - t) := div_pos h0 h1t
      positivity
    have hinner : HasDerivAt (fun v : ℝ => v / (1 - t)) (1 / (1 - t)) u :=
      (hasDerivAt_id' (𝕜 := ℝ) u).div_const (1 - t)
    have houter : HasDerivAt (fun y : ℝ => -(1 / α) / (1 + y))
        (-(-(1 / α)) / (1 + u / (1 - t)) ^ 2) (u / (1 - t)) :=
      hasDerivAt_div_add_const (-(1 / α)) 1 (u / (1 - t)) hd
    have hcomp := houter.comp u hinner
    have hfun : ((fun y : ℝ => -(1 / α) / (1 + y)) ∘ fun v : ℝ => v / (1 - t))
        = fun v : ℝ => -(1 / α) / (1 + v / (1 - t)) := rfl
    rw [hfun] at hcomp
    have hval : (-(-(1 / α)) / (1 + u / (1 - t)) ^ 2) * (1 / (1 - t))
        = Fstarp (u / (1 - t)) / (α * u) := by
      rw [Fstarp]
      have hu0 : u ≠ 0 := ne_of_gt h0
      have hαne : α ≠ 0 := hα.ne'
      first | (field_simp; ring) | field_simp | ring_nf
    rw [hval] at hcomp
    exact hcomp
  have hnonneg : ∀ u ∈ Ioi (ρ ^ α), 0 ≤ Fstarp (u / (1 - t)) / (α * u) := by
    intro u hu
    have h0 : 0 < u := lt_of_le_of_lt hρa hu.out
    have h1 : 0 ≤ u / (1 - t) := div_nonneg h0.le h1t.le
    rw [Fstarp]
    have h2 : 0 ≤ u / (1 - t) / (1 + u / (1 - t)) ^ 2 :=
      div_nonneg h1 (sq_nonneg _)
    have h3 : 0 < α * u := mul_pos hα h0
    exact div_nonneg h2 h3.le
  have htend : Tendsto (fun u : ℝ => -(1 / α) / (1 + u / (1 - t))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun u : ℝ => u / (1 - t)) atTop atTop := by
      have hpos : (0 : ℝ) < (1 - t)⁻¹ := inv_pos.mpr h1t
      simpa [div_eq_mul_inv] using tendsto_id.atTop_mul_const hpos
    have h2 : Tendsto (fun u : ℝ => (1 : ℝ) + u / (1 - t)) atTop atTop :=
      tendsto_atTop_add_const_left atTop (1 : ℝ) h1
    have h3 : Tendsto (fun u : ℝ => ((1 : ℝ) + u / (1 - t))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp h2
    have h4 := h3.const_mul (-(1 / α))
    simpa [div_eq_mul_inv] using h4
  have key := integral_Ioi_of_hasDerivAt_of_nonneg (a := ρ ^ α) (l := 0)
    (g := fun u : ℝ => -(1 / α) / (1 + u / (1 - t)))
    (g' := fun u : ℝ => Fstarp (u / (1 - t)) / (α * u)) hcont hderiv hnonneg htend
  rw [key]
  first | (field_simp; ring) | field_simp | ring_nf

/-! ## The evaluation of `L₁₂^K` on the self-similar family -/

theorem L12_selfSim {K Γ : ℝ → ℝ} {α : ℝ} {ρ t : ℝ}
    (hα : 0 < α) (hc : cK K Γ ≠ 0)
    (hΓ : IntegrableOn (fun θ => K θ * Γ θ) (Icc 0 (Real.pi / 2)))
    (hρ : 0 ≤ ρ) (ht : t < 1) :
    L12 K (fun s θ => selfSim K Γ α s θ t) ρ = 2 / (1 - t + ρ ^ α) := by
  rw [L12]
  have hpoint : ∀ s, L12dens K (fun s θ => selfSim K Γ α s θ t) s
      = (2 * α / (1 - t)) * (Fstarp (s ^ α / (1 - t)) / s) :=
    fun s => L12dens_selfSim hc hΓ (ne_of_lt ht)
  simp only [hpoint]
  rw [integral_const_mul, integral_Ioi_Fstarp_rpow hα hρ ht]
  have hD : 1 - t + ρ ^ α ≠ 0 := by
    have h : 0 < 1 - t := by linarith
    have h2 : 0 ≤ ρ ^ α := Real.rpow_nonneg hρ α
    positivity
  have h1tne : (1 : ℝ) - t ≠ 0 := by linarith
  first | (field_simp; ring) | field_simp | ring_nf

end Work.FM
