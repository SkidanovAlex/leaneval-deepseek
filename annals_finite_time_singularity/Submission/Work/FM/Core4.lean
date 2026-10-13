/-
# The fundamental model: the paper's theorem statements (self-similar family and explicit formula)
-/

import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Submission.Work.FM.Defs
import Submission.Work.FM.Core
import Submission.Work.FM.Core2
import Submission.Work.FM.Core3

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Work.FM

/-! ## The self-similar family solves the model, and blows up -/

/-- **Lemma `FMSelfSimilar`**: for `KΓ ∈ L¹` and `c = ∫KΓ ≠ 0`, the family
`f(ρ,θ,t) = 2α (Γ(θ)/c) (1-t)⁻¹ F_{*,rad}(ρ^α/(1-t))` solves the fundamental model. -/
theorem isModelSolution_selfSim {K Γ : ℝ → ℝ} {α : ℝ}
    (hα : 0 < α) (hc : cK K Γ ≠ 0)
    (hΓ : IntegrableOn (fun θ => K θ * Γ θ) (Icc 0 (Real.pi / 2))) :
    IsModelSolution K (selfSim K Γ α) :=
  isModelSolution_selfSim_of_L12 fun ρ hρ t ht => L12_selfSim hα hc hΓ hρ ht

/-- `L₁₂^K(f)(0)` for the self-similar family blows up as `t → 1⁻`. -/
theorem selfSim_blowup {K Γ : ℝ → ℝ} {α : ℝ}
    (hα : 0 < α) (hc : cK K Γ ≠ 0)
    (hΓ : IntegrableOn (fun θ => K θ * Γ θ) (Icc 0 (Real.pi / 2))) :
    Tendsto (fun t => L12 K (fun s θ => selfSim K Γ α s θ t) 0) (nhdsWithin 1 (Iio 1)) atTop := by
  refine selfSim_blowup_of_L12 fun t ht => ?_
  rw [L12_selfSim hα hc hΓ le_rfl ht, Real.zero_rpow hα.ne']
  norm_num

/-- The `t = 0` value of the tail integral of the self-similar family (the `V₀` of
the explicit formula). -/
theorem L12_selfSim_zero {K Γ : ℝ → ℝ} {α : ℝ} {ρ : ℝ}
    (hα : 0 < α) (hc : cK K Γ ≠ 0)
    (hΓ : IntegrableOn (fun θ => K θ * Γ θ) (Icc 0 (Real.pi / 2))) (hρ : 0 ≤ ρ) :
    L12 K (fun s θ => selfSim K Γ α s θ 0) ρ = 2 / (1 + ρ ^ α) := by
  have h := L12_selfSim (ρ := ρ) (t := 0) hα hc hΓ hρ (by norm_num)
  simpa using h

/-- The per-`ρ` Riccati equation `∂_t L₁₂^K(f)(ρ,t) = ½(L₁₂^K(f)(ρ,t))²` for the
self-similar family (paper line 463). -/
theorem hasDerivAt_L12_selfSim {K Γ : ℝ → ℝ} {α : ℝ} {ρ t : ℝ}
    (hα : 0 < α) (hc : cK K Γ ≠ 0)
    (hΓ : IntegrableOn (fun θ => K θ * Γ θ) (Icc 0 (Real.pi / 2)))
    (hρ : 0 ≤ ρ) (ht : t < 1) :
    HasDerivAt (fun s => L12 K (fun r θ => selfSim K Γ α r θ s) ρ)
      (L12 K (fun r θ => selfSim K Γ α r θ t) ρ ^ 2 / 2) t :=
  hasDerivAt_L12_selfSim_of_L12 hρ ht fun s hs => L12_selfSim hα hc hΓ hρ hs

/-- Paper line 461: the `ρ = 0` case of the Riccati equation, for the self-similar
family — the rate of blow-up `L₁₂^K(f)(0,t) = 2/(1-t)` with
`d/dt L₁₂^K(f)(0,t) = ½L₁₂^K(f)(0,t)²`. -/
theorem hasDerivAt_L12_selfSim_zero {K Γ : ℝ → ℝ} {α t : ℝ}
    (hα : 0 < α) (hc : cK K Γ ≠ 0)
    (hΓ : IntegrableOn (fun θ => K θ * Γ θ) (Icc 0 (Real.pi / 2))) (ht : t < 1) :
    HasDerivAt (fun s => L12 K (fun r θ => selfSim K Γ α r θ s) 0)
      ((L12 K (fun r θ => selfSim K Γ α r θ t) 0) ^ 2 / 2) t :=
  hasDerivAt_L12_selfSim hα hc hΓ le_rfl ht

/-- Consistency of the two picture of the self-similar solution: it is the explicit
solution associated with the initial datum `f₀ = selfSim · 0` and
`V₀ = L₁₂^K f₀ = 2/(1+ρ^α)`. -/
theorem selfSim_eq_explicit (K Γ : ℝ → ℝ) (α ρ θ t : ℝ) (hc : cK K Γ ≠ 0) (hρ : 0 ≤ ρ)
    (ht : t < 1) :
    selfSim K Γ α ρ θ t
      = 2 * α * (Γ θ / cK K Γ) * Fstarp (ρ ^ α)
          / (1 - t * (2 / (1 + ρ ^ α)) / 2) ^ 2 := by
  have h1 : (1 : ℝ) + ρ ^ α ≠ 0 := by
    have h2 : 0 ≤ ρ ^ α := Real.rpow_nonneg hρ α
    positivity
  have h3 : 1 - t + ρ ^ α ≠ 0 := by
    have h : 0 < 1 - t := by linarith
    have h2 : 0 ≤ ρ ^ α := Real.rpow_nonneg hρ α
    positivity
  have h3' : 1 + ρ ^ α - t ≠ 0 := by
    intro hc'
    exact h3 (by linarith)
  have hRHS : 2 * α * (Γ θ / cK K Γ) * Fstarp (ρ ^ α) / (1 - t * (2 / (1 + ρ ^ α)) / 2) ^ 2
      = 2 * α * (Γ θ / cK K Γ) * ρ ^ α / (1 - t + ρ ^ α) ^ 2 := by
    unfold Fstarp
    first | (field_simp; ring) | field_simp | ring_nf
  rw [selfSim_eq_inv hρ ht, hRHS]

/-! ## The explicit solution formula `f = f₀/(1 - ½t L₁₂^K f₀)²` -/

/-- `d/dt (c/(1 - t m/2)²) = c/(1 - t m/2)² · (m/(1 - t m/2))`: the `t`-derivative
of the explicit solution of `∂_t f = f L₁₂^K(f)`. -/
theorem hasDerivAt_explicit_inv_sq (c m t : ℝ) (h : 1 - t * m / 2 ≠ 0) :
    HasDerivAt (fun y : ℝ => c / (1 - y * m / 2) ^ 2)
      (c / (1 - t * m / 2) ^ 2 * (m / (1 - t * m / 2))) t := by
  have hlin : HasDerivAt (fun y : ℝ => 1 - y * m / 2) (-(m / 2)) t := by
    have h2 : HasDerivAt (fun y : ℝ => y * m / 2) (m / 2) t := by
      have h3 : HasDerivAt (fun y : ℝ => y * m) m t := by
        simpa using (hasDerivAt_id' (𝕜 := ℝ) t).mul_const m
      have h4 : HasDerivAt (fun y : ℝ => y * m / 2) (m / 2) t := h3.div_const 2
      convert h4 using 1 <;> (first | (funext y; ring) | ring_nf)
    have hc : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 t := hasDerivAt_const t 1
    have h4 := hc.sub h2
    convert h4 using 1 <;> (first | (funext y; simp) | ring_nf)
  have hsq : HasDerivAt (fun y : ℝ => (1 - y * m / 2) ^ 2) (-(m * (1 - t * m / 2))) t := by
    have h2 := hlin.pow 2
    convert h2 using 1 <;> (first | (funext y; simp) | ring_nf)
  have hinv : HasDerivAt (fun y : ℝ => ((1 - y * m / 2) ^ 2)⁻¹)
      (-(-(m * (1 - t * m / 2))) / ((1 - t * m / 2) ^ 2) ^ 2) t :=
    hsq.inv (pow_ne_zero 2 h)
  have hmul := hinv.const_mul c
  rw [show (fun y : ℝ => c / (1 - y * m / 2) ^ 2)
      = fun y => c * ((1 - y * m / 2) ^ 2)⁻¹ from by
    funext y; rw [div_eq_mul_inv]]
  have hval : c * (-(-(m * (1 - t * m / 2))) / ((1 - t * m / 2) ^ 2) ^ 2)
      = c / (1 - t * m / 2) ^ 2 * (m / (1 - t * m / 2)) := by
    first | (field_simp; ring) | field_simp | ring_nf
  rw [hval] at hmul
  exact hmul

/-- **The explicit solution formula** (paper line 463): if `V = L₁₂^K f₀` and `φ = 1 - ½tV`,
then `L₁₂^K(f₀/φ²)(ρ) = V(ρ)/φ(ρ)`. This is the self-consistency of the explicit
solution `f(ρ,θ,t) = f₀(ρ,θ)/(1-½t·L₁₂^K(f₀)(ρ))²`.

The hypothesis `hcontV` (right-continuity of `V` at `ρ`) is satisfied whenever
`L12dens K f₀ ∈ L¹((ρ,∞))`; for concrete data (e.g. the self-similar family) it is
a continuity check. -/
theorem L12_explicitSol {K : ℝ → ℝ} {f₀ : ℝ → ℝ → ℝ} {ρ t : ℝ}
    (hV : ∀ s ∈ Ioi ρ, HasDerivAt (fun σ => L12 K f₀ σ) (-(L12dens K f₀ s)) s)
    (hcontV : ContinuousWithinAt (fun σ => L12 K f₀ σ) (Ici ρ) ρ)
    (hint : IntegrableOn (fun s => L12dens K f₀ s / (1 - t * L12 K f₀ s / 2) ^ 2) (Ioi ρ))
    (hden : ∀ s ∈ Ioi ρ, 1 - t * L12 K f₀ s / 2 ≠ 0)
    (hdenρ : 1 - t * L12 K f₀ ρ / 2 ≠ 0)
    (htend : Tendsto (fun σ => L12 K f₀ σ) atTop (𝓝 0)) :
    L12 K (fun s θ => f₀ s θ / (1 - t * L12 K f₀ s / 2) ^ 2) ρ
      = L12 K f₀ ρ / (1 - t * L12 K f₀ ρ / 2) := by
  -- the density of the modified profile
  have hdens : ∀ s, L12dens K (fun s θ => f₀ s θ / (1 - t * L12 K f₀ s / 2) ^ 2) s
      = L12dens K f₀ s / (1 - t * L12 K f₀ s / 2) ^ 2 := by
    intro s
    rw [L12dens, L12dens]
    rw [show (fun θ => K θ * (f₀ s θ / (1 - t * L12 K f₀ s / 2) ^ 2) / s)
        = fun θ => ((1 - t * L12 K f₀ s / 2) ^ 2)⁻¹ * (K θ * f₀ s θ / s) from by
      funext θ; ring]
    rw [integral_const_mul]
    first | (rw [div_eq_mul_inv]; ring) | ring
  -- the derivative of `-Ψ`, where `Ψ = V/φ`
  have hderiv : ∀ s ∈ Ioi ρ, HasDerivAt (fun σ => -(L12 K f₀ σ / (1 - t * L12 K f₀ σ / 2)))
      (L12dens K f₀ s / (1 - t * L12 K f₀ s / 2) ^ 2) s := by
    intro s hs
    have hnum := hV s hs
    have hphi : HasDerivAt (fun σ : ℝ => 1 - t * L12 K f₀ σ / 2)
        (0 - t * (-(L12dens K f₀ s)) / 2) s := by
      have h2 : HasDerivAt (fun σ : ℝ => t * L12 K f₀ σ) (t * (-(L12dens K f₀ s))) s :=
        hnum.const_mul t
      have h3 : HasDerivAt (fun σ : ℝ => t * L12 K f₀ σ / 2) (t * (-(L12dens K f₀ s)) / 2) s :=
        h2.div_const 2
      have hc : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 s := hasDerivAt_const s 1
      have h4 := hc.sub h3
      convert h4 using 1 <;> (first | (funext σ; ring) | ring_nf)
    have hq := hnum.div hphi (hden s hs)
    have hneg := hq.neg
    convert hneg using 1 <;>
      (first | (funext σ; ring) | (field_simp; ring) | ring_nf)
  have hcont : ContinuousWithinAt (fun σ : ℝ => -(L12 K f₀ σ / (1 - t * L12 K f₀ σ / 2)))
      (Ici ρ) ρ := by
    have h1 : ContinuousWithinAt (fun σ : ℝ => 1 - t * L12 K f₀ σ / 2) (Ici ρ) ρ := by
      have h2 : ContinuousWithinAt (fun σ : ℝ => t * L12 K f₀ σ / 2) (Ici ρ) ρ :=
        (hcontV.const_mul t).div_const 2
      have h3 : ContinuousWithinAt (fun σ : ℝ => (1 : ℝ) - t * L12 K f₀ σ / 2) (Ici ρ) ρ :=
        continuousWithinAt_const.sub h2
      exact h3
    exact (hcontV.div h1 hdenρ).neg
  have htendΨ : Tendsto (fun σ : ℝ => -(L12 K f₀ σ / (1 - t * L12 K f₀ σ / 2)))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun σ : ℝ => 1 - t * L12 K f₀ σ / 2) atTop (𝓝 (1 - t * 0 / 2)) :=
      (tendsto_const_nhds.sub ((htend.const_mul t).div_const 2))
    have h2 : Tendsto (fun σ : ℝ => L12 K f₀ σ / (1 - t * L12 K f₀ σ / 2))
        atTop (𝓝 (0 / (1 - t * 0 / 2))) :=
      htend.div h1 (by norm_num)
    have h3 := h2.neg
    simpa using h3
  have key := integral_Ioi_of_hasDerivAt_of_tendsto
    (f := fun σ : ℝ => -(L12 K f₀ σ / (1 - t * L12 K f₀ σ / 2)))
    (f' := fun σ : ℝ => L12dens K f₀ σ / (1 - t * L12 K f₀ σ / 2) ^ 2)
    (a := ρ) (m := 0) hcont hderiv hint htendΨ
  rw [L12]
  simp only [hdens]
  rw [key]
  ring

/-- **The explicit solution of the fundamental model**: if `L₁₂^K(f₀/φ²) = V/φ`
(which is `L12_explicitSol`), then `f(ρ,θ,t) = f₀(ρ,θ)/φ(ρ,t)²` solves
`∂_t f = f·L₁₂^K(f)`. -/
theorem isModelSolution_explicitSol {K : ℝ → ℝ} {f₀ : ℝ → ℝ → ℝ}
    (hself : ∀ t ρ, 0 ≤ ρ → t < 1 →
      L12 K (fun s θ => f₀ s θ / (1 - t * L12 K f₀ s / 2) ^ 2) ρ
        = L12 K f₀ ρ / (1 - t * L12 K f₀ ρ / 2))
    (hden : ∀ ρ, 0 ≤ ρ → ∀ t, t < 1 → 1 - t * L12 K f₀ ρ / 2 ≠ 0) :
    IsModelSolution K (fun ρ θ t => f₀ ρ θ / (1 - t * L12 K f₀ ρ / 2) ^ 2) := by
  intro ρ θ t hρ ht
  rw [hself t ρ hρ ht]
  exact hasDerivAt_explicit_inv_sq (f₀ ρ θ) (L12 K f₀ ρ) t (hden ρ hρ t ht)

end Work.FM
