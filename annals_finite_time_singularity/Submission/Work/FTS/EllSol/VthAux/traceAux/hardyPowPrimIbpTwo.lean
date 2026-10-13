import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.EllSol.VthAux.traceAux

/-- **Weighted Hardy inequality, power weight, primitive in integration-by-parts form.**

Let `0 < a < 1`, `0 < δ ≤ ε`, `H : ℝ → ℝ` continuous on `[δ, ε]` with `H δ = 0`, `H ε ≥ 0` and
derivative `v` on `(δ, ε)`, where `v` is interval integrable and (not actually needed for the
inequality) nonnegative.  Then
`∫_δ^ε θ^{a-2} H(θ) dθ ≤ (1/(1-a)) ∫_δ^ε θ^{a-1} v(θ) dθ`.

Proof: `F(θ) := θ^{a-1} H(θ)` has derivative `(a-1)θ^{a-2}H(θ) + θ^{a-1}v(θ)` on `(δ,ε)`, so the
fundamental theorem of calculus gives
`(a-1) I₁ + I₂ = ε^{a-1}H(ε) - δ^{a-1}H(δ) = ε^{a-1}H(ε) ≥ 0`, hence
`(1-a) I₁ = I₂ - ε^{a-1}H(ε) ≤ I₂`, i.e. `I₁ ≤ I₂/(1-a)`. -/
theorem hardyPowPrimIbpTwo {a δ ε : ℝ} {H v : ℝ → ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hδ : 0 < δ)
    (hδε : δ ≤ ε) (hHc : ContinuousOn H (Set.Icc δ ε))
    (hder : ∀ x ∈ Set.Ioo δ ε, HasDerivAt H (v x) x)
    (hvI : IntervalIntegrable v volume δ ε) (hvnn : ∀ x ∈ Set.Ioo δ ε, 0 ≤ v x)
    (hHδ : H δ = 0) (hHε : 0 ≤ H ε) :
    ∫ θ in δ..ε, θ ^ (a - 2) * H θ ≤ (1 / (1 - a)) * ∫ θ in δ..ε, θ ^ (a - 1) * v θ := by
  have hεpos : 0 < ε := lt_of_lt_of_le hδ hδε
  have h1a : 0 < 1 - a := by linarith
  -- continuity of the two power weights on `[δ, ε]`
  have hpow1 : ContinuousOn (fun θ : ℝ => θ ^ (a - 2)) (Set.Icc δ ε) :=
    continuousOn_id.rpow_const fun θ hθ => Or.inl (ne_of_gt (lt_of_lt_of_le hδ hθ.1))
  have hpow2 : ContinuousOn (fun θ : ℝ => θ ^ (a - 1)) (Set.Icc δ ε) :=
    continuousOn_id.rpow_const fun θ hθ => Or.inl (ne_of_gt (lt_of_lt_of_le hδ hθ.1))
  have hpow2' : ContinuousOn (fun θ : ℝ => θ ^ (a - 1)) (Set.uIcc δ ε) := by
    rwa [Set.uIcc_of_le hδε]
  -- integrability of the two pieces of the derivative
  have hint1 : IntervalIntegrable (fun θ : ℝ => θ ^ (a - 2) * H θ) volume δ ε :=
    (hpow1.mul hHc).intervalIntegrable_of_Icc hδε
  have hint2 : IntervalIntegrable (fun θ : ℝ => θ ^ (a - 1) * v θ) volume δ ε :=
    hvI.continuousOn_mul hpow2'
  -- the derivative of the primitive `θ ↦ θ^(a-1) * H θ`
  have hFder : ∀ x ∈ Set.Ioo δ ε,
      HasDerivAt (fun θ : ℝ => θ ^ (a - 1) * H θ)
        ((a - 1) * (x ^ (a - 2) * H x) + x ^ (a - 1) * v x) x := by
    intro x hx
    have hxpos : 0 < x := lt_trans hδ hx.1
    have hpd : HasDerivAt (fun θ : ℝ => θ ^ (a - 1)) ((a - 1) * x ^ (a - 2)) x := by
      have h0 := Real.hasDerivAt_rpow_const (p := a - 1) (x := x) (Or.inl (ne_of_gt hxpos))
      rwa [show (a - 1) - 1 = a - 2 from by ring] at h0
    have hm : HasDerivAt (fun θ : ℝ => θ ^ (a - 1) * H θ)
        (((a - 1) * x ^ (a - 2)) * H x + x ^ (a - 1) * v x) x := hpd.mul (hder x hx)
    simpa only [mul_assoc] using hm
  have hFcont : ContinuousOn (fun θ : ℝ => θ ^ (a - 1) * H θ) (Set.Icc δ ε) := hpow2.mul hHc
  have hintsum : IntervalIntegrable
      (fun θ : ℝ => (a - 1) * (θ ^ (a - 2) * H θ) + θ ^ (a - 1) * v θ) volume δ ε := by
    have h := (hint1.const_mul (a - 1)).add hint2
    simpa only [Pi.add_apply] using h
  -- fundamental theorem of calculus
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hδε hFcont hFder hintsum
  simp only [hHδ, mul_zero, sub_zero] at hFTC
  -- split the integral of the sum
  have hsplit : ∫ θ in δ..ε, ((a - 1) * (θ ^ (a - 2) * H θ) + θ ^ (a - 1) * v θ)
      = (a - 1) * (∫ θ in δ..ε, θ ^ (a - 2) * H θ) + ∫ θ in δ..ε, θ ^ (a - 1) * v θ := by
    rw [intervalIntegral.integral_add (hint1.const_mul (a - 1)) hint2,
      intervalIntegral.integral_const_mul]
  have hAB : (a - 1) * (∫ θ in δ..ε, θ ^ (a - 2) * H θ) + ∫ θ in δ..ε, θ ^ (a - 1) * v θ
      = ε ^ (a - 1) * H ε := by
    rw [← hsplit]
    exact hFTC
  -- final arithmetic
  have hc : 0 ≤ ε ^ (a - 1) * H ε := mul_nonneg (Real.rpow_nonneg hεpos.le _) hHε
  have hkey : (1 - a) * (∫ θ in δ..ε, θ ^ (a - 2) * H θ)
      = (∫ θ in δ..ε, θ ^ (a - 1) * v θ) - ε ^ (a - 1) * H ε := by
    have h1 : (a - 1) * (∫ θ in δ..ε, θ ^ (a - 2) * H θ)
        = ε ^ (a - 1) * H ε - ∫ θ in δ..ε, θ ^ (a - 1) * v θ :=
      eq_sub_iff_add_eq.mpr hAB
    rw [show (1 : ℝ) - a = - (a - 1) from by ring, neg_mul, h1]
    ring
  rw [one_div_mul_eq_div, le_div_iff₀ h1a,
    mul_comm (∫ θ in δ..ε, θ ^ (a - 2) * H θ) (1 - a), hkey]
  exact sub_le_self _ hc

end Work.FTS.EllSol.VthAux.traceAux
