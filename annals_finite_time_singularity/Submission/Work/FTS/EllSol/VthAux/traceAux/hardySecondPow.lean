import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.EllSol.VthAux.traceAux.hardyPowAux
import Submission.Work.FTS.EllSol.VthAux.traceAux.hardyPowPrimIbpTwo
import Submission.Work.FTS.EllSol.VthAux.traceAux.integrableOn_Ioo_of_intervalIntegral_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.VthAux.traceAux

open MeasureTheory Set Filter
open scoped Real Topology ENNReal Interval


/-- **Weighted Hardy inequality for the second derivative (power weight).**

For `0 < a < 1`, `ε > 0` and `h : ℝ → ℝ` of class `C²` on `(0, ε)` with `h θ → 0` as `θ → 0⁺`
and `∫_0^ε θ^a |h''(θ)| dθ < ∞`, the singular integral `∫_0^ε θ^{a-2} |h(θ)| dθ` is finite
(equivalently: `(fun θ => θ^(a-2) * |h θ|)` is `IntegrableOn (Set.Ioo 0 ε)`).

*Proof route (all steps are `intervalIntegral`, no product-measure Fubini needed).*  Write
`ψ := fun θ => |deriv (deriv h) θ|`.  For a fixed interior point `θ₀ ∈ (0,ε)` one has
`|h'(θ)| ≤ |h'(θ₀)| + ∫ s in θ..θ₀, ψ s` for `θ < θ₀`, whence
`Δ := ∫_0^ε θ^{a-1}|h'| ≤ |h'(θ₀)|ε^a/a + (1/a)∫_0^ε s^a ψ s` (Tonelli: `∫_0^s θ^{a-1}dθ = s^a/a`),
plus a bounded piece on `[θ₀,ε]`.
Then `|h(δ)| ≤ ∫_0^δ|h'| ≤ δ^{1-a}Δ` (from `h0`), and with `G θ := ∫ s in δ..θ, |h'|`
(`G δ = 0`, `G' = |h'|`) one integration by parts gives
`∫_δ^ε θ^{a-2}|h| ≤ δ^{a-1}|h(δ)|/(1-a) + (1/(1-a))∫_δ^ε θ^{a-1}|h'| ≤ 2Δ/(1-a)`,
uniformly in `δ`; let `δ ↓ 0` by monotone convergence for the nonnegative integrand.
(Equivalently, the multiplicative-average representation
`θ^{a-2} h(θ) = ∫_0^1 (1-t)t^{-a}(θt)^a h''(θt) dt` with the `L¹` kernel `(1-t)t^{-a}` gives the
same estimate.)-/
theorem hardySecondPow {a ε : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hε : 0 < ε) {h : ℝ → ℝ}
    (hC2 : ContDiffOn ℝ 2 h (Set.Ioo 0 ε))
    (h0 : Filter.Tendsto h (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => θ ^ a * |deriv (deriv h) θ|) (Set.Ioo 0 ε)) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => θ ^ (a - 2) * |h θ|) (Set.Ioo 0 ε) := by
  obtain ⟨_hIntW_Ioc, habsIntIoo, hh_le, hWmono⟩ := hardySecondPowStep1 ha0 ha1 hε hC2 h0 hint
  have ha1a : (0 : ℝ) < 1 - a := by linarith
  have hC1 : ContDiffOn ℝ 1 h (Set.Ioo 0 ε) := (contDiffOn_iff_forall_nat_le.mp hC2) 1 (by norm_num)
  have hφc : ContDiffOn ℝ 1 (deriv h) (Set.Ioo 0 ε) := hC2.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hhc : ContinuousOn h (Set.Ioo 0 ε) := hC1.continuousOn
  have hφ_cont : ContinuousOn (deriv h) (Set.Ioo 0 ε) := hφc.continuousOn
  have hφd : ∀ x ∈ Set.Ioo 0 ε, HasDerivAt h (deriv h x) x := fun x hx =>
    (hC1.differentiableOn (by norm_num)).hasDerivAt (isOpen_Ioo.mem_nhds hx)
  set Δ : ℝ := ∫ x in Set.Ioc 0 ε, x ^ (a - 1) * |deriv h x| with hΔ
  have hhδ_le : ∀ {δ : ℝ}, 0 < δ → δ < ε → |h δ| ≤ δ ^ (1 - a) * Δ := by
    intro δ hδ0 hδ1
    rw [hΔ]
    exact hh_le δ ⟨hδ0, hδ1⟩
  have hStepB : ∀ δ ∈ Set.Ioo 0 ε,
      (∫ θ in δ..ε, θ ^ (a - 2) * |h θ|) ≤ 2 * Δ / (1 - a) := by
    intro δ hδ
    have hδ0 : 0 < δ := hδ.1
    have hδε : δ ≤ ε := hδ.2.le
    set H : ℝ → ℝ := fun θ => ∫ s in δ..θ, |deriv h s| with hHdef
    have hII : IntervalIntegrable (fun s : ℝ => |deriv h s|) volume δ ε := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hδε, integrableOn_Ioc_iff_integrableOn_Ioo]
      exact habsIntIoo.mono_set (fun y hy => ⟨lt_trans hδ0 hy.1, hy.2⟩)
    have hHder : ∀ x ∈ Set.Ioo δ ε, HasDerivAt H (|deriv h x|) x := by
      intro x hx
      have hIIx : IntervalIntegrable (fun s : ℝ => |deriv h s|) volume δ x := by
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx.1.le, integrableOn_Ioc_iff_integrableOn_Ioo]
        exact habsIntIoo.mono_set (fun y hy => ⟨lt_trans hδ0 hy.1, lt_trans hy.2 hx.2⟩)
      have hnhds : Set.Ioo 0 ε ∈ 𝓝 x :=
        mem_of_superset (isOpen_Ioo.mem_nhds hx) (fun y hy => ⟨lt_trans hδ0 hy.1, hy.2⟩)
      refine intervalIntegral.integral_hasDerivAt_right hIIx ?_ ?_
      · exact ⟨Set.Ioo 0 ε, hnhds, hφ_cont.abs.aestronglyMeasurable measurableSet_Ioo⟩
      · exact hφ_cont.abs.continuousAt hnhds
    have hHc : ContinuousOn H (Set.Icc δ ε) := by
      have hpc := intervalIntegral.continuousOn_primitive_interval' hII (a := δ)
        (by rw [Set.uIcc_of_le hδε]; exact ⟨le_rfl, hδε⟩)
      rwa [Set.uIcc_of_le hδε] at hpc
    have hHδ : H δ = 0 := intervalIntegral.integral_same
    have hHε : 0 ≤ H ε := intervalIntegral.integral_nonneg hδε (fun u _ => abs_nonneg _)
    have hibp := hardyPowPrimIbpTwo ha0 ha1 hδ0 hδε hHc hHder hII
      (fun x _ => abs_nonneg _) hHδ hHε
    have hHmono : ∀ x ∈ Set.Ioo δ ε, H x ≤ H ε := by
      intro x hx
      have hIIx : IntervalIntegrable (fun s : ℝ => |deriv h s|) volume δ x := by
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx.1.le, integrableOn_Ioc_iff_integrableOn_Ioo]
        exact habsIntIoo.mono_set (fun y hy => ⟨lt_trans hδ0 hy.1, lt_trans hy.2 hx.2⟩)
      have hIIy : IntervalIntegrable (fun s : ℝ => |deriv h s|) volume x ε := by
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx.2.le, integrableOn_Ioc_iff_integrableOn_Ioo]
        exact habsIntIoo.mono_set (fun y hy => ⟨lt_trans (lt_trans hδ0 hx.1) hy.1, hy.2⟩)
      have hsp := intervalIntegral.integral_add_adjacent_intervals hIIx hIIy
      have hnn : 0 ≤ ∫ s in x..ε, |deriv h s| :=
        intervalIntegral.integral_nonneg hx.2.le (fun u _ => abs_nonneg _)
      linarith
    have habsH : ∀ θ ∈ Set.Ioo δ ε, |h θ| ≤ |h δ| + H θ := by
      intro θ hθ
      have hsub2 : Set.uIcc δ θ ⊆ Set.Ioo 0 ε := fun x hx => by
        rw [Set.uIcc_of_le hθ.1.le] at hx
        exact ⟨lt_of_lt_of_le hδ0 hx.1, lt_of_le_of_lt hx.2 hθ.2⟩
      have hd : ∀ x ∈ Set.uIcc δ θ, HasDerivAt h (deriv h x) x := fun x hx => hφd x (hsub2 hx)
      have hi : IntervalIntegrable (deriv h) volume δ θ := (hφ_cont.mono hsub2).intervalIntegrable
      have hFTC : ∫ s in δ..θ, deriv h s = h θ - h δ :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
      have h1 : |h θ - h δ| ≤ H θ := by
        rw [← hFTC, hHdef]
        exact intervalIntegral.abs_integral_le_integral_abs hθ.1.le
      have h2 : |h θ| ≤ |h δ| + |h θ - h δ| := by
        have h3 := abs_add_le (h θ - h δ) (h δ)
        rw [sub_add_cancel] at h3
        linarith
      linarith
    have hI1 : IntervalIntegrable (fun θ : ℝ => θ ^ (a - 2) * |h θ|) volume δ ε :=
      hardyPow_intervalIntegrable_rpow_mul (p := a - 2) (by linarith) hδ0 hδε
        ((hhc.mono (fun x hx => ⟨lt_trans hδ0 hx.1, hx.2⟩)).abs)
        (fun x hx => by rw [abs_abs]; linarith [habsH x hx, hHmono x hx])
        (add_nonneg (abs_nonneg _) hHε)
    have hI2 : IntervalIntegrable (fun θ : ℝ => θ ^ (a - 2) * (|h δ| + H θ)) volume δ ε :=
      hardyPow_intervalIntegrable_rpow_mul (p := a - 2) (by linarith) hδ0 hδε
        (continuousOn_const.add (hHc.mono Set.Ioo_subset_Icc_self))
        (fun x hx => by
          rw [abs_of_nonneg (add_nonneg (abs_nonneg _)
            (intervalIntegral.integral_nonneg hx.1.le (fun u _ => abs_nonneg _)))]
          linarith [hHmono x hx])
        (add_nonneg (abs_nonneg _) hHε)
    have hstep := intervalIntegral.integral_mono_on_of_le_Ioo hδε hI1 hI2 (fun θ hθ => by
      have h1 : |h θ| ≤ |h δ| + H θ := habsH θ hθ
      exact mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (le_of_lt (lt_trans hδ0 hθ.1)) _))
    have hI2a : IntervalIntegrable (fun θ : ℝ => θ ^ (a - 2) * |h δ|) volume δ ε :=
      hardyPow_intervalIntegrable_rpow_mul (p := a - 2) (by linarith) hδ0 hδε
        continuousOn_const (fun x hx => by rw [abs_of_nonneg (abs_nonneg (h δ))])
        (abs_nonneg _)
    have hI2b : IntervalIntegrable (fun θ : ℝ => θ ^ (a - 2) * H θ) volume δ ε :=
      hardyPow_intervalIntegrable_rpow_mul (p := a - 2) (by linarith) hδ0 hδε
        (hHc.mono Set.Ioo_subset_Icc_self)
        (fun x hx => by
          rw [abs_of_nonneg (intervalIntegral.integral_nonneg hx.1.le (fun u _ => abs_nonneg _))]
          exact hHmono x hx)
        hHε
    have hsplit : ∫ θ in δ..ε, θ ^ (a - 2) * (|h δ| + H θ)
        = |h δ| * ((ε ^ (a - 1) - δ ^ (a - 1)) / (a - 1))
          + ∫ θ in δ..ε, θ ^ (a - 2) * H θ := by
      have hfun : (fun θ : ℝ => θ ^ (a - 2) * (|h δ| + H θ))
          = fun θ : ℝ => θ ^ (a - 2) * |h δ| + θ ^ (a - 2) * H θ := by
        funext θ; ring
      rw [hfun]
      rw [intervalIntegral.integral_add hI2a hI2b]
      rw [intervalIntegral.integral_mul_const]
      have h0mem : (0 : ℝ) ∉ [[δ, ε]] := by
        rw [Set.uIcc_of_le hδε]
        exact fun hcon => absurd hcon.1 (not_le.mpr hδ0)
      have hane : a - 2 ≠ -1 := by linarith
      rw [integral_rpow (Or.inr ⟨hane, h0mem⟩)]
      rw [show a - 2 + 1 = a - 1 by ring]
      ring
    have hconv : (ε ^ (a - 1) - δ ^ (a - 1)) / (a - 1)
        = (δ ^ (a - 1) - ε ^ (a - 1)) / (1 - a) := by
      have h1 : a - 1 ≠ 0 := by linarith
      have h2 : (1 : ℝ) - a ≠ 0 := ne_of_gt ha1a
      field_simp
      ring
    have hbd1 : |h δ| * ((ε ^ (a - 1) - δ ^ (a - 1)) / (a - 1)) ≤ Δ / (1 - a) := by
      rw [hconv]
      have h2 : δ ^ (a - 1) - ε ^ (a - 1) ≤ δ ^ (a - 1) := by
        linarith [Real.rpow_nonneg hε.le (a - 1)]
      have h3 : |h δ| * (δ ^ (a - 1) - ε ^ (a - 1)) ≤ |h δ| * δ ^ (a - 1) :=
        mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      have h4 : |h δ| * δ ^ (a - 1) ≤ Δ := by
        have h5 := hhδ_le hδ0 hδ.2
        have h6 : δ ^ (a - 1) * (δ ^ (1 - a) * Δ) = Δ := by
          rw [← mul_assoc, ← Real.rpow_add hδ0, show a - 1 + (1 - a) = 0 by ring,
            Real.rpow_zero, one_mul]
        calc |h δ| * δ ^ (a - 1) ≤ (δ ^ (1 - a) * Δ) * δ ^ (a - 1) :=
              mul_le_mul_of_nonneg_right h5 (Real.rpow_nonneg hδ0.le _)
          _ = Δ := by rw [mul_comm]; exact h6
      have h7 : |h δ| * (δ ^ (a - 1) - ε ^ (a - 1)) / (1 - a) ≤ Δ / (1 - a) :=
        div_le_div_of_nonneg_right (le_trans h3 h4) ha1a.le
      simpa only [mul_div_assoc] using h7
    have hbd2 : ∫ θ in δ..ε, θ ^ (a - 1) * |deriv h θ| ≤ Δ := by
      rw [hΔ]
      exact hWmono δ hδ
    have hbd3 : ∫ θ in δ..ε, θ ^ (a - 2) * H θ ≤ (1 / (1 - a)) * Δ := by
      refine le_trans hibp (mul_le_mul_of_nonneg_left hbd2 ?_)
      positivity
    calc ∫ θ in δ..ε, θ ^ (a - 2) * |h θ|
        ≤ ∫ θ in δ..ε, θ ^ (a - 2) * (|h δ| + H θ) := hstep
      _ = |h δ| * ((ε ^ (a - 1) - δ ^ (a - 1)) / (a - 1))
            + ∫ θ in δ..ε, θ ^ (a - 2) * H θ := hsplit
      _ ≤ Δ / (1 - a) + (1 / (1 - a)) * Δ := add_le_add hbd1 hbd3
      _ = 2 * Δ / (1 - a) := by ring
  refine integrableOn_Ioo_of_intervalIntegral_le hε (fun x hx => ?_) (fun δ hδ => ?_) (fun δ hδ => hStepB δ hδ)
  · exact mul_nonneg (Real.rpow_nonneg hx.1.le _) (abs_nonneg _)
  · have hδ0 : 0 < δ := hδ.1
    have hδε : δ ≤ ε := hδ.2.le
    have hfix : ∀ θ ∈ Set.Ioo δ ε, |h θ| ≤ |h δ| + ∫ s in δ..ε, |deriv h s| := by
      intro θ hθ
      have hsub3 : Set.uIcc δ θ ⊆ Set.Ioo 0 ε := fun x hx => by
        rw [Set.uIcc_of_le hθ.1.le] at hx
        exact ⟨lt_of_lt_of_le hδ0 hx.1, lt_of_le_of_lt hx.2 hθ.2⟩
      have hd3 : ∀ x ∈ Set.uIcc δ θ, HasDerivAt h (deriv h x) x := fun x hx => hφd x (hsub3 hx)
      have hII3 : IntervalIntegrable (fun s : ℝ => |deriv h s|) volume δ θ := by
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hθ.1.le, integrableOn_Ioc_iff_integrableOn_Ioo]
        exact habsIntIoo.mono_set (fun y hy => ⟨lt_trans hδ0 hy.1, lt_trans hy.2 hθ.2⟩)
      have hII4 : IntervalIntegrable (fun s : ℝ => |deriv h s|) volume θ ε := by
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hθ.2.le, integrableOn_Ioc_iff_integrableOn_Ioo]
        exact habsIntIoo.mono_set (fun y hy => ⟨lt_trans (lt_trans hδ0 hθ.1) hy.1, hy.2⟩)
      have hFTC3 : ∫ s in δ..θ, deriv h s = h θ - h δ :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt hd3 ((hφ_cont.mono hsub3).intervalIntegrable)
      have h4 : |h θ - h δ| ≤ ∫ s in δ..θ, |deriv h s| := by
        rw [← hFTC3]; exact intervalIntegral.abs_integral_le_integral_abs hθ.1.le
      have h5 : ∫ s in δ..θ, |deriv h s| ≤ ∫ s in δ..ε, |deriv h s| := by
        have hsp := intervalIntegral.integral_add_adjacent_intervals hII3 hII4
        have hnn : 0 ≤ ∫ s in θ..ε, |deriv h s| :=
          intervalIntegral.integral_nonneg hθ.2.le (fun u _ => abs_nonneg _)
        linarith
      have h6 : |h θ| ≤ |h δ| + |h θ - h δ| := by
        have h7 := abs_add_le (h θ - h δ) (h δ)
        rw [sub_add_cancel] at h7
        linarith
      linarith
    exact hardyPow_intervalIntegrable_rpow_mul (p := a - 2) (by linarith) hδ0 hδε
      ((hhc.mono (fun x hx => ⟨lt_trans hδ0 hx.1, hx.2⟩)).abs)
      (fun x hx => by rw [abs_abs]; exact hfix x hx)
      (add_nonneg (abs_nonneg _)
        (intervalIntegral.integral_nonneg hδε (fun u _ => abs_nonneg _)))

end Work.FTS.EllSol.VthAux.traceAux
