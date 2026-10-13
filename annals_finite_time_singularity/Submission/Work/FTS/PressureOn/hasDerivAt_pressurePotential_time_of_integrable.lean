/-
# The time-derivative of the pressure potential: the corrected statement

`Work.FTS.PressureOn.hasDerivAt_pressurePotential_time` (the requested lemma) is **false** as it
stands: its hypotheses constrain `f` only *relative to the value at `t`* (`hlip` bounds
`‖f y s - f y t‖`), together with the support condition `hsupp`, and these do **not** force the
spatial slices `f · s` to be integrable against the singular kernel `∇Nfund (x - ·)`.  With a
non-integrable slice the Bochner integral `∫ y, ⟪∇Nfund (x - y), f y s⟫` is `0` *by convention*
(`MeasureTheory.integral_undef`), so the left-hand side of the asserted `HasDerivAt` degenerates
to the constant `0`, while the asserted derivative is a genuine, generally non-zero integral of
the time derivative.  A concrete counterexample is recorded in
`Submission/Work/FTS/PressureOn/refute_hasDerivAt_pressurePotential_time.lean`.

The present file proves the corrected statement: the *same* conclusion holds as soon as the
slices are integrable against the kernel -- the missing hypothesis

  `hInt : ∀ s ∈ Ioo (t - 1) (t + 1), Integrable (fun y => ⟪∇Nfund (x - y), f y s⟫)`,

which is exactly what the dominated-convergence argument needs (and which is automatic, e.g., if
`f` is jointly continuous with `y`-support in a fixed ball; see
`hasDerivAt_pressurePotential_time_of_continuous`).

The proof differentiates under the integral sign: the difference quotients
`(s - t)⁻¹ • (F s - F t)` are dominated by the integrable weight
`C ‖∇Nfund (x - ·)‖` on the support ball, and converge pointwise to
`⟪∇Nfund (x - ·), ∂ₜf(·,t)⟫`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Submission.Work.FTS.PressureOn.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set MeasureTheory Metric Filter
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn

/-! ## The kernel `∇Nfund` -/

/-- The pointwise size of the kernel: `‖∇Nfund z‖ = (4π)⁻¹‖z‖⁻²`. -/
theorem norm_nablaNfund (z : R3) : ‖nablaNfund z‖ = (4 * Real.pi)⁻¹ * ‖z‖ ^ (-2 : ℝ) := by
  rw [nablaNfund_eq_neg_newtonGrad, norm_neg, norm_newtonGrad]
  rcases eq_or_lt_of_le (norm_nonneg z) with h | h
  · simp [← h]
  · rw [Real.rpow_neg (norm_nonneg z) (2 : ℝ), Real.rpow_two]
    field_simp

/-- **`‖x - ·‖ ^ (-2)` is integrable on every ball of `ℝ³`** (the kernel is locally integrable in
dimension three; we shift so that the singularity sits at the centre of a ball, and use
`integrableOn_ball_of_norm_le_rpow`). -/
theorem integrableOn_norm_sub_sq_inv_ball (x : R3) (R : ℝ) :
    IntegrableOn (fun y : R3 => ‖x - y‖ ^ (-2 : ℝ)) (ball 0 R) := by
  have hdim : Module.finrank ℝ R3 = 3 := by simp [R3]
  have h1 : IntegrableOn (fun z : R3 => ‖z‖ ^ (-2 : ℝ)) (ball 0 (‖x‖ + R)) := by
    refine integrableOn_ball_of_norm_le_rpow (μ := volume) (F := ℝ) (C := 1) (α := 2)
      (r := ‖x‖ + R) (by rw [hdim]; norm_num) (by rw [hdim]; norm_num) ?_ ?_
    · filter_upwards with z
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _), one_mul]
    · have hfun : (fun z : R3 => ‖z‖ ^ (-2 : ℝ)) = fun z => (‖z‖ ^ (2 : ℕ))⁻¹ := by
        funext z
        rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg (norm_nonneg z), Real.rpow_two]
      rw [hfun]
      exact ((continuous_norm.pow 2).measurable.inv).aemeasurable.aestronglyMeasurable
  have h2 : IntegrableOn (fun z : R3 => ‖z‖ ^ (-2 : ℝ)) (ball (-x) R) := by
    refine h1.mono_set (fun z hz => ?_)
    have hz' : ‖z + x‖ < R := by
      rw [mem_ball, dist_eq_norm, sub_neg_eq_add] at hz
      exact hz
    have hlt : ‖z‖ < ‖x‖ + R :=
      calc ‖z‖ = ‖z + x - x‖ := by rw [add_sub_cancel_right]
        _ ≤ ‖z + x‖ + ‖x‖ := norm_sub_le _ _
        _ < R + ‖x‖ := by linarith
        _ = ‖x‖ + R := by ring
    simpa only [mem_ball, dist_zero_right, sub_zero] using hlt
  have hmp : MeasurePreserving (fun z : R3 => z + (-x)) volume volume :=
    measurePreserving_add_right volume (-x)
  have hmb : MeasurableEmbedding (fun z : R3 => z + (-x)) :=
    (Homeomorph.addRight (-x)).measurableEmbedding
  have hpre : (fun z : R3 => z + (-x)) ⁻¹' ball (-x) R = ball 0 R := by
    ext z
    rw [mem_preimage, mem_ball, mem_ball, dist_eq_norm, dist_eq_norm,
      show z + -x - -x = z by abel, sub_zero]
  have hcomp : ((fun z : R3 => ‖z‖ ^ (-2 : ℝ)) ∘ fun z => z + (-x))
      = fun y : R3 => ‖x - y‖ ^ (-2 : ℝ) := by
    funext y
    have h : y + (-x) = -(x - y) := by abel
    rw [Function.comp_apply, h, norm_neg]
  have := (hmp.integrableOn_comp_preimage hmb (f := fun z : R3 => ‖z‖ ^ (-2 : ℝ))
    (s := ball (-x) R)).mpr h2
  rwa [hpre, hcomp] at this

/-- The dominating weight of the differentiation under the integral sign:
`C ‖∇Nfund (x - y)‖` on the closed ball of radius `R`, zero outside.  It is integrable because
`‖∇Nfund (x - ·)‖ ≲ ‖x - ·‖⁻²` is locally integrable in dimension three and the support is
bounded. -/
theorem integrable_indicator_kernelWeight (x : R3) {R C : ℝ} :
    Integrable ((closedBall (0 : R3) R).indicator (fun y => C * ‖nablaNfund (x - y)‖)) := by
  rw [integrable_indicator_iff measurableSet_closedBall]
  have hker : IntegrableOn (fun y : R3 => C * ‖nablaNfund (x - y)‖) (ball 0 (R + 1)) := by
    have h : IntegrableOn (fun y : R3 => (C * (4 * Real.pi)⁻¹) * ‖x - y‖ ^ (-2 : ℝ))
        (ball 0 (R + 1)) := (integrableOn_norm_sub_sq_inv_ball x (R + 1)).const_mul _
    refine IntegrableOn.congr_fun h (fun y _ => ?_) measurableSet_ball
    rw [norm_nablaNfund]
    ring
  refine hker.mono_set (fun y hy => ?_)
  have hy' : ‖y‖ ≤ R := by
    rw [mem_closedBall, dist_eq_norm, sub_zero] at hy
    exact hy
  simpa only [mem_ball, dist_zero_right, sub_zero] using (by linarith : ‖y‖ < R + 1)

/-! ## The corrected differentiation under the integral sign -/

theorem hasDerivAt_pressurePotential_time_of_integrable {f : R3 → ℝ → R3} {x : R3} {t : ℝ}
    (hsupp : ∃ R, ∀ s ∈ Set.Ioo (t - 1) (t + 1), ∀ y, f y s ≠ 0 → ‖y‖ ≤ R)
    (hlip : ∃ C, ∀ y, ∀ s ∈ Set.Ioo (t - 1) (t + 1), ‖f y s - f y t‖ ≤ C * |s - t|)
    (hderiv : ∀ y, HasDerivAt (f y) (FiniteTimeSingularity.timeDeriv f y t) t)
    (hInt : ∀ s ∈ Set.Ioo (t - 1) (t + 1),
      Integrable (fun y => inner ℝ (nablaNfund (x - y)) (f y s))) :
    HasDerivAt (fun s => pressurePotential (f · s) x)
      (-∫ y, inner ℝ (nablaNfund (x - y)) (FiniteTimeSingularity.timeDeriv f y t)) t := by
  obtain ⟨R, hR⟩ := hsupp
  obtain ⟨C, hC⟩ := hlip
  -- the neighbourhood of `t` on which all the hypotheses are available
  have htS : t ∈ Set.Ioo (t - 1) (t + 1) := ⟨by linarith, by linarith⟩
  have hSnhds : Set.Ioo (t - 1) (t + 1) ∈ 𝓝 t := isOpen_Ioo.mem_nhds htS
  -- the Lipschitz constant is non-negative (test it at `s = t + 1/2`)
  have hCnn : 0 ≤ C := by
    have hhalf : t + 1 / 2 ∈ Set.Ioo (t - 1) (t + 1) := ⟨by linarith, by linarith⟩
    have h := hC (0 : R3) (t + 1 / 2) hhalf
    have h2 : |t + 1 / 2 - t| = 1 / 2 := by rw [add_sub_cancel_left, abs_of_pos]; norm_num
    rw [h2] at h
    linarith [norm_nonneg (f 0 (t + 1 / 2) - f 0 t)]
  -- the intermediate objects
  set F : ℝ → R3 → ℝ := fun s y => inner ℝ (nablaNfund (x - y)) (f y s) with hF
  set F' : R3 → ℝ := fun y => inner ℝ (nablaNfund (x - y)) (timeDeriv f y t) with hF'
  set G : ℝ → R3 → ℝ := fun s y => (s - t)⁻¹ • (F s y - F t y) with hG
  set bound : R3 → ℝ :=
    (closedBall (0 : R3) R).indicator (fun y => C * ‖nablaNfund (x - y)‖) with hbound
  have hbound_int : Integrable bound volume := integrable_indicator_kernelWeight x
  -- ## measurability of the difference quotients
  have hG_meas : ∀ᶠ s in 𝓝[≠] t, AEStronglyMeasurable (G s) volume := by
    filter_upwards [nhdsWithin_le_nhds hSnhds] with s hsS
    have h1 : Integrable (F s) volume := hInt s hsS
    have h2 : Integrable (F t) volume := hInt t htS
    exact ((h1.aestronglyMeasurable.sub h2.aestronglyMeasurable).const_smul (s - t)⁻¹)
  -- ## the dominating bound
  have hG_bound : ∀ᶠ s in 𝓝[≠] t, ∀ᵐ y ∂volume, ‖G s y‖ ≤ bound y := by
    filter_upwards [nhdsWithin_le_nhds hSnhds] with s hsS
    refine ae_of_all _ (fun y => ?_)
    by_cases hy : ‖y‖ ≤ R
    · have hyc : y ∈ closedBall (0 : R3) R := by
        rw [mem_closedBall, dist_eq_norm, sub_zero]
        exact hy
      have hby : bound y = C * ‖nablaNfund (x - y)‖ := by
        simp only [hbound, Set.indicator_of_mem hyc]
      rw [hby]
      by_cases hst : s = t
      · subst hst
        simp only [hG, sub_self, inv_zero, zero_smul, norm_zero]
        exact mul_nonneg hCnn (norm_nonneg _)
      · have hpos : 0 < |s - t| := abs_pos.mpr (sub_ne_zero.mpr hst)
        have hle := hC y s hsS
        have hinner : F s y - F t y = inner ℝ (nablaNfund (x - y)) (f y s - f y t) := by
          simp only [hF, inner_sub_right]
        have hGy : G s y = (s - t)⁻¹ • (F s y - F t y) := by simp only [hG]
        have hb : ‖inner ℝ (nablaNfund (x - y)) (f y s - f y t)‖
            ≤ ‖nablaNfund (x - y)‖ * (C * |s - t|) :=
          calc ‖inner ℝ (nablaNfund (x - y)) (f y s - f y t)‖
              ≤ ‖nablaNfund (x - y)‖ * ‖f y s - f y t‖ := norm_inner_le_norm _ _
            _ ≤ ‖nablaNfund (x - y)‖ * (C * |s - t|) :=
                mul_le_mul_of_nonneg_left hle (norm_nonneg _)
        rw [hGy, hinner, norm_smul, Real.norm_eq_abs, abs_inv]
        calc |s - t|⁻¹ * ‖inner ℝ (nablaNfund (x - y)) (f y s - f y t)‖
            ≤ |s - t|⁻¹ * (‖nablaNfund (x - y)‖ * (C * |s - t|)) :=
              mul_le_mul_of_nonneg_left hb (by positivity)
          _ = C * ‖nablaNfund (x - y)‖ := by
              have hsne' : |s - t| ≠ 0 := ne_of_gt hpos
              field_simp
    · have hynot : y ∉ closedBall (0 : R3) R := by
        rw [mem_closedBall, dist_eq_norm, sub_zero]
        exact hy
      have hby : bound y = 0 := by simp only [hbound, Set.indicator_of_notMem hynot]
      have hfs : f y s = 0 := by
        by_contra hne
        exact hy (hR s hsS y hne)
      have hft : f y t = 0 := by
        by_contra hne
        exact hy (hR t htS y hne)
      rw [hby]
      simp only [hG, hF, hfs, hft, inner_zero_right, sub_zero, smul_zero, norm_zero, le_refl]
  -- ## the pointwise limit of the difference quotients
  have hG_lim : ∀ᵐ y ∂volume, Tendsto (fun s => G s y) (𝓝[≠] t) (𝓝 (F' y)) := by
    refine ae_of_all _ (fun y => ?_)
    have hraw : Tendsto (fun s : ℝ => (s - t)⁻¹ • (f y s - f y t)) (𝓝[≠] t)
        (𝓝 (timeDeriv f y t)) := by
      simpa only [slope_def_module] using (show Tendsto (fun s : ℝ => slope (f y) t s) (𝓝[≠] t)
        (𝓝 (timeDeriv f y t)) from (hderiv y).tendsto_slope)
    have hcomp : Tendsto (fun s : ℝ =>
        inner ℝ (nablaNfund (x - y)) ((s - t)⁻¹ • (f y s - f y t))) (𝓝[≠] t)
        (𝓝 (inner ℝ (nablaNfund (x - y)) (timeDeriv f y t))) :=
      (tendsto_const_nhds (x := nablaNfund (x - y)) (f := 𝓝[≠] t)).inner hraw
    refine hcomp.congr' ?_
    filter_upwards with s
    simp only [hG, hF, inner_sub_right, real_inner_smul_right, smul_eq_mul]
  -- ## differentiation under the integral sign
  have hDCT := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := 𝓝[≠] t)
    (F := G) (f := F') bound hG_meas hG_bound hbound_int hG_lim
  -- ## identify the integrals of the difference quotients with the slopes
  have hslope : (fun s => ∫ y, G s y) =ᶠ[𝓝[≠] t] slope (fun s => ∫ y, F s y) t := by
    have hA : Set.Ioo (t - 1) (t + 1) ∈ 𝓝[≠] t := nhdsWithin_le_nhds hSnhds
    filter_upwards [self_mem_nhdsWithin, hA] with s hsne hsS
    have hIs : Integrable (F s) volume := hInt s hsS
    have hIt : Integrable (F t) volume := hInt t htS
    have h1 : (∫ y, G s y) = (s - t)⁻¹ • ∫ y, (F s y - F t y) := by
      simp only [hG, integral_smul]
    have h2 : (∫ y, (F s y - F t y)) = (∫ y, F s y) - ∫ y, F t y := integral_sub hIs hIt
    rw [h1, h2, slope_def_module]
  have hmain : Tendsto (slope (fun s => ∫ y, F s y) t) (𝓝[≠] t) (𝓝 (∫ y, F' y)) :=
    hDCT.congr' hslope
  have hderivF : HasDerivAt (fun s => ∫ y, F s y) (∫ y, F' y) t :=
    hasDerivAt_iff_tendsto_slope.mpr hmain
  have hneg := hderivF.neg
  have hfun : (fun s => pressurePotential (f · s) x) = -fun s => ∫ y, F s y := by
    funext s
    simp only [pressurePotential, hF, Pi.neg_apply]
  rw [hfun]
  simpa only [hF'] using hneg

end Work.FTS.PressureOn
