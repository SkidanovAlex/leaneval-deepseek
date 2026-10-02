/-
Copyright: Work.MRMT (mandelbar) subproject.

# The base identity of the Cauchy transform: `∫ ∂̄ψ / z = -π ψ(0)`

For `ψ : ℂ → ℂ` of class `C^∞` (`∞ = ↑(⊤ : ℕ∞)` in `ℕ∞ω = WithTop ℕ∞`; this is smoothness,
NOT the analytic order `⊤`) with compact support,

  `∫_ℂ ∂̄ψ(z) / z dz = -π ψ(0)`.

This is the distributional identity `∂̄(1/z) = -π δ₀` in integral form — the base case, translated
by `ζ`, of the Cauchy transform identity `∂̄(Cω) = ω` — and it is the `z`-integral produced when
Fubini is applied to `Work.MRMT.Cauchy.isDbarDeriv_cauchy_of_integrable`.

## Proof

For `ε > 0` put `K_ε(z) = z̄/(‖z‖²+ε²)`, a smooth mollification of `1/z` whose `∂̄` is
`ε²/(‖z‖²+ε²)²`, a mollified delta.  Integration by parts for `∂̄`
(`Work.MRMT.QC.integral_mul_dzbar_eq_neg`, applied with test function `K_ε` and the compactly
supported factor `ψ`) and the pointwise computation
`∂̄K_ε = ε²/(‖z‖²+ε²)²` (`Work.MRMT.Cauchy.dzbar_star_div_normSq_add`) give

  `∫ ∂̄ψ · K_ε = - ∫ ψ · ε²/(‖z‖²+ε²)²`   (`ε > 0`).

Both sides have well-defined limits as `ε → 0⁺`:
* `K_ε → 1/z` pointwise, with `‖K_ε‖ ≤ 1/‖z‖` summable near `0` in dimension two, so the left side
  tends to `∫ ∂̄ψ/z` by dominated convergence (proved below, in this file);
* substituting `z = ε w` turns the right side into `∫ ψ(εw)/(1+‖w‖²)² dw`, which tends to
  `ψ(0) ∫ (1+‖w‖²)⁻² dw = π ψ(0)`
  (`Work.MRMT.Cauchy.tendsto_integral_mul_kernelSq`).
Hence `∫ ∂̄ψ/z = -π ψ(0)`.
-/
import Mathlib
import Submission.Work.MRMT.Basic
import Submission.Work.MRMT.Sobolev.integral_dzbar_eq_zero_of_contDiff
import Submission.Work.MRMT.Sobolev.dzbar_mul
import Submission.Work.MRMT.QC.integral_mul_dzbar_eq_neg
import Submission.Work.MRMT.Cauchy.radial_kernel_integrable
import Submission.Work.MRMT.Cauchy.dzbar_star_div_normSq_add
import Submission.Work.MRMT.Cauchy.tendsto_integral_mul_kernelSq

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Complex Function Filter
open scoped Distributions Topology ENNReal

namespace Work.MRMT.Cauchy

/-- `∂̄ψ` vanishes at every point where `ψ` vanishes on a neighbourhood, in particular off the
topological support of `ψ`.  (If `ψ =ᶠ[𝓝 z] 0` then `fderiv ℝ ψ z = 0`, hence `∂̄ψ z = 0`.) -/
private theorem dzbar_eq_zero_of_notMem_tsupport {ψ : ℂ → ℂ} {z : ℂ} (hz : z ∉ tsupport ψ) :
    Work.MRMT.dzbar ψ z = 0 := by
  have hone : (tsupport ψ)ᶜ ∈ 𝓝 z := (isClosed_tsupport ψ).isOpen_compl.mem_nhds hz
  have hev : ψ =ᶠ[𝓝 z] 0 := by
    filter_upwards [hone] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  have hψ0 : HasFDerivAt ψ (0 : ℂ →L[ℝ] ℂ) z :=
    (hev.hasFDerivAt_iff).mpr (hasFDerivAt_const (0 : ℂ) z)
  simp [Work.MRMT.dzbar, hψ0.fderiv]

/-- The mollified kernel `z ↦ z̄/(‖z‖²+ε²)` (for `ε > 0`) is `C¹`, hence admissible as a test
function for `Work.MRMT.QC.integral_mul_dzbar_eq_neg`. -/
private theorem contDiff_one_cauKernel (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ 1 (fun z : ℂ => star z / ((‖z‖ ^ 2 + ε ^ 2 : ℝ) : ℂ)) := by
  have hstar : ContDiff ℝ 1 (fun z : ℂ => star z) := by
    have h : (star : ℂ → ℂ) = ⇑Complex.conjCLE := by funext z; simp
    rw [h]; exact Complex.conjCLE.contDiff
  have hre : ContDiff ℝ 1 (fun z : ℂ => z.re) := Complex.reCLM.contDiff
  have him : ContDiff ℝ 1 (fun z : ℂ => z.im) := Complex.imCLM.contDiff
  have hden : ContDiff ℝ 1 (fun z : ℂ => ((‖z‖ ^ 2 + ε ^ 2 : ℝ) : ℂ)) := by
    have h1 : ContDiff ℝ 1 (fun z : ℂ => (‖z‖ ^ 2 : ℝ)) := by
      rw [show (fun z : ℂ => (‖z‖ ^ 2 : ℝ)) = fun z => z.re * z.re + z.im * z.im from by
        funext z; rw [Complex.sq_norm, Complex.normSq_apply]]
      exact (hre.mul hre).add (him.mul him)
    exact Complex.ofRealCLM.contDiff.comp (h1.add contDiff_const)
  have hne : ∀ z : ℂ, ((‖z‖ ^ 2 + ε ^ 2 : ℝ) : ℂ) ≠ 0 := by
    intro z
    rw [Complex.ofReal_ne_zero]
    exact ne_of_gt (by nlinarith [sq_nonneg ‖z‖, sq_nonneg ε, norm_nonneg z, hε])
  have hinv : ContDiff ℝ 1 (fun z : ℂ => (((‖z‖ ^ 2 + ε ^ 2 : ℝ) : ℂ))⁻¹) := hden.inv hne
  convert hstar.mul hinv using 1
  funext z
  rw [div_eq_mul_inv]

/-- **The `ε`-identity.**  For smooth compactly supported `ψ` and `ε > 0`, integrating by parts
for `∂̄` against the mollified kernel `K_ε(z) = z̄/(‖z‖²+ε²)` gives

`∫_ℂ ∂̄ψ · K_ε = - ∫_ℂ ψ · ε²/(‖z‖²+ε²)²`.

(Integration by parts also works for merely `C¹` test functions; smoothness is used only to keep
the hypotheses of the file uniform.) -/
private theorem integral_dzbar_mul_cauKernel_eq_neg (ψ : ℂ → ℂ)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hs : HasCompactSupport ψ)
    (ε : ℝ) (hε : 0 < ε) :
    ∫ z, Work.MRMT.dzbar ψ z * (star z / ((‖z‖ ^ 2 + ε ^ 2 : ℝ) : ℂ))
      = - ∫ z, ψ z * ((ε : ℂ) ^ 2 / (((‖z‖ ^ 2 + ε ^ 2 : ℝ) : ℂ)) ^ 2) := by
  have hibp := Work.MRMT.QC.integral_mul_dzbar_eq_neg
    (f := fun z : ℂ => star z / ((‖z‖ ^ 2 + ε ^ 2 : ℝ) : ℂ)) (g := ψ)
    (contDiff_one_cauKernel ε hε) (hψ.of_le (by simp)) hs
  have h1 : ∫ z, (fun z : ℂ => star z / ((‖z‖ ^ 2 + ε ^ 2 : ℝ) : ℂ)) z * Work.MRMT.dzbar ψ z
      = ∫ z, Work.MRMT.dzbar ψ z * (star z / ((‖z‖ ^ 2 + ε ^ 2 : ℝ) : ℂ)) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    ring
  have h2 : ∫ z, Work.MRMT.dzbar (fun w : ℂ => star w / ((‖w‖ ^ 2 + ε ^ 2 : ℝ) : ℂ)) z * ψ z
      = ∫ z, ψ z * ((ε : ℂ) ^ 2 / (((‖z‖ ^ 2 + ε ^ 2 : ℝ) : ℂ)) ^ 2) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show Work.MRMT.dzbar (fun w : ℂ => star w / ((‖w‖ ^ 2 + ε ^ 2 : ℝ) : ℂ)) z * ψ z
      = ψ z * ((ε : ℂ) ^ 2 / (((‖z‖ ^ 2 + ε ^ 2 : ℝ) : ℂ)) ^ 2)
    rw [Work.MRMT.Cauchy.dzbar_star_div_normSq_add ε z]
    ring
  rw [h1, h2] at hibp
  exact hibp

/-- **First half of the base identity.**  For smooth compactly supported `ψ` the mollified
integrals `ε ↦ ∫_ℂ ∂̄ψ(z) · z̄/(‖z‖²+ε²) dz` converge, as `ε → 0⁺`, to `∫_ℂ ∂̄ψ(z)/z dz`.

Dominated convergence with the bound `‖∂̄ψ(z)‖/‖z‖`, using that `∂̄ψ` is continuous with compact
support and that `z ↦ 1/‖z‖` is integrable near the origin in dimension `2`
(`Work.MRMT.Cauchy.radial_kernel_integrable`). -/
theorem tendsto_integral_dzbar_mul_cauKernel (ψ : ℂ → ℂ)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hs : HasCompactSupport ψ) :
    Tendsto (fun ε : ℝ => ∫ z, Work.MRMT.dzbar ψ z * (star z / ((‖z‖ ^ 2 + ε ^ 2 : ℝ) : ℂ)))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ z, Work.MRMT.dzbar ψ z / z)) := by
  have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hfd : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv hne
  have hcdz : Continuous (Work.MRMT.dzbar ψ) := by
    unfold Work.MRMT.dzbar
    exact ((hfd.clm_apply continuous_const).add
      (continuous_const.mul (hfd.clm_apply continuous_const))).div_const 2
  -- the support of `ψ` sits in a closed ball, and `∂̄ψ` is bounded there
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hs.isCompact.isBounded
  set R₀ : ℝ := max R 1 with hR₀def
  have hR₀1 : (1 : ℝ) ≤ R₀ := le_max_right _ _
  have hR₀0 : (0 : ℝ) ≤ R₀ := le_trans zero_le_one hR₀1
  have hsub : tsupport ψ ⊆ Metric.closedBall (0 : ℂ) R₀ :=
    fun z hz => Metric.closedBall_subset_closedBall (le_max_left R 1) (hR hz)
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (0 : ℂ) R₀).exists_bound_of_continuousOn hcdz.continuousOn
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 (Metric.mem_closedBall_self hR₀0))
  -- the dominating function
  have hint : Integrable (fun z : ℂ => if ‖z‖ ≤ R₀ then ‖z‖ ^ (-1 : ℝ) else 0) volume := by
    have h := Work.MRMT.Cauchy.radial_kernel_integrable (0 : ℂ) R₀ (α := 1) (by norm_num)
    simpa using h
  have hbnd_int :
      Integrable (fun z : ℂ => C * (if ‖z‖ ≤ R₀ then ‖z‖ ^ (-1 : ℝ) else 0)) volume :=
    hint.const_mul C
  -- the pointwise bound, valid for every `ε`
  have hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ z ∂volume,
      ‖Work.MRMT.dzbar ψ z * (star z / ((‖z‖ ^ 2 + ε ^ 2 : ℝ) : ℂ))‖
        ≤ C * (if ‖z‖ ≤ R₀ then ‖z‖ ^ (-1 : ℝ) else 0) := by
    refine Filter.Eventually.of_forall (fun ε => Filter.Eventually.of_forall (fun z => ?_))
    by_cases hzR : ‖z‖ ≤ R₀
    · have hCz : ‖Work.MRMT.dzbar ψ z‖ ≤ C :=
        hC z (by simpa [Metric.mem_closedBall] using hzR)
      have hK : ‖star z / ((‖z‖ ^ 2 + ε ^ 2 : ℝ) : ℂ)‖ ≤ ‖z‖ ^ (-1 : ℝ) := by
        rw [norm_div, norm_star, Real.rpow_neg_one]
        rcases eq_or_ne z 0 with rfl | hz0
        · simp
        · have hQ : ‖((((‖z‖ ^ 2 + ε ^ 2 : ℝ))) : ℂ)‖ = ‖z‖ ^ 2 + ε ^ 2 := by
            rw [show ‖((((‖z‖ ^ 2 + ε ^ 2 : ℝ))) : ℂ)‖ = |(‖z‖ ^ 2 + ε ^ 2 : ℝ)| from
              RCLike.norm_ofReal (‖z‖ ^ 2 + ε ^ 2), abs_of_nonneg (by positivity)]
          rw [hQ]
          have h2 : ‖z‖ / (‖z‖ ^ 2 + ε ^ 2) ≤ ‖z‖ / ‖z‖ ^ 2 := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith [sq_nonneg ε, sq_nonneg ‖z‖, norm_nonneg z]
          have h3 : ‖z‖ / ‖z‖ ^ 2 = ‖z‖⁻¹ := by
            rw [sq, div_mul_eq_div_div_swap, div_self (by positivity : ‖z‖ ≠ 0), one_div]
          rwa [h3] at h2
      calc ‖Work.MRMT.dzbar ψ z * (star z / ((‖z‖ ^ 2 + ε ^ 2 : ℝ) : ℂ))‖
          = ‖Work.MRMT.dzbar ψ z‖ * ‖star z / ((‖z‖ ^ 2 + ε ^ 2 : ℝ) : ℂ)‖ := norm_mul _ _
        _ ≤ C * ‖z‖ ^ (-1 : ℝ) := mul_le_mul hCz hK (norm_nonneg _) hC0
        _ = C * (if ‖z‖ ≤ R₀ then ‖z‖ ^ (-1 : ℝ) else 0) := by rw [if_pos hzR]
    · have hdz0 : Work.MRMT.dzbar ψ z = 0 :=
        dzbar_eq_zero_of_notMem_tsupport
          (fun hmem => hzR (by simpa [Metric.mem_closedBall, dist_eq_norm] using hsub hmem))
      simp [hdz0, if_neg hzR]
  -- the pointwise limit
  have hlim : ∀ᵐ z ∂volume, Tendsto (fun ε : ℝ =>
        Work.MRMT.dzbar ψ z * (star z / ((‖z‖ ^ 2 + ε ^ 2 : ℝ) : ℂ)))
      (𝓝[>] (0 : ℝ)) (𝓝 (Work.MRMT.dzbar ψ z / z)) := by
    refine Filter.Eventually.of_forall (fun z => ?_)
    rcases eq_or_ne z 0 with rfl | hz0
    · have hfun : (fun ε : ℝ =>
            Work.MRMT.dzbar ψ (0 : ℂ) * (star (0 : ℂ) / ((‖(0 : ℂ)‖ ^ 2 + ε ^ 2 : ℝ) : ℂ)))
          = fun _ : ℝ => (0 : ℂ) := by
        funext ε; simp
      rw [hfun]
      simpa using tendsto_const_nhds
    · have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
      have hcont : Continuous (fun ε : ℝ => star z / ((‖z‖ ^ 2 + ε ^ 2 : ℝ) : ℂ)) := by
        refine Continuous.div continuous_const (by fun_prop) (fun ε => ?_)
        rw [Complex.ofReal_ne_zero]
        exact ne_of_gt (by nlinarith [sq_nonneg ‖z‖, sq_nonneg ε, norm_nonneg z, hzpos])
      have h0 : star z / ((‖z‖ ^ 2 + 0 ^ 2 : ℝ) : ℂ) = 1 / z := by
        rw [show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero]
        have hQz : (((‖z‖ ^ 2 : ℝ)) : ℂ) = z * star z := by
          rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]; simp
        rw [hQz, div_mul_eq_div_div_swap, div_self (star_ne_zero.mpr hz0)]
      have h1 : Tendsto (fun ε : ℝ => star z / ((‖z‖ ^ 2 + ε ^ 2 : ℝ) : ℂ)) (𝓝 0)
          (𝓝 (star z / ((‖z‖ ^ 2 + 0 ^ 2 : ℝ) : ℂ))) := hcont.tendsto 0
      rw [h0] at h1
      have h2 := (h1.const_mul (Work.MRMT.dzbar ψ z)).mono_left
        (nhdsWithin_le_nhds : 𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
      simpa [div_eq_mul_inv] using h2
  refine tendsto_integral_filter_of_dominated_convergence
    (fun z : ℂ => C * (if ‖z‖ ≤ R₀ then ‖z‖ ^ (-1 : ℝ) else 0)) ?_ hbound hbnd_int hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hQcont : Continuous (fun z : ℂ => ((‖z‖ ^ 2 + ε ^ 2 : ℝ) : ℂ)) := by fun_prop
  have hQne : ∀ z : ℂ, ((‖z‖ ^ 2 + ε ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have hε' : (0 : ℝ) < ε := hε
    intro z
    rw [Complex.ofReal_ne_zero]
    exact ne_of_gt (by nlinarith [sq_nonneg ‖z‖, sq_nonneg ε, norm_nonneg z, hε'])
  exact (hcdz.mul (Continuous.div continuous_star hQcont hQne)).aestronglyMeasurable

theorem integral_dzbar_div_eq_neg_pi_mul (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hs : HasCompactSupport ψ) :
    ∫ z, Work.MRMT.dzbar ψ z / z = -(Real.pi : ℂ) * ψ 0 := by
  have hlim1 := tendsto_integral_dzbar_mul_cauKernel ψ hψ hs
  have hlim2 := Work.MRMT.Cauchy.tendsto_integral_mul_kernelSq ψ hψ.continuous hs
  have hadj : (fun ε : ℝ => ∫ z, Work.MRMT.dzbar ψ z * (star z / ((‖z‖ ^ 2 + ε ^ 2 : ℝ) : ℂ)))
      =ᶠ[𝓝[>] (0 : ℝ)]
        fun ε : ℝ => - ∫ z, ψ z * ((ε : ℂ) ^ 2 / (((‖z‖ ^ 2 + ε ^ 2 : ℝ) : ℂ)) ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact integral_dzbar_mul_cauKernel_eq_neg ψ hψ hs ε hε
  have hlim2' : Tendsto
      (fun ε : ℝ => - ∫ z, ψ z * ((ε : ℂ) ^ 2 / (((‖z‖ ^ 2 + ε ^ 2 : ℝ) : ℂ)) ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 (-((Real.pi : ℂ) * ψ 0))) := hlim2.neg
  have hlim1' : Tendsto
      (fun ε : ℝ => ∫ z, Work.MRMT.dzbar ψ z * (star z / ((‖z‖ ^ 2 + ε ^ 2 : ℝ) : ℂ)))
      (𝓝[>] (0 : ℝ)) (𝓝 (-((Real.pi : ℂ) * ψ 0))) :=
    Filter.Tendsto.congr' hadj.symm hlim2'
  have huniq : (∫ z, Work.MRMT.dzbar ψ z / z) = -((Real.pi : ℂ) * ψ 0) :=
    tendsto_nhds_unique hlim1 hlim1'
  simpa [neg_mul] using huniq

end Work.MRMT.Cauchy
