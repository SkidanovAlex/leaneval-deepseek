/-
# The fundamental-solution identity `∫ ℝ³ N(x - y) Δψ(x) dx = -ψ(y)`

This module proves `Work.FTS.PressureOn.PoissonAux.kernelIntegral`: for every `ψ : ℝ³ → ℝ` of
class `C^∞` with compact support and every centre `y`,

`∫ x, newtonKernel (x - y) * laplaceTrace ψ x = -ψ y`,

i.e. `Δ ((4π‖·‖)⁻¹) = -δ₀` weakly, which is the kernel-level content of the weak Poisson identity
`weakPoisson` and of `green_identity`.

## Route

The singular kernel is truncated near the origin: with `χ` the smooth profile of
`PoissonAux/Defs.lean` (`χ = 1` on `(-∞,1]`, `χ = 0` on `[2,∞)`) put

`M_ε x = smallCut ε x * newtonKernel x = (1 - χ(‖x‖²/ε²)) / (4π‖x‖)`

(`= cutProfile ε (‖x‖²)`, a `C²` function, constant near `0` and equal to `N` far out).  Its
Laplacian away from the origin is the *mass kernel*
`massKernel ε x = N x · ρ_ε''(‖x‖)`, `ρ_ε = rhoProfile ε` (`laplaceTrace_cutKernel`).

For `ε > 0` Green's identity (`Green.integral_mul_laplaceTrace_comm`) gives

`∫ x, M_ε x · Δψ x = ∫ x, ΔM_ε x · ψ x = ∫ x, massKernel ε x · ψ x`,

and the two sides are evaluated as `ε → 0⁺`:

* the left side tends to `∫ x, N x · Δψ x` by dominated convergence (the domination
  `‖N · Δψ‖` is integrable: `Δψ` is compactly supported and `‖·‖⁻¹ ∈ L¹_loc(ℝ³)`);
* the right side is a scaled approximate identity: writing `ρ_ε(r) = ρ_1(r/ε)` gives the
  pointwise scaling `massKernel ε x = (ε³)⁻¹ massKernel 1 (ε⁻¹ • x)` (`KI.massKernel_scale`), the
  change of variables `Measure.integral_comp_inv_smul` turns the integral into
  `∫ x, massKernel 1 x · ψ(ε • x)`, which converges to `ψ 0 · ∫ x, massKernel 1 x = -ψ 0` by
  dominated convergence (`KI.massKernel_peak`, `KI.massKernel_one_mass`).

The general centre `y` follows from the centred case applied to `ψ (· + y)` and the translation
invariance of the integral (`integral_sub_right_eq_self`), using that the Laplace trace commutes
with translations (`KI.laplaceTrace_comp_add`).
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.PoissonAux.Defs
import Submission.Work.FTS.PressureOn.PoissonAux.Ibp
import Submission.Work.FTS.PressureOn.PoissonAux.Ibp2
import Submission.Work.FTS.PressureOn.integral_div_eq_zero_of_hasFDerivAt
import Submission.Work.FTS.PressureOn.PoissonAux.laplaceTrace_cutKernel
import Submission.Work.FTS.PressureOn.Green.integral_mul_laplaceTrace_comm
import Submission.Work.FTS.PressureOn.Green.integrableOn_newtonKernel_ball
import Submission.Work.FTS.PressureOn.PoissonAux.KI.massKernel_one_mass
import Submission.Work.FTS.PressureOn.PoissonAux.KI.massKernel_scale
import Submission.Work.FTS.PressureOn.PoissonAux.KI.massKernel_peak
import Submission.Work.FTS.PressureOn.PoissonAux.KI.laplaceTrace_comp_add
import Submission.Work.FTS.PressureOn.PoissonAux.KI.integrable_newtonKernel_mul_laplaceTrace

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set MeasureTheory Metric Filter
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn.PoissonAux

/-! ## The truncated kernel is `C²` -/

/-- The truncated Newtonian kernel `x ↦ smallCut ε x * newtonKernel x` is `C²` for `ε > 0`: it is
`cutProfile ε (‖x‖²)`, and `cutProfile ε` is `C²` (`contDiff_cutProfile`). -/
lemma contDiff_smallCut_mul_newtonKernel (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ 2 (fun x : R3 => smallCut ε x * newtonKernel x) := by
  have h1 : ContDiff ℝ (2 : ℕ∞) (fun x : R3 => cutProfile ε (‖x‖ ^ 2)) :=
    (contDiff_cutProfile ε hε).comp (contDiff_norm_sq (𝕜 := ℝ) (n := (2 : ℕ∞)))
  refine contDiffOn_univ.1 ((contDiffOn_univ.2 h1).congr ?_)
  intro x _
  exact (cutProfile_normSq ε x).symm

/-! ## Green's identity for each truncation -/

/-- **Green's identity applied to the truncation.**  For `ε > 0`,

`∫ x, (smallCut ε x * newtonKernel x) * laplaceTrace Ψ x = ∫ x, massKernel ε x * Ψ x`,

because the two integrands differ by a divergence
(`Green.integral_mul_laplaceTrace_comm`), and away from the single point `0` the Laplacian of the
truncated kernel is the mass kernel (`laplaceTrace_cutKernel`). -/
lemma integral_cutKernel_mul_laplaceTrace_eq (ε : ℝ) (hε : 0 < ε) {Ψ : R3 → ℝ}
    (hΨ2 : ContDiff ℝ 2 Ψ) (hΨcs : HasCompactSupport Ψ) :
    ∫ x, (smallCut ε x * newtonKernel x) * laplaceTrace Ψ x
      = ∫ x, massKernel ε x * Ψ x := by
  have hcut : ContDiff ℝ 2 (fun x : R3 => smallCut ε x * newtonKernel x) :=
    contDiff_smallCut_mul_newtonKernel ε hε
  rw [Green.integral_mul_laplaceTrace_comm _ _ hcut hΨ2 hΨcs]
  refine integral_congr_ae ?_
  have hne : ∀ᵐ x ∂(volume : Measure R3), x ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simp
  filter_upwards [hne] with x hx
  rw [laplaceTrace_cutKernel ε hε hx]

/-! ## The `ε → 0⁺` limit of the truncated side -/

/-- **Dominated convergence for the truncated kernel.**  As `ε → 0⁺` the truncated kernel
`smallCut ε · newtonKernel` tends pointwise (off the origin) to `newtonKernel`, so
`∫ x, (smallCut ε x * N x) ΔΨ x → ∫ x, N x ΔΨ x` for `Ψ` of class `C²` with compact support. -/
lemma tendsto_integral_cutKernel {Ψ : R3 → ℝ} (hΨ2 : ContDiff ℝ 2 Ψ)
    (hΨcs : HasCompactSupport Ψ) :
    Tendsto (fun ε : ℝ => ∫ x, (smallCut ε x * newtonKernel x) * laplaceTrace Ψ x)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x, newtonKernel x * laplaceTrace Ψ x)) := by
  have hcont : Continuous (laplaceTrace Ψ) := Green.continuous_laplaceTrace Ψ hΨ2
  have hinte : Integrable (fun x : R3 => newtonKernel x * laplaceTrace Ψ x) :=
    KI.integrable_newtonKernel_mul_laplaceTrace hΨ2 hΨcs
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x : R3 => ‖newtonKernel x * laplaceTrace Ψ x‖) ?_ ?_ hinte.norm ?_
  · -- a.e. strong measurability
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hsc : Measurable (fun x : R3 => smallCut ε x) :=
      (contDiff_smallCut ε hε 0).continuous.measurable
    exact ((hsc.mul Green.measurable_newtonKernel).mul hcont.measurable).aestronglyMeasurable
  · -- domination
    filter_upwards with ε
    filter_upwards with x
    have habs : ‖smallCut ε x‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (smallCut_nonneg ε x)]
      exact smallCut_le_one ε x
    calc ‖(smallCut ε x * newtonKernel x) * laplaceTrace Ψ x‖
        = ‖smallCut ε x‖ * ‖newtonKernel x‖ * ‖laplaceTrace Ψ x‖ := by
          rw [norm_mul, norm_mul]
      _ = ‖smallCut ε x‖ * (‖newtonKernel x‖ * ‖laplaceTrace Ψ x‖) := by ring
      _ ≤ 1 * (‖newtonKernel x‖ * ‖laplaceTrace Ψ x‖) :=
          mul_le_mul_of_nonneg_right habs (by positivity)
      _ = ‖newtonKernel x * laplaceTrace Ψ x‖ := by rw [one_mul, norm_mul]
  · -- pointwise convergence
    filter_upwards with x
    by_cases hx : x = 0
    · subst hx
      have h0 : newtonKernel (0 : R3) = 0 := by simp [newtonKernel]
      rw [h0]
      simp
    · -- for `x ≠ 0` the cutoff tends to `1`
      have hδ : 0 < ‖x‖ / Real.sqrt 2 := by positivity
      have hmem : Ioo (0 : ℝ) (‖x‖ / Real.sqrt 2) ∈ 𝓝[>] (0 : ℝ) := by
        rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
        exact ⟨Iio _, Iio_mem_nhds hδ, fun y hy => ⟨hy.2, hy.1⟩⟩
      have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝[>] (0 : ℝ)]
          (fun ε : ℝ => radialCut (‖x‖ ^ 2 / ε ^ 2)) := by
        filter_upwards [hmem] with ε hε
        refine (radialCut_eq_zero ?_).symm
        rw [le_div_iff₀ (pow_pos hε.1 2)]
        have h2 : ε * Real.sqrt 2 < ‖x‖ := by
          have h := hε.2
          rw [lt_div_iff₀ (Real.sqrt_pos.mpr (by norm_num))] at h
          exact h
        have h4 : (ε * Real.sqrt 2) ^ 2 < ‖x‖ ^ 2 := by
          rw [sq_lt_sq,
            abs_of_nonneg (mul_nonneg (le_of_lt hε.1) (Real.sqrt_nonneg 2)),
            abs_of_nonneg (norm_nonneg x)]
          exact h2
        have h5 : (ε * Real.sqrt 2) ^ 2 = 2 * ε ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
          ring
        linarith
      have h0 : Tendsto (fun ε : ℝ => radialCut (‖x‖ ^ 2 / ε ^ 2))
          (𝓝[>] (0 : ℝ)) (𝓝 0) :=
        tendsto_const_nhds.congr' hev
      have hsm : Tendsto (fun ε : ℝ => smallCut ε x) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
        have h1 : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) :=
          tendsto_const_nhds
        have h := h1.sub h0
        simpa only [Pi.sub_apply, smallCut_apply, sub_zero] using h
      simpa using (hsm.mul tendsto_const_nhds).mul tendsto_const_nhds

/-! ## The centred fundamental identity -/

/-- **The centred fundamental solution identity.**  For `Ψ` of class `C²` with compact support,

`∫ x, newtonKernel x * laplaceTrace Ψ x = -Ψ 0`.

This is the `y = 0` case of `kernelIntegral`; the general case is deduced from it by translation. -/
lemma kernelIntegral_zero {Ψ : R3 → ℝ} (hΨ2 : ContDiff ℝ 2 Ψ) (hΨcs : HasCompactSupport Ψ) :
    ∫ x, newtonKernel x * laplaceTrace Ψ x = -Ψ 0 := by
  have hΨc : Continuous Ψ := hΨ2.continuous
  -- the per-`ε` identity: truncate, use Green, then rescale the mass kernel
  have hper : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∫ x, (smallCut ε x * newtonKernel x) * laplaceTrace Ψ x)
        = (∫ x, massKernel 1 x * Ψ (ε • x)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [integral_cutKernel_mul_laplaceTrace_eq ε hε hΨ2 hΨcs]
    have hp : ∀ x : R3, massKernel ε x * Ψ x
        = (ε ^ 3)⁻¹ * (massKernel 1 (ε⁻¹ • x) * Ψ x) := by
      intro x
      rw [KI.massKernel_scale ε hε x]
      ring
    calc ∫ x, massKernel ε x * Ψ x
        = ∫ x, (ε ^ 3)⁻¹ * (massKernel 1 (ε⁻¹ • x) * Ψ x) :=
          integral_congr_ae (Eventually.of_forall hp)
      _ = (ε ^ 3)⁻¹ * ∫ x, massKernel 1 (ε⁻¹ • x) * Ψ x := integral_const_mul _ _
      _ = (ε ^ 3)⁻¹
            * ∫ x, (fun u : R3 => massKernel 1 u * Ψ (ε • u)) (ε⁻¹ • x) := by
          congr 1
          refine integral_congr_ae (Eventually.of_forall ?_)
          intro x
          show massKernel 1 (ε⁻¹ • x) * Ψ x
            = massKernel 1 (ε⁻¹ • x) * Ψ (ε • (ε⁻¹ • x))
          rw [smul_inv_smul₀ (ne_of_gt hε)]
      _ = (ε ^ 3)⁻¹ * (|ε ^ 3| * ∫ x, massKernel 1 x * Ψ (ε • x)) := by
          rw [Measure.integral_comp_inv_smul (volume : Measure R3)
            (fun u : R3 => massKernel 1 u * Ψ (ε • u)) ε]
          simp [R3, smul_eq_mul]
      _ = ∫ x, massKernel 1 x * Ψ (ε • x) := by
          rw [abs_of_pos (pow_pos hε 3),
            inv_mul_cancel_left₀ (pow_ne_zero 3 (ne_of_gt hε))]
  -- the limit of the rescaled mass kernel is `-Ψ 0`
  have hlim2 : Tendsto (fun ε : ℝ => ∫ x, massKernel 1 x * Ψ (ε • x))
      (𝓝[>] (0 : ℝ)) (𝓝 (-Ψ 0)) := by
    have hpeak := KI.massKernel_peak hΨc
    rw [KI.massKernel_one_mass] at hpeak
    simpa using hpeak
  have hlim1 : Tendsto (fun ε : ℝ => ∫ x, massKernel 1 x * Ψ (ε • x))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x, newtonKernel x * laplaceTrace Ψ x)) :=
    (tendsto_integral_cutKernel hΨ2 hΨcs).congr' hper
  exact tendsto_nhds_unique hlim1 hlim2

/-! ## The fundamental solution identity -/

theorem kernelIntegral {ψ : R3 → ℝ} (hψ : ∀ n : ℕ, ContDiff ℝ n ψ) (hcs : HasCompactSupport ψ)
    (y : R3) :
    ∫ x, newtonKernel (x - y) * laplaceTrace ψ x = -ψ y := by
  have hψ2 : ContDiff ℝ 2 ψ := hψ 2
  -- the translate of `ψ` by `y` is again `C²` with compact support
  have hshift2 : ContDiff ℝ 2 (fun z : R3 => ψ (z + y)) :=
    hψ2.comp (contDiff_id.add contDiff_const)
  have hshift : HasCompactSupport (fun z : R3 => ψ (z + y)) := by
    have h := hcs.comp_homeomorph (Homeomorph.addRight y)
    simpa only [Function.comp_def, Homeomorph.coe_addRight] using h
  -- the translate of the integral
  have hsub : ∫ x, newtonKernel (x - y) * laplaceTrace ψ x
      = ∫ x, newtonKernel x * laplaceTrace ψ (x + y) := by
    have h := integral_sub_right_eq_self (μ := volume)
      (fun z : R3 => newtonKernel z * laplaceTrace ψ (z + y)) y
    simpa only [sub_add_cancel] using h
  -- the Laplace trace commutes with translation
  have hEq : (fun x : R3 => newtonKernel x * laplaceTrace ψ (x + y))
      = fun x : R3 => newtonKernel x * laplaceTrace (fun z : R3 => ψ (z + y)) x := by
    funext x
    rw [KI.laplaceTrace_comp_add ψ hψ2 y x]
  rw [hsub, hEq]
  have hz := kernelIntegral_zero hshift2 hshift
  simpa using hz

end Work.FTS.PressureOn.PoissonAux
