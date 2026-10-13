import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.CurlGrad.fderiv_normed_convolution_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Filter
open scoped Convolution Topology Pointwise

namespace Work.FTS.PressureOn.CurlGrad

/-- **The smoothing limit step.**  Let `ω : ℝ³ → ℝ³` be continuous, `ψ : ℝ³ → ℝ` of class `C¹`
with compact support, and `φ n` a sequence of bump functions with `rOut → 0`.  Then the integrals of
`x ↦ d(ρ_n ⋆ ψ)(x)(ω x)` converge to the integral of `x ↦ dψ(x)(ω x)`:

`Tendsto (fun n => ∫ x, fderiv ℝ (ρ_n ⋆ ψ) x (ω x)) atTop (𝓝 (∫ x, fderiv ℝ ψ x (ω x)))`.

Please declare it in `namespace Work.FTS.PressureOn.CurlGrad` so that its full name is
`Work.FTS.PressureOn.CurlGrad.tendsto_integral_inner_fderiv_convolution`.

Route (all ingredients are in Mathlib; note `(φ n).normed volume` needs `open MeasureTheory` or the
explicit `MeasureTheory.MeasureSpace.volume`):
* For each `n` the integrand is
  `x ↦ ∫ t, (φ n).normed volume t * (fderiv ℝ ψ (x - t) (ω x)) ∂volume`: differentiate the
  convolution with `HasCompactSupport.hasFDerivAt_convolution_right`
  (`Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`) with `L := ContinuousLinearMap.lsmul ℝ ℝ`,
  `f := (φ n).normed volume`, `g := ψ`, then evaluate the `ContinuousLinearMap.precompR`-convolution
  at `ω x` with `MeasureTheory.convolution_precompR_apply`
  (`Mathlib/Analysis/Convolution.lean`); `MeasureTheory.convolution_def` unfolds the definition.
  (This is the already-proved lemma `Work.FTS.PressureOn.CurlGrad.fderiv_normed_convolution_eq` in
  `Submission/Work/FTS/PressureOn/CurlGrad/fderiv_normed_convolution_eq.lean`.)
* Pointwise convergence for fixed `x` is `ContDiffBump.convolution_tendsto_right_of_continuous`
  applied to the continuous function `g := fun y => fderiv ℝ ψ y (ω x)` — note that
  `(ρ_n ⋆ g) x = ∫ t, (φ n).normed volume t * g (x - t)`, so its value at `x` converges to
  `g x = fderiv ℝ ψ x (ω x)`.
* Domination: `‖fderiv ℝ ψ y‖ ≤ M` for all `y` and some `M ≥ 0` (use `hψcs.fderiv ℝ` and
  `(hψ.continuous_fderiv (by norm_num)).norm` / `HasCompactSupport.exists_norm_le`), and
  `fderiv ℝ ψ` vanishes off `tsupport ψ`; since the support of `(φ n).normed volume` is
  `Metric.ball 0 (φ n).rOut` (`ContDiffBump.support_normed_eq`), for all large `n` the integrand is
  dominated by `fun x => M * ‖ω x‖ * (Metric.closedBall 0 R).indicator (fun _ => 1) x` for a large
  radius `R` (with `Metric.closedBall 0 R ⊇ tsupport ψ + Metric.closedBall 0 1`); that dominator is
  integrable because `‖ω‖` is bounded on the compact set `Metric.closedBall 0 R`
  (`IsCompact.exists_bound_of_continuousOn` / `Continuous.norm`), and
  `MeasureTheory.tendsto_integral_of_dominated_convergence` closes the proof. -/
theorem tendsto_integral_inner_fderiv_convolution
    {ω : Work.FTS.PressureOn.R3 → Work.FTS.PressureOn.R3} (hω : Continuous ω)
    {ψ : Work.FTS.PressureOn.R3 → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψcs : HasCompactSupport ψ)
    {φ : ℕ → ContDiffBump (0 : Work.FTS.PressureOn.R3)}
    (hφ : Filter.Tendsto (fun n => (φ n).rOut) Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => ∫ x, fderiv ℝ (MeasureTheory.convolution ((φ n).normed volume) ψ
          (ContinuousLinearMap.lsmul ℝ ℝ) volume) x (ω x))
      Filter.atTop
      (nhds (∫ x, fderiv ℝ ψ x (ω x))) := by
  -- ## Elementary facts about `ψ`
  -- `fderiv ψ` vanishes off the (closed) topological support of `ψ`.
  have hfderiv_zero : ∀ y ∉ tsupport ψ, fderiv ℝ ψ y = 0 := by
    intro y hy
    have hmem : (tsupport ψ)ᶜ ∈ 𝓝 y := (isClosed_tsupport ψ).isOpen_compl.mem_nhds hy
    have heq : (fun _ : R3 => (0:ℝ)) =ᶠ[𝓝 y] ψ := by
      filter_upwards [hmem] with z hz
      exact (image_eq_zero_of_notMem_tsupport hz).symm
    rw [heq.symm.fderiv_eq]
    simp
  -- A uniform bound `M` for `‖fderiv ψ‖`.
  obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ y : R3, ‖fderiv ℝ ψ y‖ ≤ M := by
    obtain ⟨C, hC⟩ : ∃ C, ∀ y ∈ tsupport ψ, ‖fderiv ℝ ψ y‖ ≤ C :=
      hψcs.isCompact.exists_bound_of_continuousOn (hψ.continuous_fderiv one_ne_zero).continuousOn
    refine ⟨max C 0, le_max_right _ _, fun y => ?_⟩
    by_cases hy : y ∈ tsupport ψ
    · exact le_trans (hC y hy) (le_max_left _ _)
    · rw [hfderiv_zero y hy, norm_zero]
      exact le_max_right _ _
  -- A large radius `R` containing `tsupport ψ + closedBall 0 1`.
  obtain ⟨R, hR⟩ : ∃ R : ℝ, tsupport ψ + Metric.closedBall (0:R3) 1 ⊆ Metric.closedBall 0 R := by
    have hcomp : IsCompact (tsupport ψ + Metric.closedBall (0:R3) 1) :=
      hψcs.isCompact.add (isCompact_closedBall (0:R3) 1)
    exact (Metric.isBounded_iff_subset_closedBall (0:R3)).1 hcomp.isBounded
  -- ## Rewriting the integrand as a convolution integral
  have hF : ∀ n x, fderiv ℝ (MeasureTheory.convolution ((φ n).normed volume) ψ
        (ContinuousLinearMap.lsmul ℝ ℝ) volume) x (ω x)
      = ∫ t, (φ n).normed volume t * fderiv ℝ ψ (x - t) (ω x) := by
    intro n x
    rw [fderiv_normed_convolution_eq hψ hψcs x (ω x)]
    rw [MeasureTheory.convolution_def]
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  -- ## A uniform pointwise bound for the rewritten integrand
  have hF_le : ∀ n x, ‖∫ t, (φ n).normed volume t * fderiv ℝ ψ (x - t) (ω x)‖ ≤ M * ‖ω x‖ := by
    intro n x
    have hρ : Integrable (fun t : R3 => (φ n).normed volume t) volume := (φ n).integrable_normed
    have hdom : Integrable (fun t : R3 => (φ n).normed volume t * (M * ‖ω x‖)) volume :=
      hρ.mul_const _
    have hle : ∀ t : R3, ‖(φ n).normed volume t * fderiv ℝ ψ (x - t) (ω x)‖
        ≤ (φ n).normed volume t * (M * ‖ω x‖) := by
      intro t
      rw [norm_mul, Real.norm_of_nonneg ((φ n).nonneg_normed t)]
      have h1 : ‖fderiv ℝ ψ (x - t) (ω x)‖ ≤ M * ‖ω x‖ :=
        calc ‖fderiv ℝ ψ (x - t) (ω x)‖ ≤ ‖fderiv ℝ ψ (x - t)‖ * ‖ω x‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ M * ‖ω x‖ := mul_le_mul_of_nonneg_right (hM (x - t)) (norm_nonneg _)
      exact mul_le_mul_of_nonneg_left h1 ((φ n).nonneg_normed t)
    calc ‖∫ t, (φ n).normed volume t * fderiv ℝ ψ (x - t) (ω x)‖
        ≤ ∫ t, ‖(φ n).normed volume t * fderiv ℝ ψ (x - t) (ω x)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ t, (φ n).normed volume t * (M * ‖ω x‖) :=
          integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _) hdom
            (Eventually.of_forall hle)
      _ = M * ‖ω x‖ := by
          rw [integral_mul_const, ContDiffBump.integral_normed, one_mul]
  -- ## The integrand vanishes off `closedBall 0 R` once `rOut ≤ 1`
  have hzeroF : ∀ n, (φ n).rOut ≤ 1 → ∀ x ∉ Metric.closedBall (0:R3) R,
      (∫ t, (φ n).normed volume t * fderiv ℝ ψ (x - t) (ω x)) = 0 := by
    intro n hn x hx
    have hzero : (fun t => (φ n).normed volume t * fderiv ℝ ψ (x - t) (ω x)) = fun _ => (0:ℝ) := by
      funext t
      by_cases ht : (φ n).normed volume t = 0
      · simp [ht]
      · have ht_ball : t ∈ Metric.ball (0:R3) ((φ n).rOut) := by
          rw [← ContDiffBump.support_normed_eq (f := φ n) (μ := (volume : Measure R3))]
          exact ht
        have ht_norm : ‖t‖ < (φ n).rOut := by
          simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using ht_ball
        have ht1 : t ∈ Metric.closedBall (0:R3) 1 := by
          simp only [Metric.mem_closedBall, dist_zero_right]
          linarith
        have hxt : x - t ∉ tsupport ψ := by
          intro hcon
          exact hx (hR ⟨x - t, hcon, t, ht1, sub_add_cancel x t⟩)
        simp [hfderiv_zero (x - t) hxt]
    rw [hzero]
    simp
  -- ## The dominator, and its integrability
  have hBd_meas : MeasurableSet (Metric.closedBall (0:R3) R) :=
    (isCompact_closedBall (0:R3) R).isClosed.measurableSet
  have hbound_int : Integrable
      (fun x : R3 => M * ‖ω x‖ * (Metric.closedBall (0:R3) R).indicator (fun _ => (1:ℝ)) x)
      volume := by
    have heq : (fun x : R3 => M * ‖ω x‖ * (Metric.closedBall (0:R3) R).indicator (fun _ => (1:ℝ)) x)
        = (Metric.closedBall (0:R3) R).indicator (fun x : R3 => M * ‖ω x‖) := by
      funext x
      by_cases hx : x ∈ Metric.closedBall (0:R3) R
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]
    rw [heq]
    exact (integrable_indicator_iff hBd_meas).2
      ((continuous_const.mul hω.norm).continuousOn.integrableOn_compact (isCompact_closedBall 0 R))
  have hbound_ev : ∀ᶠ n in atTop, ∀ᵐ x ∂(volume : Measure R3),
      ‖∫ t, (φ n).normed volume t * fderiv ℝ ψ (x - t) (ω x)‖
        ≤ M * ‖ω x‖ * (Metric.closedBall (0:R3) R).indicator (fun _ => (1:ℝ)) x := by
    filter_upwards [hφ.eventually (eventually_le_nhds zero_lt_one)] with n hn
    refine Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ Metric.closedBall (0:R3) R
    · rw [Set.indicator_of_mem hx, mul_one]
      exact hF_le n x
    · rw [Set.indicator_of_notMem hx, mul_zero, hzeroF n hn x hx, norm_zero]
  -- ## Measurability
  have hmeas : ∀ᶠ n in atTop, AEStronglyMeasurable
      (fun x : R3 => ∫ t, (φ n).normed volume t * fderiv ℝ ψ (x - t) (ω x)) volume := by
    refine Eventually.of_forall fun n => ?_
    have hconv : ContDiff ℝ 1 (MeasureTheory.convolution ((φ n).normed volume) ψ
        (ContinuousLinearMap.lsmul ℝ ℝ) volume) :=
      hψcs.contDiff_convolution_right (L := ContinuousLinearMap.lsmul ℝ ℝ)
        ((φ n).integrable_normed.locallyIntegrable) hψ
    have hcont : Continuous (fun x : R3 => fderiv ℝ (MeasureTheory.convolution ((φ n).normed volume) ψ
        (ContinuousLinearMap.lsmul ℝ ℝ) volume) x (ω x)) :=
      (hconv.continuous_fderiv one_ne_zero).clm_apply hω
    exact hcont.aestronglyMeasurable.congr (Eventually.of_forall (hF n))
  -- ## Pointwise convergence at every `x`
  have hlim : ∀ᵐ x ∂(volume : Measure R3), Tendsto
      (fun n => ∫ t, (φ n).normed volume t * fderiv ℝ ψ (x - t) (ω x)) atTop
      (𝓝 (fderiv ℝ ψ x (ω x))) := by
    refine Eventually.of_forall fun x => ?_
    have hgc : Continuous (fun y : R3 => fderiv ℝ ψ y (ω x)) :=
      (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have h := ContDiffBump.convolution_tendsto_right_of_continuous (φ := φ)
      (g := fun y : R3 => fderiv ℝ ψ y (ω x)) (μ := (volume : Measure R3)) hφ hgc x
    simpa only [MeasureTheory.convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul] using h
  -- ## Dominated convergence, and transport back to the original integrand
  refine Tendsto.congr (fun n => ?_) (tendsto_integral_filter_of_dominated_convergence
    (fun x : R3 => M * ‖ω x‖ * (Metric.closedBall (0:R3) R).indicator (fun _ => (1:ℝ)) x)
    hmeas hbound_ev hbound_int hlim)
  exact integral_congr_ae (Eventually.of_forall fun x => (hF n x).symm)

end Work.FTS.PressureOn.CurlGrad
