import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.RingTheory.TotallySplit
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## Two elementary facts used by the transfer identity

`ρ` is supported in the closed unit ball (`IsMollKernel.support`), so every point at which `ρ` does
not vanish lies in `Metric.closedBall 0 1`; and the `log z`-shift `x ↦ log z - εx` of an integrable
log-coordinate trace stays integrable on the line (translation invariance of the Lebesgue measure
plus the dilation `x ↦ -ε x`). -/

/-- A point at which an admissible kernel does not vanish lies in the closed unit ball. -/
lemma mti_mem_ball_of_support {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {q : ℝ × ℝ} (hq : ρ q ≠ 0) : q ∈ Metric.closedBall (0 : ℝ × ℝ) 1 := by
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
  have hs := hρ.support q hq
  have h1 : q.1 ^ 2 ≤ 1 ^ 2 := by nlinarith [sq_nonneg q.2]
  have h2 : q.2 ^ 2 ≤ 1 ^ 2 := by nlinarith [sq_nonneg q.1]
  refine max_le ?_ ?_
  · simpa using ((sq_le_sq.mp h1) : |q.1| ≤ |(1 : ℝ)|)
  · simpa using ((sq_le_sq.mp h2) : |q.2| ≤ |(1 : ℝ)|)

/-- **Integrability of the shifted absolute trace.**  If `u ↦ lam (exp u)` is integrable on the
line and `ε > 0`, `z > 0`, then so is `x ↦ |lam (z exp (-(ε x)))|`.  Indeed
`z exp (-(ε x)) = exp (log z - ε x)`, and the affine map `x ↦ log z - ε x` preserves
integrability (`MeasureTheory.MeasurePreserving.integrable_comp_emb` for the translation,
`Integrable.comp_mul_left'` for the dilation). -/
lemma mti_integrable_shift_abs {lam : ℝ → ℝ}
    (hint : MeasureTheory.Integrable (fun u : ℝ => lam (Real.exp u)))
    {ε z : ℝ} (hε : 0 < ε) (hz : 0 < z) :
    MeasureTheory.Integrable (fun x : ℝ => |lam (z * Real.exp (-(ε * x)))|) volume := by
  have hshift : MeasureTheory.Integrable (fun y : ℝ => lam (Real.exp (y + Real.log z))) volume := by
    have hmp : MeasureTheory.MeasurePreserving (fun y : ℝ => y + Real.log z) volume volume :=
      MeasureTheory.measurePreserving_add_right volume (Real.log z)
    have hemb : MeasurableEmbedding (fun y : ℝ => y + Real.log z) :=
      measurableEmbedding_addRight (Real.log z)
    exact (hmp.integrable_comp_emb hemb).mpr hint
  have hscale : MeasureTheory.Integrable (fun x : ℝ => lam (Real.exp ((-ε) * x + Real.log z)))
      volume :=
    hshift.comp_mul_left' (by linarith : (-ε) ≠ 0)
  have hfun : ∀ x : ℝ, lam (Real.exp ((-ε) * x + Real.log z)) = lam (z * Real.exp (-(ε * x))) := by
    intro x
    congr 1
    rw [show (-ε) * x + Real.log z = Real.log z - ε * x by ring, Real.exp_sub, Real.exp_log hz]
    rw [div_eq_mul_inv, Real.exp_neg]
  have hscale' : MeasureTheory.Integrable (fun x : ℝ => lam (z * Real.exp (-(ε * x)))) volume :=
    hscale.congr (Filter.Eventually.of_forall hfun)
  simpa only [Real.norm_eq_abs] using hscale'.norm

/-- **The transfer identity for the log-coordinate kernel.**  For an admissible mollifier kernel
`ρ` (`Work.FTS.StrongEps.IsMollKernel`: continuous, supported in the closed unit ball,
nonnegative, total mass one), `ε > 0`, `z > 0` and a measurable `lam` whose log-coordinate trace
is integrable,

  `∫ p, Jker ρ ε p * lam (z * exp (-p.1)) = ∫ s, (∫ t, ρ (s,t)) * lam (z * exp (-(ε * s)))`.

Route: the change of variables `p ↦ ε⁻¹ • p`
(`MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg`, unconditional), followed by Fubini on
the `s`-marginal of `ρ`.  The absolute convergence needed by Fubini follows from `hint`: `ρ` is
bounded and supported in the unit ball, so `|q₁| ≤ 1` on its support and
`∫_{|q₁| ≤ 1} |lam (z exp (-ε q₁))| dq₁ = ε⁻¹ ∫_{log z - ε}^{log z + ε} |lam (exp u)| du`.
The same identity with a *local bound* on `lam`, `hC : ∀ q, ρ q ≠ 0 → |lam (z exp (-ε q.1))| ≤ C`,
is already proved as `integral_Jker_mul_eq_marginal` in
`Submission/Work/FTS/StrongEps/EpsLocalPStar/JepsTraceTransfer.lean` — do NOT import that module
(it contains an unproved declaration); reproduce the argument with `hint` in place of `hC`.
Declare the result in the namespace `Work.FTS.StrongEps.EpsLocalPStar`. -/
theorem MarginalTransferIntegrable {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {ε z : ℝ} (hε : 0 < ε) (hz : 0 < z) {lam : ℝ → ℝ} (hlamm : Measurable lam)
    (hint : MeasureTheory.Integrable (fun u : ℝ => lam (Real.exp u))) :
    (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p * lam (z * Real.exp (-p.1)))
      = ∫ s : ℝ, (∫ t : ℝ, ρ (s, t)) * lam (z * Real.exp (-(ε * s))) := by
  classical
  -- a uniform bound for `ρ` on the unit ball (continuity + compact support)
  obtain ⟨C₀, hC₀⟩ := (isCompact_closedBall (0 : ℝ × ℝ) 1).exists_bound_of_continuousOn
    hρ.cont.continuousOn
  set Cρ : ℝ := |C₀| with hCρdef
  have hCρnn : 0 ≤ Cρ := by rw [hCρdef]; exact abs_nonneg _
  have hCρ : ∀ q : ℝ × ℝ, q ∈ Metric.closedBall (0 : ℝ × ℝ) 1 → ‖ρ q‖ ≤ Cρ :=
    fun q hq => (hC₀ q hq).trans (le_abs_self _)
  have hΛabs : MeasureTheory.Integrable (fun x : ℝ => |lam (z * Real.exp (-(ε * x)))|) volume :=
    mti_integrable_shift_abs hint hε hz
  -- the dominating function `Cρ * |lam (z exp (-ε q₁))|` is integrable over the unit square
  have hbox : MeasureTheory.IntegrableOn
      (fun q : ℝ × ℝ => Cρ * |lam (z * Real.exp (-(ε * q.1)))|)
      (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1) volume := by
    have h1 : MeasureTheory.Integrable (fun x : ℝ => Cρ * |lam (z * Real.exp (-(ε * x)))|)
        (volume.restrict (Set.Icc (-1 : ℝ) 1)) := (hΛabs.const_mul Cρ).integrableOn
    have h2 : MeasureTheory.Integrable (fun _ : ℝ => (1 : ℝ))
        (volume.restrict (Set.Icc (-1 : ℝ) 1)) :=
      integrableOn_const (by simp)
    have h3 := h1.mul_prod h2
    rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod ℝ ℝ] at h3
    simpa only [MeasureTheory.IntegrableOn, mul_one] using h3
  have hsub : Metric.closedBall (0 : ℝ × ℝ) 1 ⊆ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1 := by
    intro q hq
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def] at hq
    have h1 : |q.1| ≤ 1 := by
      have h : ‖q.1‖ ≤ 1 := (le_max_left (‖q.1‖) (‖q.2‖)).trans hq
      simpa using h
    have h2 : |q.2| ≤ 1 := by
      have h : ‖q.2‖ ≤ 1 := (le_max_right (‖q.1‖) (‖q.2‖)).trans hq
      simpa using h
    exact ⟨by rw [Set.mem_Icc]; exact abs_le.mp h1, by rw [Set.mem_Icc]; exact abs_le.mp h2⟩
  have hball : MeasureTheory.IntegrableOn
      (fun q : ℝ × ℝ => Cρ * |lam (z * Real.exp (-(ε * q.1)))|)
      (Metric.closedBall (0 : ℝ × ℝ) 1) volume := hbox.mono_set hsub
  have hg : MeasureTheory.Integrable
      ((Metric.closedBall (0 : ℝ × ℝ) 1).indicator
        (fun q : ℝ × ℝ => Cρ * |lam (z * Real.exp (-(ε * q.1)))|)) volume :=
    hball.integrable_indicator Metric.isClosed_closedBall.measurableSet
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun q : ℝ × ℝ => ρ q * lam (z * Real.exp (-(ε * q.1)))) volume :=
    hρ.cont.aestronglyMeasurable.mul (hlamm.comp (by fun_prop)).aestronglyMeasurable
  -- hence the `q`-integrand of the marginal is integrable
  have hGint : MeasureTheory.Integrable
      (fun q : ℝ × ℝ => ρ q * lam (z * Real.exp (-(ε * q.1)))) volume := by
    refine hg.mono' haesm ?_
    filter_upwards with q
    by_cases hq : ρ q = 0
    · rw [hq, zero_mul, norm_zero]
      exact Set.indicator_nonneg (fun a _ => mul_nonneg hCρnn (abs_nonneg _)) q
    · have hmem : q ∈ Metric.closedBall (0 : ℝ × ℝ) 1 := mti_mem_ball_of_support hρ hq
      rw [Set.indicator_of_mem hmem, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (by simpa using hCρ q hmem) (abs_nonneg _)
  -- step 1: the change of variables `p ↦ ε⁻¹ • p` (unconditional)
  have hstep : (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p * lam (z * Real.exp (-p.1)))
      = ∫ q : ℝ × ℝ, ρ q * lam (z * Real.exp (-(ε * q.1))) := by
    let g : ℝ × ℝ → ℝ := fun q => ε⁻¹ ^ 2 * (ρ q * lam (z * Real.exp (-(ε * q.1))))
    have h1 : (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p * lam (z * Real.exp (-p.1)))
        = ∫ p : ℝ × ℝ, g (ε⁻¹ • p) := by
      refine integral_congr_ae (Eventually.of_forall fun p => ?_)
      have hε1 : ε * (ε⁻¹ * p.1) = p.1 := by
        rw [← mul_assoc, mul_inv_cancel₀ hε.ne', one_mul]
      have hfst : (ε⁻¹ • p).1 = ε⁻¹ * p.1 := rfl
      simp only [Work.FTS.StrongEps.Jker, g, hfst, hε1]
      ring
    have h2 := MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg
      (μ := (volume : Measure (ℝ × ℝ))) g hε.le
    rw [show Module.finrank ℝ (ℝ × ℝ) = 2 from by simp [Module.finrank_prod],
      smul_eq_mul] at h2
    rw [h1, h2]
    have h3 : (∫ q : ℝ × ℝ, g q)
        = ε⁻¹ ^ 2 * ∫ q : ℝ × ℝ, ρ q * lam (z * Real.exp (-(ε * q.1))) := by
      simp only [g]
      rw [MeasureTheory.integral_const_mul]
    rw [h3]
    have h4 : ε ^ 2 * ε⁻¹ ^ 2 = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hε.ne', one_pow]
    rw [← mul_assoc, h4, one_mul]
  -- step 2: Fubini on the `s`-marginal of `ρ`
  have hGint' : MeasureTheory.Integrable
      (fun q : ℝ × ℝ => ρ q * lam (z * Real.exp (-(ε * q.1)))) (volume.prod volume) := by
    simpa only [MeasureTheory.Measure.volume_eq_prod ℝ ℝ] using hGint
  have hR : (∫ s, (∫ t, ρ (s, t)) * lam (z * Real.exp (-(ε * s))))
      = ∫ q : ℝ × ℝ, ρ q * lam (z * Real.exp (-(ε * q.1))) := by
    have hinner : ∀ s : ℝ, (∫ t, ρ (s, t)) * lam (z * Real.exp (-(ε * s)))
        = ∫ t, ρ (s, t) * lam (z * Real.exp (-(ε * s))) := fun s => by
      rw [MeasureTheory.integral_mul_const]
    simp only [hinner]
    rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
    exact (MeasureTheory.integral_prod _ hGint').symm
  rw [hstep, hR]

end Work.FTS.StrongEps.EpsLocalPStar
