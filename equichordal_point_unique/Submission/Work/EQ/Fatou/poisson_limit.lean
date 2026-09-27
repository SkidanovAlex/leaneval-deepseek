import Mathlib
import Submission.Work.EQ.FatouDefs
import Submission.Work.EQ.Fatou.pk_eq_poissonKernel
import Submission.Work.EQ.Fatou.pk_nonneg

/-!
# The Poisson integral reproduces a holomorphic function from its `L¹` boundary values

If `g` is holomorphic on the unit disc, bounded by `M`, and `F` is the `L¹`-limit of the dilates
`θ ↦ g(ρ_k e^{iθ})` with `ρ_k → 1⁻`, then inside the disc `g` is the Poisson integral of `F`:

`g(r e^{iθ}) = (2π)⁻¹ ∫₀^{2π} pk r (θ - φ) F φ dφ`.

The proof uses Mathlib's Poisson integral formula `DiffContOnCl.circleAverage_poissonKernel_smul`
applied to the dilates `z ↦ g(ρ z)`, together with the elementary bound `pk r ψ ≤ (1+r)/(1-r)`
which controls the difference term.
-/

set_option linter.unusedVariables false

namespace Work.EQ.Fatou

open MeasureTheory Filter

/-- Continuity of the angle Poisson kernel for `0 ≤ r < 1`. -/
lemma pk_continuous (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    Continuous fun ψ : ℝ => Work.EQ.pk r ψ := by
  unfold Work.EQ.pk
  apply Continuous.div <;> try fun_prop
  intro ψ
  have h2 : 0 ≤ 2*r*(1 - Real.cos ψ) := mul_nonneg (by linarith) (by linarith [Real.cos_le_one ψ])
  have h1 : 0 < (1-r)^2 := sq_pos_of_ne_zero (by linarith)
  have he : 1 - 2*r*Real.cos ψ + r^2 = (1-r)^2 + 2*r*(1-Real.cos ψ) := by ring
  rw [he]; linarith

/-- The angle Poisson kernel is bounded by `(1+r)/(1-r)` on the unit disc. -/
lemma pk_le_bound (r ψ : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    Work.EQ.pk r ψ ≤ (1+r)/(1-r) := by
  unfold Work.EQ.pk
  have hden : 0 < 1 - 2*r*Real.cos ψ + r^2 := by
    have h2 : 0 ≤ 2*r*(1 - Real.cos ψ) := mul_nonneg (by linarith) (by linarith [Real.cos_le_one ψ])
    have h1 : 0 < (1-r)^2 := sq_pos_of_ne_zero (by linarith)
    have he : 1 - 2*r*Real.cos ψ + r^2 = (1-r)^2 + 2*r*(1-Real.cos ψ) := by ring
    rw [he]; linarith
  rw [div_le_div_iff₀ hden (by linarith)]
  nlinarith [Real.cos_le_one ψ]

/-- The Poisson kernel is an approximate identity: the absolute value of its integral against
an interval-integrable function is bounded by `(1+r)/(1-r)` times the `L¹` norm. -/
theorem pk_integral_bound {r θ : ℝ} (hr : r ∈ Set.Ioo 0 1) {u : ℝ → ℂ}
    (hu : IntervalIntegrable u MeasureTheory.volume (0:ℝ) (2 * Real.pi)) :
    ‖∫ φ in (0:ℝ)..2 * Real.pi, (Work.EQ.pk r (θ - φ) : ℂ) * u φ‖
      ≤ ((1 + r) / (1 - r)) * ∫ φ in (0:ℝ)..2 * Real.pi, ‖u φ‖ := by
  have hr0 : 0 ≤ r := hr.1.le
  have hr1 : r < 1 := hr.2
  have h2π : (0:ℝ) ≤ 2*Real.pi := by positivity
  have h1 : ‖∫ φ in (0:ℝ)..2*Real.pi, (Work.EQ.pk r (θ-φ) : ℂ) * u φ‖
      ≤ ∫ φ in (0:ℝ)..2*Real.pi, ((1+r)/(1-r)) * ‖u φ‖ := by
    refine intervalIntegral.norm_integral_le_of_norm_le h2π ?_ ?_
    · filter_upwards with t ht
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Work.EQ.Fatou.pk_nonneg r (θ - t) hr0 hr1)]
      exact mul_le_mul_of_nonneg_right (pk_le_bound r (θ - t) hr0 hr1) (norm_nonneg _)
    · exact hu.norm.const_mul _
  rw [intervalIntegral.integral_const_mul] at h1
  exact h1

/-- Multiplying an interval-integrable function by the (continuous, bounded) Poisson kernel
preserves interval-integrability. -/
theorem intervalIntegrable_pk_mul {r θ : ℝ} (hr : r ∈ Set.Ioo 0 1) {u : ℝ → ℂ}
    (hu : IntervalIntegrable u MeasureTheory.volume (0:ℝ) (2 * Real.pi)) :
    IntervalIntegrable (fun φ => (Work.EQ.pk r (θ - φ) : ℂ) * u φ) MeasureTheory.volume
      (0:ℝ) (2 * Real.pi) := by
  have hcont : ContinuousOn (fun φ : ℝ => (Work.EQ.pk r (θ - φ) : ℂ)) (Set.uIcc 0 (2*Real.pi)) := by
    apply Continuous.continuousOn
    exact Complex.continuous_ofReal.comp ((pk_continuous r hr.1.le hr.2).comp (by fun_prop))
  exact hu.continuousOn_mul hcont

/-- Continuity in the radial variable: if `ρ k → 1⁻` then `g(ρ k · r · e^{iθ}) → g(r e^{iθ})`. -/
theorem tendsto_discVal_rho {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (Metric.ball 0 1))
    (ρ : ℕ → ℝ) (hρ : Filter.Tendsto ρ Filter.atTop (nhdsWithin 1 (Set.Iio 1)))
    {r : ℝ} (hr : r ∈ Set.Ioo (0:ℝ) 1) (θ : ℝ) :
    Filter.Tendsto (fun k => Work.EQ.discVal g (ρ k * r) θ) Filter.atTop
      (nhds (Work.EQ.discVal g r θ)) := by
  have hr0 : 0 < r := hr.1
  have hr1 : r < 1 := hr.2
  set z : ℂ := (r:ℂ) * Complex.exp ((θ:ℂ)*Complex.I) with hzdef
  have hzn : ‖z‖ = r := by
    rw [hzdef, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr0]
  have hzmem : z ∈ Metric.ball (0:ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right, hzn]; exact hr1
  have hcont : ContinuousAt g z := hg.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds hzmem)
  have hρr : Filter.Tendsto (fun k => ρ k * r) Filter.atTop (nhds r) := by
    have h := (hρ.mono_right nhdsWithin_le_nhds).mul_const r
    simpa using h
  have hseq : Filter.Tendsto (fun k => ((ρ k * r : ℝ) : ℂ) * Complex.exp ((θ:ℂ)*Complex.I))
      Filter.atTop (nhds z) := by
    have h2 := (Complex.continuous_ofReal.tendsto r).comp hρr
    rw [hzdef]
    exact h2.mul tendsto_const_nhds
  have hfin := hcont.tendsto.comp hseq
  simpa [Work.EQ.discVal, Function.comp_def, hzdef] using hfin

theorem poisson_limit {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (Metric.ball 0 1)) {M : ℝ}
    (hM : ∀ z ∈ Metric.ball (0:ℂ) 1, ‖g z‖ ≤ M)
    (ρ : ℕ → ℝ) (hρ : Filter.Tendsto ρ Filter.atTop (nhdsWithin 1 (Set.Iio 1)))
    {F : ℝ → ℂ}
    (hFi : MeasureTheory.Integrable F (MeasureTheory.volume.restrict (Set.Ioc 0 (2 * Real.pi))))
    (hF : Filter.Tendsto (fun k => ∫ θ in (0:ℝ)..2 * Real.pi, ‖Work.EQ.discVal g (ρ k) θ - F θ‖)
      Filter.atTop (nhds 0)) :
    ∀ r ∈ Set.Ioo (0:ℝ) 1, ∀ θ : ℝ,
      Work.EQ.discVal g r θ = (2 * Real.pi)⁻¹ *
        (∫ φ in (0:ℝ)..2 * Real.pi, Work.EQ.pk r (θ - φ) * F φ) := by
  intro r hr θ
  have h2πpos : (0:ℝ) < 2 * Real.pi := by positivity
  have hFi' : IntervalIntegrable F MeasureTheory.volume (0:ℝ) (2 * Real.pi) := by
    rw [intervalIntegrable_iff, MeasureTheory.IntegrableOn, Set.uIoc_of_le (le_of_lt h2πpos)]
    exact hFi
  -- eventually `ρ k ∈ (0,1)`
  have hev : ∀ᶠ k in Filter.atTop, ρ k ∈ Set.Ioo (0:ℝ) 1 := by
    have h1 : ∀ᶠ k in Filter.atTop, ρ k < 1 := hρ.eventually self_mem_nhdsWithin
    have h2 : ∀ᶠ k in Filter.atTop, (0:ℝ) < ρ k :=
      hρ.eventually (nhdsWithin_le_nhds (Ioi_mem_nhds (by norm_num : (0:ℝ) < 1)))
    filter_upwards [h1, h2] with k hk1 hk2
    exact ⟨hk2, hk1⟩
  -- continuity of the dilate of `g`
  have hcont_discVal : ∀ ρ' ∈ Set.Ioo (0:ℝ) 1,
      Continuous (fun φ : ℝ => Work.EQ.discVal g ρ' φ) := by
    intro ρ' hρ'
    have hmap : ∀ φ : ℝ, (ρ':ℂ) * Complex.exp ((φ:ℂ)*Complex.I) ∈ Metric.ball (0:ℂ) 1 := by
      intro φ
      rw [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ'.1]
      exact hρ'.2
    have := hg.continuousOn.comp_continuous
      (by fun_prop : Continuous fun φ : ℝ => (ρ':ℂ) * Complex.exp ((φ:ℂ)*Complex.I)) hmap
    simpa [Work.EQ.discVal, Function.comp_def] using this
  -- the Poisson formula for the dilate `z ↦ g(ρ' z)`
  have hPoisson : ∀ ρ' ∈ Set.Ioo (0:ℝ) 1,
      (2 * Real.pi)⁻¹ • (∫ φ in (0:ℝ)..2 * Real.pi,
          (Work.EQ.pk r (θ - φ) : ℂ) * Work.EQ.discVal g ρ' φ)
        = Work.EQ.discVal g (ρ' * r) θ := by
    intro ρ' hρ'
    have hρ0' : 0 < ρ' := hρ'.1
    have hρ1' : ρ' < 1 := hρ'.2
    have hr1 : r < 1 := hr.2
    set w : ℂ := (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) with hwdef
    have hwn : ‖w‖ = r := by
      rw [hwdef, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hr.1]
    have hwmem : w ∈ Metric.ball (0:ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right, hwn]; exact hr1
    have hGdiff : DifferentiableOn ℂ (fun z : ℂ => g ((ρ':ℂ) * z)) (Metric.ball 0 1) := by
      have h1 : DifferentiableOn ℂ (fun z : ℂ => (ρ':ℂ) * z) (Metric.ball 0 1) := by fun_prop
      refine hg.comp h1 (fun z hz => ?_)
      rw [Metric.mem_ball, dist_zero_right] at hz ⊢
      calc ‖(ρ':ℂ) * z‖ = ρ' * ‖z‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0']
        _ < ρ' * 1 := by gcongr
        _ < 1 := by linarith [hρ1']
    have hGcont : ContinuousOn (fun z : ℂ => g ((ρ':ℂ) * z)) (closure (Metric.ball 0 1)) := by
      rw [closure_ball (0:ℂ) (by norm_num : (1:ℝ) ≠ 0)]
      refine hg.continuousOn.comp ?_ (fun z hz => ?_)
      · fun_prop
      · rw [Metric.mem_closedBall, dist_zero_right] at hz
        rw [Metric.mem_ball, dist_zero_right]
        calc ‖(ρ':ℂ) * z‖ = ρ' * ‖z‖ := by
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0']
          _ ≤ ρ' * 1 := by gcongr
          _ < 1 := by linarith [hρ1']
    have hDCC : DiffContOnCl ℂ (fun z : ℂ => g ((ρ':ℂ) * z)) (Metric.ball 0 1) :=
      ⟨hGdiff, hGcont⟩
    have hP := DiffContOnCl.circleAverage_poissonKernel_smul hDCC hwmem
    rw [Real.circleAverage_def] at hP
    have hint : (∫ s in (0:ℝ)..2*Real.pi,
          (poissonKernel 0 w • (fun z : ℂ => g ((ρ':ℂ)*z))) (circleMap 0 1 s))
        = ∫ s in (0:ℝ)..2*Real.pi, (↑(Work.EQ.pk r (θ - s)) : ℂ) * Work.EQ.discVal g ρ' s := by
      apply intervalIntegral.integral_congr
      intro s hs
      dsimp only
      rw [hwdef]
      rw [show circleMap 0 1 s = Complex.exp ((s:ℂ)*Complex.I) from by simp [circleMap]]
      change poissonKernel 0 (↑r * Complex.exp (↑θ * Complex.I)) (Complex.exp ((s:ℂ) * Complex.I))
          • g (↑ρ' * Complex.exp ((s:ℂ) * Complex.I))
        = ↑(Work.EQ.pk r (θ - s)) * Work.EQ.discVal g ρ' s
      rw [Complex.real_smul, ← Work.EQ.Fatou.pk_eq_poissonKernel r θ s hr1]
      rfl
    rw [hint] at hP
    have hrhs : g ((ρ':ℂ) * w) = Work.EQ.discVal g (ρ' * r) θ := by
      congr 1
      simp only [hwdef]
      push_cast
      ring
    rw [hrhs] at hP
    exact hP
  -- split the integral into the dilate plus the difference
  have hsplit : ∀ᶠ k in Filter.atTop,
      (∫ φ in (0:ℝ)..2 * Real.pi, (Work.EQ.pk r (θ - φ) : ℂ) * F φ)
        = (∫ φ in (0:ℝ)..2 * Real.pi, (Work.EQ.pk r (θ - φ) : ℂ) * Work.EQ.discVal g (ρ k) φ)
          + (∫ φ in (0:ℝ)..2 * Real.pi,
              (Work.EQ.pk r (θ - φ) : ℂ) * (F φ - Work.EQ.discVal g (ρ k) φ)) := by
    filter_upwards [hev] with k hk
    have hId : IntervalIntegrable (Work.EQ.discVal g (ρ k)) MeasureTheory.volume (0:ℝ) (2*Real.pi) :=
      (hcont_discVal (ρ k) hk).intervalIntegrable 0 (2*Real.pi)
    have hIA : IntervalIntegrable
        (fun φ => (Work.EQ.pk r (θ - φ) : ℂ) * Work.EQ.discVal g (ρ k) φ)
        MeasureTheory.volume (0:ℝ) (2*Real.pi) :=
      intervalIntegrable_pk_mul hr hId
    have hIB : IntervalIntegrable
        (fun φ => (Work.EQ.pk r (θ - φ) : ℂ) * (F φ - Work.EQ.discVal g (ρ k) φ))
        MeasureTheory.volume (0:ℝ) (2*Real.pi) :=
      intervalIntegrable_pk_mul hr (hFi'.sub hId)
    rw [← intervalIntegral.integral_add hIA hIB]
    apply intervalIntegral.integral_congr
    intro φ hφ
    ring
  -- assembling: `X = discVal g (ρ k · r) θ + error`
  have hdecomp : ∀ᶠ k in Filter.atTop,
      (2 * Real.pi)⁻¹ • (∫ φ in (0:ℝ)..2 * Real.pi, (Work.EQ.pk r (θ - φ) : ℂ) * F φ)
        = Work.EQ.discVal g (ρ k * r) θ
          + (2 * Real.pi)⁻¹ • (∫ φ in (0:ℝ)..2 * Real.pi,
              (Work.EQ.pk r (θ - φ) : ℂ) * (F φ - Work.EQ.discVal g (ρ k) φ)) := by
    filter_upwards [hev, hsplit] with k hk hsp
    rw [hsp, smul_add, hPoisson (ρ k) hk]
  -- the error term tends to `0`
  have hE0 : Filter.Tendsto (fun k => (2 * Real.pi)⁻¹ • (∫ φ in (0:ℝ)..2 * Real.pi,
      (Work.EQ.pk r (θ - φ) : ℂ) * (F φ - Work.EQ.discVal g (ρ k) φ)))
      Filter.atTop (nhds 0) := by
    have hbnd : ∀ᶠ k in Filter.atTop,
        ‖(2 * Real.pi)⁻¹ • (∫ φ in (0:ℝ)..2 * Real.pi,
            (Work.EQ.pk r (θ - φ) : ℂ) * (F φ - Work.EQ.discVal g (ρ k) φ))‖
          ≤ ((2 * Real.pi)⁻¹ * ((1+r)/(1-r))) *
              (∫ φ in (0:ℝ)..2 * Real.pi, ‖F φ - Work.EQ.discVal g (ρ k) φ‖) := by
      filter_upwards [hev] with k hk
      rw [norm_smul, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ (2*Real.pi)⁻¹)]
      have hId : IntervalIntegrable (Work.EQ.discVal g (ρ k)) MeasureTheory.volume
          (0:ℝ) (2*Real.pi) :=
        (hcont_discVal (ρ k) hk).intervalIntegrable 0 (2*Real.pi)
      have hb := pk_integral_bound (θ := θ) hr (hFi'.sub hId)
      calc (2*Real.pi)⁻¹ * ‖∫ φ in (0:ℝ)..2*Real.pi,
            (Work.EQ.pk r (θ - φ) : ℂ) * (F φ - Work.EQ.discVal g (ρ k) φ)‖
          ≤ (2*Real.pi)⁻¹ * (((1+r)/(1-r)) *
              ∫ φ in (0:ℝ)..2*Real.pi, ‖F φ - Work.EQ.discVal g (ρ k) φ‖) :=
            mul_le_mul_of_nonneg_left hb (by positivity)
        _ = ((2*Real.pi)⁻¹ * ((1+r)/(1-r))) *
              (∫ φ in (0:ℝ)..2*Real.pi, ‖F φ - Work.EQ.discVal g (ρ k) φ‖) := by ring
    have hInt : Filter.Tendsto
        (fun k => ∫ φ in (0:ℝ)..2 * Real.pi, ‖F φ - Work.EQ.discVal g (ρ k) φ‖)
        Filter.atTop (nhds 0) := by
      refine hF.congr' ?_
      filter_upwards with k
      apply intervalIntegral.integral_congr
      intro φ hφ
      simp only [norm_sub_rev]
    refine squeeze_zero_norm' hbnd ?_
    have hlim := hInt.const_mul ((2*Real.pi)⁻¹ * ((1+r)/(1-r)))
    simpa using hlim
  have hd : Filter.Tendsto (fun k => Work.EQ.discVal g (ρ k * r) θ) Filter.atTop
      (nhds (Work.EQ.discVal g r θ)) := tendsto_discVal_rho hg ρ hρ hr θ
  have hbound : ∀ᶠ k in Filter.atTop,
      ‖((2 * Real.pi)⁻¹ • (∫ φ in (0:ℝ)..2 * Real.pi,
          (Work.EQ.pk r (θ - φ) : ℂ) * F φ)) - Work.EQ.discVal g r θ‖
        ≤ ‖(2 * Real.pi)⁻¹ • (∫ φ in (0:ℝ)..2 * Real.pi,
              (Work.EQ.pk r (θ - φ) : ℂ) * (F φ - Work.EQ.discVal g (ρ k) φ))‖
          + ‖Work.EQ.discVal g (ρ k * r) θ - Work.EQ.discVal g r θ‖ := by
    filter_upwards [hdecomp] with k hk
    rw [hk]
    calc ‖(Work.EQ.discVal g (ρ k * r) θ + (2 * Real.pi)⁻¹ • (∫ φ in (0:ℝ)..2 * Real.pi,
            (Work.EQ.pk r (θ - φ) : ℂ) * (F φ - Work.EQ.discVal g (ρ k) φ)))
          - Work.EQ.discVal g r θ‖
        = ‖(2 * Real.pi)⁻¹ • (∫ φ in (0:ℝ)..2 * Real.pi,
              (Work.EQ.pk r (θ - φ) : ℂ) * (F φ - Work.EQ.discVal g (ρ k) φ))
            + (Work.EQ.discVal g (ρ k * r) θ - Work.EQ.discVal g r θ)‖ := by ring_nf
      _ ≤ ‖(2 * Real.pi)⁻¹ • (∫ φ in (0:ℝ)..2 * Real.pi,
              (Work.EQ.pk r (θ - φ) : ℂ) * (F φ - Work.EQ.discVal g (ρ k) φ))‖
            + ‖Work.EQ.discVal g (ρ k * r) θ - Work.EQ.discVal g r θ‖ := norm_add_le _ _
  have hlim2 : Filter.Tendsto (fun k => ‖(2 * Real.pi)⁻¹ • (∫ φ in (0:ℝ)..2 * Real.pi,
          (Work.EQ.pk r (θ - φ) : ℂ) * (F φ - Work.EQ.discVal g (ρ k) φ))‖
        + ‖Work.EQ.discVal g (ρ k * r) θ - Work.EQ.discVal g r θ‖) Filter.atTop (nhds 0) := by
    have ha : Filter.Tendsto (fun k => ‖(2 * Real.pi)⁻¹ • (∫ φ in (0:ℝ)..2 * Real.pi,
          (Work.EQ.pk r (θ - φ) : ℂ) * (F φ - Work.EQ.discVal g (ρ k) φ))‖)
        Filter.atTop (nhds 0) := by simpa using hE0.norm
    have hb : Filter.Tendsto
        (fun k => ‖Work.EQ.discVal g (ρ k * r) θ - Work.EQ.discVal g r θ‖)
        Filter.atTop (nhds 0) := by
      have hconst : Filter.Tendsto (fun _ : ℕ => Work.EQ.discVal g r θ) Filter.atTop
          (nhds (Work.EQ.discVal g r θ)) := tendsto_const_nhds
      have h1 : Filter.Tendsto
          (fun k : ℕ => Work.EQ.discVal g (ρ k * r) θ - Work.EQ.discVal g r θ) Filter.atTop
          (nhds (Work.EQ.discVal g r θ - Work.EQ.discVal g r θ)) := hd.sub hconst
      simpa using h1.norm
    simpa using ha.add hb
  have hle : ‖((2 * Real.pi)⁻¹ • (∫ φ in (0:ℝ)..2 * Real.pi,
      (Work.EQ.pk r (θ - φ) : ℂ) * F φ)) - Work.EQ.discVal g r θ‖ ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim2 hbound
  have heq : (2 * Real.pi)⁻¹ • (∫ φ in (0:ℝ)..2 * Real.pi,
      (Work.EQ.pk r (θ - φ) : ℂ) * F φ) = Work.EQ.discVal g r θ := by
    have hz : ‖((2 * Real.pi)⁻¹ • (∫ φ in (0:ℝ)..2 * Real.pi,
        (Work.EQ.pk r (θ - φ) : ℂ) * F φ)) - Work.EQ.discVal g r θ‖ = 0 :=
      le_antisymm hle (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  exact heq.symm

end Work.EQ.Fatou
