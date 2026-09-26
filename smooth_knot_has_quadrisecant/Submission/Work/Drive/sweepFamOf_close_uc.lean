import Mathlib
import Submission.Work.Drive.sweepFamOf
import Submission.Work.Drive.sweepFamOf_close

/-!
# Uniform closeness of the double blur on a compact sweep window

`Work.Drive.sweepFamOf_close` bounds the double blur of a loop family `Γ` by `M δ₁ + N δ₂`
*when a Lipschitz constant `N` in the sweep parameter is known for all `s`*.  Here `Γ` is merely
jointly continuous and `period`-periodic in the loop parameter; on a compact sweep window
`σ ∈ [a,b] ⊂ (0,1)` the sweep-parameter continuity is nevertheless *uniform in the loop parameter*,
because `Γ` is periodic, hence determined by its restriction to the compact fundamental domain
`[a,b] × [0,period]`.  Combining the two estimates gives the uniform statement
`Work.Drive.sweepFamOf_close_uc`.
-/

noncomputable section
namespace Work.Drive

open MeasureTheory
open scoped Real Topology intervalIntegral
open LeanEval.KnotTheory.Quadrisecant

/-- **A bump average is bounded by `C` as soon as the bound holds on the integration interval.**
This is `Work.Drive.norm_bumpAvg_le` with the pointwise estimate required only on `[-1,1]`. -/
lemma norm_bumpAvg_le_Icc {g : ℝ → Space} (hg : Continuous g) {C : ℝ}
    (hC : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ‖g u‖ ≤ C) :
    ‖∫ u in (-1 : ℝ)..1, sweepBump u • g u‖ ≤ C := by
  refine (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (-1 : ℝ) ≤ 1)).trans ?_
  have h1 : IntervalIntegrable (fun u : ℝ => ‖sweepBump u • g u‖) volume (-1 : ℝ) 1 :=
    ((sweepBump_continuous.smul hg).norm).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun u : ℝ => sweepBump u * C) volume (-1 : ℝ) 1 :=
    (sweepBump_continuous.mul continuous_const).intervalIntegrable _ _
  refine (intervalIntegral.integral_mono_on (by norm_num : (-1 : ℝ) ≤ 1) h1 h2 ?_).trans ?_
  · intro u hu
    rw [norm_smul, Real.norm_of_nonneg (sweepBump_nonneg u)]
    exact mul_le_mul_of_nonneg_left (hC u hu) (sweepBump_nonneg u)
  · rw [intervalIntegral.integral_mul_const, integral_sweepBump, one_mul]

/-- **Every real number reduces to the fundamental domain of a positive period**, modulo an integer
multiple of the period: `t = t₀ + n * period` with `t₀ ∈ [0, period]`. -/
lemma exists_period_reduce (t : ℝ) :
    ∃ t₀ ∈ Set.Icc (0 : ℝ) period, ∃ n : ℤ, t = t₀ + (n : ℝ) * period := by
  have hp : 0 < period := period_pos
  have hpne : period ≠ 0 := ne_of_gt hp
  refine ⟨Int.fract (t / period) * period, ⟨?_, ?_⟩, ⌊t / period⌋, ?_⟩
  · exact mul_nonneg (Int.fract_nonneg _) hp.le
  · calc Int.fract (t / period) * period ≤ 1 * period :=
          mul_le_mul_of_nonneg_right (Int.fract_lt_one _).le hp.le
      _ = period := one_mul _
  · have h := congrArg (fun x : ℝ => x * period) (Int.fract_add_floor (t / period))
    rw [add_mul, div_mul_cancel₀ t hpne] at h
    simpa using h.symm

theorem sweepFamOf_close_uc {Γ : ℝ → ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hΓ : Continuous (fun p : ℝ × ℝ => Γ p.1 p.2))
    (hper : ∀ s t : ℝ, Γ s (t + LeanEval.KnotTheory.Quadrisecant.period) = Γ s t)
    {M : ℝ} (hMnn : 0 ≤ M)
    (hM : ∀ s t₁ t₂ : ℝ, ‖Γ s t₁ - Γ s t₂‖ ≤ M * |t₂ - t₁|)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ L : ℝ, 0 < L ∧ ∀ δ₁ δ₂ : ℝ, 0 ≤ δ₁ → δ₁ ≤ L → 0 ≤ δ₂ → δ₂ ≤ L →
      ∀ σ ∈ Set.Icc a b, ∀ t : ℝ,
        ‖Work.Drive.sweepFamOf Γ δ₁ δ₂ σ t - Γ σ t‖ ≤ ε := by
  -- The compact window in the sweep parameter, and uniform continuity of `Γ` on it.
  have hK : IsCompact (Set.Icc (a / 2) ((1 + b) / 2) ×ˢ Set.Icc (0 : ℝ) period) :=
    isCompact_Icc.prod isCompact_Icc
  have huc : UniformContinuousOn (fun p : ℝ × ℝ => Γ p.1 p.2)
      (Set.Icc (a / 2) ((1 + b) / 2) ×ˢ Set.Icc (0 : ℝ) period) :=
    hK.uniformContinuousOn_of_continuous hΓ.continuousOn
  obtain ⟨η, hηpos, hη⟩ := (Metric.uniformContinuousOn_iff.mp huc) (ε / 2) (by linarith)
  refine ⟨min (min (min (a / 2) ((1 - b) / 2)) (η / 2)) (ε / (2 * (M + 1))), ?_, ?_⟩
  · exact lt_min (lt_min (lt_min (by linarith) (by linarith)) (by linarith))
      (div_pos hε (by linarith))
  intro δ₁ δ₂ hδ₁0 hδ₁L hδ₂0 hδ₂L σ hσ t
  -- bounds extracted from the threshold
  have hδ₂_a : δ₂ ≤ a / 2 :=
    hδ₂L.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hδ₂_b : δ₂ ≤ (1 - b) / 2 :=
    hδ₂L.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hδ₂_η : δ₂ ≤ η / 2 := hδ₂L.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδ₁_e : δ₁ ≤ ε / (2 * (M + 1)) := hδ₁L.trans (min_le_right _ _)
  obtain ⟨hσa, hσb⟩ := Set.mem_Icc.mp hσ
  have hσwin : σ ∈ Set.Icc (a / 2) ((1 + b) / 2) :=
    Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  -- uniform continuity in the sweep parameter, uniform in the loop parameter (periodicity!)
  have hunif : ∀ s' : ℝ, s' ∈ Set.Icc (a / 2) ((1 + b) / 2) → |s' - σ| < η →
      ∀ t₀ ∈ Set.Icc (0 : ℝ) period, ‖Γ s' t₀ - Γ σ t₀‖ ≤ ε / 2 := by
    intro s' hs' hdist t₀ ht₀
    have hx : (s', t₀) ∈ Set.Icc (a / 2) ((1 + b) / 2) ×ˢ Set.Icc (0 : ℝ) period := ⟨hs', ht₀⟩
    have hy : (σ, t₀) ∈ Set.Icc (a / 2) ((1 + b) / 2) ×ˢ Set.Icc (0 : ℝ) period := ⟨hσwin, ht₀⟩
    have hd : dist (s', t₀) (σ, t₀) < η := by
      have h1 : dist (s', t₀) (σ, t₀) = |s' - σ| := by
        rw [Prod.dist_eq, dist_self, Real.dist_eq, max_eq_left (abs_nonneg _)]
      rw [h1]; exact hdist
    have h := hη (s', t₀) hx (σ, t₀) hy hd
    have h' : ‖Γ s' t₀ - Γ σ t₀‖ < ε / 2 := by
      have h2 : dist (Γ s' t₀) (Γ σ t₀) < ε / 2 := h
      rwa [dist_eq_norm] at h2
    exact h'.le
  -- periodicity: reduce the loop parameter to the fundamental domain
  obtain ⟨t₀, ht₀, n, htn⟩ := exists_period_reduce t
  have hper_s : ∀ s : ℝ, Function.Periodic (fun τ : ℝ => Γ s τ) period := fun s τ => hper s τ
  have hred : ∀ s : ℝ, Γ s t = Γ s t₀ := by
    intro s
    rw [htn]
    exact (hper_s s).int_mul n t₀
  -- The outer (sweep-parameter) estimate at scale `ε/2`.
  have hQcont : Continuous (fun v : ℝ => Γ (σ - δ₂ * v) t) :=
    hΓ.comp ((continuous_const.sub (continuous_const.mul continuous_id)).prodMk continuous_const)
  have hout : ‖(∫ v in (-1 : ℝ)..1, sweepBump v • Γ (σ - δ₂ * v) t) - Γ σ t‖ ≤ ε / 2 := by
    have hcont1 : Continuous (fun v : ℝ => sweepBump v • Γ (σ - δ₂ * v) t) :=
      sweepBump_continuous.smul hQcont
    have hcont2 : Continuous (fun v : ℝ => sweepBump v • Γ σ t) :=
      sweepBump_continuous.smul continuous_const
    have hconst : (∫ v in (-1 : ℝ)..1, sweepBump v • Γ σ t) = Γ σ t := by
      rw [intervalIntegral.integral_smul_const, integral_sweepBump, one_smul]
    have hdiff : (∫ v in (-1 : ℝ)..1, sweepBump v • Γ (σ - δ₂ * v) t) - Γ σ t
        = ∫ v in (-1 : ℝ)..1, sweepBump v • (Γ (σ - δ₂ * v) t - Γ σ t) := by
      nth_rewrite 1 [← hconst]
      rw [← intervalIntegral.integral_sub (hcont1.intervalIntegrable _ _)
        (hcont2.intervalIntegrable _ _)]
      refine intervalIntegral.integral_congr (fun v _ => ?_)
      rw [smul_sub]
    rw [hdiff]
    refine norm_bumpAvg_le_Icc (hQcont.sub continuous_const) (fun v hv => ?_)
    have hvabs : |δ₂ * v| ≤ δ₂ := by
      rw [abs_mul, abs_of_nonneg hδ₂0]
      calc δ₂ * |v| ≤ δ₂ * 1 := mul_le_mul_of_nonneg_left (abs_le.mpr hv) hδ₂0
        _ = δ₂ := mul_one _
    have hsw : σ - δ₂ * v ∈ Set.Icc (a / 2) ((1 + b) / 2) := by
      refine Set.mem_Icc.mpr ⟨?_, ?_⟩
      · nlinarith [hσa, hδ₂_a, hδ₂0, hv.2]
      · nlinarith [hσb, hδ₂_b, hδ₂0, hv.1]
    have hdist : |(σ - δ₂ * v) - σ| < η := by
      rw [show (σ - δ₂ * v) - σ = -(δ₂ * v) by ring, abs_neg]
      exact lt_of_le_of_lt hvabs (by linarith)
    have h := hunif (σ - δ₂ * v) hsw hdist t₀ ht₀
    rw [← hred (σ - δ₂ * v), ← hred σ] at h
    exact h
  -- The inner (loop-parameter) estimate: global in the sweep parameter, using `M`.
  have hinner : ∀ σ' τ : ℝ, ‖(∫ u in (-1 : ℝ)..1, sweepBump u • Γ σ' (τ - δ₁ * u)) - Γ σ' τ‖
      ≤ M * δ₁ := by
    intro σ' τ
    have hf : Continuous (fun τ' : ℝ => Γ σ' τ') :=
      hΓ.comp (continuous_const.prodMk continuous_id)
    have hbd : ∀ x h : ℝ, |h| ≤ δ₁ → ‖Γ σ' (x + h) - Γ σ' x‖ ≤ M * δ₁ := by
      intro x h hh
      have h1 : ‖Γ σ' (x + h) - Γ σ' x‖ ≤ M * |x - (x + h)| := hM σ' (x + h) x
      rw [show x - (x + h) = -h by ring, abs_neg] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left hh hMnn)
    exact bump_blur_close (f := fun τ' : ℝ => Γ σ' τ') (ε := M * δ₁) (δ := δ₁) (δ' := δ₁)
      hf (mul_nonneg hMnn hδ₁0) hbd (by rw [abs_of_nonneg hδ₁0]) τ
  have hinner_cont : Continuous
      (fun v : ℝ => ∫ u in (-1 : ℝ)..1, sweepBump u • Γ (σ - δ₂ * v) (t - δ₁ * u)) := by
    have hf : Continuous (fun p : ℝ × ℝ => sweepBump p.2 • Γ (σ - δ₂ * p.1) (t - δ₁ * p.2)) := by
      refine (sweepBump_continuous.comp continuous_snd).smul ?_
      exact hΓ.comp ((continuous_const.sub (continuous_const.mul continuous_fst)).prodMk
        (continuous_const.sub (continuous_const.mul continuous_snd)))
    have h := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume) (f := fun v u : ℝ => sweepBump u • Γ (σ - δ₂ * v) (t - δ₁ * u)) hf (-1) 1
    simpa using h
  have hAB : ‖sweepFamOf Γ δ₁ δ₂ σ t - (∫ v in (-1 : ℝ)..1, sweepBump v • Γ (σ - δ₂ * v) t)‖
      ≤ M * δ₁ := by
    have hInt1 : IntervalIntegrable
        (fun v : ℝ => sweepBump v •
          (∫ u in (-1 : ℝ)..1, sweepBump u • Γ (σ - δ₂ * v) (t - δ₁ * u)))
        volume (-1) 1 := (sweepBump_continuous.smul hinner_cont).intervalIntegrable _ _
    have hInt2 : IntervalIntegrable (fun v : ℝ => sweepBump v • Γ (σ - δ₂ * v) t) volume (-1) 1 :=
      (sweepBump_continuous.smul hQcont).intervalIntegrable _ _
    have hdiff : sweepFamOf Γ δ₁ δ₂ σ t - (∫ v in (-1 : ℝ)..1, sweepBump v • Γ (σ - δ₂ * v) t)
        = ∫ v in (-1 : ℝ)..1, sweepBump v •
            ((∫ u in (-1 : ℝ)..1, sweepBump u • Γ (σ - δ₂ * v) (t - δ₁ * u))
              - Γ (σ - δ₂ * v) t) := by
      unfold sweepFamOf
      rw [← intervalIntegral.integral_sub hInt1 hInt2]
      refine intervalIntegral.integral_congr (fun v _ => ?_)
      rw [smul_sub]
    rw [hdiff]
    exact norm_bumpAvg_le (hinner_cont.sub hQcont) (fun v => hinner (σ - δ₂ * v) t)
  -- `M δ₁ ≤ ε/2`
  have hMδ₁ : M * δ₁ ≤ ε / 2 := by
    have hden : 0 < 2 * (M + 1) := by linarith
    have h : δ₁ * (2 * (M + 1)) ≤ ε := by
      calc δ₁ * (2 * (M + 1)) ≤ (ε / (2 * (M + 1))) * (2 * (M + 1)) :=
            mul_le_mul_of_nonneg_right hδ₁_e hden.le
        _ = ε := div_mul_cancel₀ ε (ne_of_gt hden)
    nlinarith [h, hMnn, hδ₁0]
  -- combine
  have hsplit : sweepFamOf Γ δ₁ δ₂ σ t - Γ σ t
      = (sweepFamOf Γ δ₁ δ₂ σ t - (∫ v in (-1 : ℝ)..1, sweepBump v • Γ (σ - δ₂ * v) t))
        + ((∫ v in (-1 : ℝ)..1, sweepBump v • Γ (σ - δ₂ * v) t) - Γ σ t) :=
    (sub_add_sub_cancel _ _ _).symm
  rw [hsplit]
  calc ‖(sweepFamOf Γ δ₁ δ₂ σ t - (∫ v in (-1 : ℝ)..1, sweepBump v • Γ (σ - δ₂ * v) t))
        + ((∫ v in (-1 : ℝ)..1, sweepBump v • Γ (σ - δ₂ * v) t) - Γ σ t)‖
      ≤ ‖sweepFamOf Γ δ₁ δ₂ σ t - (∫ v in (-1 : ℝ)..1, sweepBump v • Γ (σ - δ₂ * v) t)‖
        + ‖(∫ v in (-1 : ℝ)..1, sweepBump v • Γ (σ - δ₂ * v) t) - Γ σ t‖ := norm_add_le _ _
    _ ≤ M * δ₁ + ε / 2 := add_le_add hAB hout
    _ ≤ ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

end Work.Drive
