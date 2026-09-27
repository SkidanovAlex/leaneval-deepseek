import Mathlib
import Submission.Work.EQ.FanSep.Defs
import Submission.Work.EQ.fan_base
import Submission.Work.EQ.germC_apply_ne

namespace Work.EQ.FanSep

open Work.EQ Complex Metric Filter
open scoped Topology

noncomputable section

/-- **Local Lipschitz bound at `0`.** A function analytic at `0` and vanishing there satisfies
`‖f u‖ ≤ p ‖u‖` on a small ball.  (Factor `f u = u · dslope f 0 u` via `mul_dslope_eq`; the
`dslope` is analytic, hence continuous, hence locally bounded.) -/
theorem analytic_lipschitz {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (h0 : f 0 = 0) :
    ∃ δ p : ℝ, 0 < δ ∧ 0 < p ∧ ∀ u : ℂ, ‖u‖ < δ → ‖f u‖ ≤ p * ‖u‖ := by
  have hcont : ContinuousAt (dslope f 0) 0 := (Work.EQ.analyticAt_dslope hf).continuousAt
  have hb : ∀ᶠ u in 𝓝 (0 : ℂ), ‖dslope f 0 u‖ ≤ ‖dslope f 0 0‖ + 1 := by
    have hmem : ∀ᶠ u in 𝓝 (0 : ℂ), dslope f 0 u ∈ Metric.ball (dslope f 0 0) 1 :=
      hcont.eventually_mem (Metric.ball_mem_nhds _ one_pos)
    filter_upwards [hmem] with u hu
    rw [Metric.mem_ball, dist_eq_norm] at hu
    have h2 : ‖dslope f 0 u‖ ≤ ‖dslope f 0 u - dslope f 0 0‖ + ‖dslope f 0 0‖ := by
      linarith [norm_sub_norm_le (dslope f 0 u) (dslope f 0 0)]
    linarith
  obtain ⟨δ, hδ0, hδ⟩ := Work.EQ.exists_ball_of_eventually hb
  refine ⟨δ, ‖dslope f 0 0‖ + 1, hδ0, by positivity, fun u hu => ?_⟩
  have hu' : u ∈ Metric.ball (0 : ℂ) δ := by
    rwa [Metric.mem_ball, dist_eq_norm, sub_zero]
  have hb' := hδ u hu'
  rw [← Work.EQ.mul_dslope_eq (f := f) h0, norm_mul]
  calc ‖u‖ * ‖dslope f 0 u‖ ≤ ‖u‖ * (‖dslope f 0 0‖ + 1) :=
        mul_le_mul_of_nonneg_left hb' (norm_nonneg _)
    _ = (‖dslope f 0 0‖ + 1) * ‖u‖ := by ring

/-- **The second coordinate factors through the first.**  Near `0`, off the origin,
`(germC a h u).2 = ((germC a h u).1 - a/2) · h (λ u)`.  This is the algebraic content of the
"semiprojective" coordinate: the ratio `y/(x - a/2)` of a germ point equals `h(λu)`, which
tends to `h 0 = 0`. -/
theorem germC_snd_factor {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u : ℂ, 0 < ‖u‖ → ‖u‖ < δ →
      (germC a h u).2 = ((germC a h u).1 - ((a / 2 : ℝ) : ℂ)) * h ((eqLam a : ℂ) * u) := by
  obtain ⟨hr, han, h0, hderiv, hreal, hFE⟩ := hh
  have hl : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  have hmem0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) r := by simpa using hr
  have hn : AnalyticAt ℂ h 0 := han 0 hmem0
  have hM : AnalyticAt ℂ (fun v : ℂ => h ((eqLam a : ℂ) * v)) 0 := by
    have h1 : AnalyticAt ℂ (fun v : ℂ => (eqLam a : ℂ) * v) 0 :=
      analyticAt_const.mul analyticAt_id
    have h2 : AnalyticAt ℂ h ((eqLam a : ℂ) * 0) := by simpa using hn
    simpa [Function.comp_def] using h2.comp h1
  have hD : AnalyticAt ℂ (fun v : ℂ => h ((eqLam a : ℂ) * v) - h v) 0 := hM.sub hn
  have hDcont : ContinuousAt (gD a h) 0 := (Work.EQ.analyticAt_dslope hD).continuousAt
  have hD0 : gD a h 0 ≠ 0 := by
    have hd0 : HasDerivAt h (-1) 0 := by
      have := hn.differentiableAt.hasDerivAt
      rwa [hderiv] at this
    have hBder : HasDerivAt (fun v : ℂ => h ((eqLam a : ℂ) * v)) (-(eqLam a : ℂ)) 0 := by
      have hder0c : HasDerivAt h (-1) ((eqLam a : ℂ) * 0) := by simpa using hd0
      have hh' := hder0c.comp 0 (hasDerivAt_const_mul ((eqLam a : ℂ)))
      simpa [Function.comp_def] using hh'
    have hDder : HasDerivAt (fun v : ℂ => h ((eqLam a : ℂ) * v) - h v)
        (-(eqLam a : ℂ) - (-1)) 0 := hBder.sub hd0
    have hderivD : deriv (fun v : ℂ => h ((eqLam a : ℂ) * v) - h v) 0 = 1 - (eqLam a : ℂ) := by
      rw [hDder.deriv]; ring
    rw [gD, dslope_same, hderivD, sub_ne_zero]
    intro hc
    have hc' : (1 : ℝ) = eqLam a := by
      have h1 : ((1 : ℝ) : ℂ) = ((eqLam a : ℝ) : ℂ) := by
        rw [Complex.ofReal_one]; exact hc
      exact Complex.ofReal_injective h1
    linarith
  obtain ⟨δ, hδ0, hδne⟩ := Work.EQ.exists_ball_of_eventually (hDcont.eventually_ne hD0)
  refine ⟨δ, hδ0, fun u hupos huδ => ?_⟩
  have hu : u ≠ 0 := by rwa [norm_pos_iff] at hupos
  have hu' : u ∈ Metric.ball (0 : ℂ) δ := by
    rwa [Metric.mem_ball, dist_eq_norm, sub_zero]
  have hDne : gD a h u ≠ 0 := hδne u hu'
  have hzero : (fun v : ℂ => h ((eqLam a : ℂ) * v) - h v) 0 = 0 := by
    simp only [mul_zero, h0, sub_self]
  have hDen : h ((eqLam a : ℂ) * u) - h u ≠ 0 := by
    have hval : h ((eqLam a : ℂ) * u) - h u = u * gD a h u := by
      rw [gD]
      exact (Work.EQ.mul_dslope_eq (f := fun v : ℂ => h ((eqLam a : ℂ) * v) - h v) hzero).symm
    rw [hval]
    exact mul_ne_zero hu hDne
  rw [Work.EQ.germC_apply_ne h0 hu]
  field_simp
  push_cast
  ring

theorem germ_lip {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∃ δ p q : ℝ, 0 < δ ∧ 0 < p ∧ 0 < q ∧ ∀ u : ℂ, ‖u‖ < δ →
      ‖(germC a h u).1 - ((-1 / 2 : ℝ) : ℂ)‖ ≤ p * ‖u‖ ∧
      ‖(germC a h u).2‖ ≤ q * ‖u‖ * ‖(germC a h u).1 - ((a / 2 : ℝ) : ℂ)‖ := by
  have hh' := hh
  obtain ⟨hr, han, h0, hderiv, hreal, hFE⟩ := hh'
  have hl0 : 0 < eqLam a := eqLam_pos' ha0 ha1
  have hl1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  -- analyticity of the first coordinate of the germ
  obtain ⟨ρ, hρ0, hAnC⟩ := Work.EQ.germC_analytic ha0 ha1 hh
  have hAn1 : AnalyticAt ℂ (fun u => (germC a h u).1) 0 := by
    have hmemC : (0 : ℂ) ∈ Metric.ball (0 : ℂ) ρ := by simpa using hρ0
    have hproj : AnalyticAt ℂ (fun p : ℂ × ℂ => p.1) (germC a h 0) :=
      (ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt _
    exact hproj.comp (hAnC 0 hmemC)
  have hf_an : AnalyticAt ℂ (fun u => (germC a h u).1 - ((-1 / 2 : ℝ) : ℂ)) 0 :=
    hAn1.sub analyticAt_const
  have hf0 : (fun u => (germC a h u).1 - ((-1 / 2 : ℝ) : ℂ)) 0 = 0 := by
    show (germC a h 0).1 - ((-1 / 2 : ℝ) : ℂ) = 0
    rw [Work.EQ.germC_value ha0 ha1 hh]
    simp
  obtain ⟨δ₁, p, hδ₁, hp, hb1⟩ := analytic_lipschitz hf_an hf0
  -- analyticity of `h ∘ (λ·)`
  have hAnM : AnalyticAt ℂ (fun v : ℂ => h ((eqLam a : ℂ) * v)) 0 := by
    have hmem0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) r := by simpa using hr
    have hn : AnalyticAt ℂ h 0 := han 0 hmem0
    have h1 : AnalyticAt ℂ (fun v : ℂ => (eqLam a : ℂ) * v) 0 :=
      analyticAt_const.mul analyticAt_id
    have h2 : AnalyticAt ℂ h ((eqLam a : ℂ) * 0) := by simpa using hn
    simpa [Function.comp_def] using h2.comp h1
  have hM0 : (fun v : ℂ => h ((eqLam a : ℂ) * v)) 0 = 0 := by
    simp only [mul_zero, h0]
  obtain ⟨δ₂, q, hδ₂, hq, hb2⟩ := analytic_lipschitz hAnM hM0
  obtain ⟨δ₃, hδ₃, hfac⟩ := germC_snd_factor ha0 ha1 hh
  refine ⟨min δ₁ (min δ₂ δ₃), p, q, lt_min hδ₁ (lt_min hδ₂ hδ₃), hp, hq, ?_⟩
  intro u hu
  have hu1 : ‖u‖ < δ₁ := lt_of_lt_of_le hu (min_le_left _ _)
  have hu2 : ‖u‖ < δ₂ := lt_of_lt_of_le hu (le_trans (min_le_right _ _) (min_le_left _ _))
  have hu3 : ‖u‖ < δ₃ := lt_of_lt_of_le hu (le_trans (min_le_right _ _) (min_le_right _ _))
  refine ⟨hb1 u hu1, ?_⟩
  rcases eq_or_ne u 0 with rfl | hu0
  · rw [Work.EQ.germC_value ha0 ha1 hh]
    simp
  · have hupos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
    have hA : 0 ≤ ‖(germC a h u).1 - ((a / 2 : ℝ) : ℂ)‖ := norm_nonneg _
    have hstep : ‖h ((eqLam a : ℂ) * u)‖ ≤ q * ‖u‖ := hb2 u hu2
    rw [hfac u hupos hu3, norm_mul]
    calc ‖(germC a h u).1 - ((a / 2 : ℝ) : ℂ)‖ * ‖h ((eqLam a : ℂ) * u)‖
        ≤ ‖(germC a h u).1 - ((a / 2 : ℝ) : ℂ)‖ * (q * ‖u‖) :=
          mul_le_mul_of_nonneg_left hstep hA
      _ = q * ‖u‖ * ‖(germC a h u).1 - ((a / 2 : ℝ) : ℂ)‖ := by ring

end

end Work.EQ.FanSep
