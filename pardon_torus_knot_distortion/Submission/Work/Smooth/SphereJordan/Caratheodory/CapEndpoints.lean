import Submission.Work.Smooth.SphereJordan.Caratheodory.CapEstimate

/-!
# Endpoints of the cap arc: existence of the two limiting points

For a holomorphic `f` on the unit disc, the image under `f` of the cap arc
`τ ↦ capPt s τ = 1 - s * exp(τ * I)` (`τ ∈ (-arccos (s/2), arccos (s/2))`) has two endpoints:
the limits of `f (capPt s τ)` as `τ → ±arccos (s/2)`, and their distance is at most the length
`capLen f s` of the image arc.

This is the first half of the Garnett–Marshall boundary-continuity argument (see `NOTES.md`).
-/

noncomputable section
open Set Metric Filter MeasureTheory
open scoped Topology ENNReal

namespace Work.Smooth.SphereJordan.Caratheodory

/-- The arc `capPt s (-α(s), α(s))` lies in the unit disc. -/
lemma capPt_mem_ball_of_mem_Ioo {s : ℝ} (hs : 0 < s) (hs2 : s < 2) {u : ℝ}
    (hu : u ∈ Set.Ioo (-(capAlpha s)) (capAlpha s)) : capPt s u ∈ Metric.ball (0 : ℂ) 1 := by
  rw [capPt_mem_ball_iff hs hs2]
  rw [Set.mem_Ioo] at hu
  have hαπ : capAlpha s < Real.pi := capAlpha_lt_pi hs
  have hcos : Real.cos (capAlpha s) = s / 2 := cos_capAlpha hs hs2
  by_cases h : 0 ≤ u
  · have h1 : Real.cos (capAlpha s) < Real.cos u :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (x := u) (y := capAlpha s) h hαπ.le hu.2
    rw [hcos] at h1; linarith
  · push_neg at h
    have h1 : Real.cos (capAlpha s) < Real.cos (-u) :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (x := -u) (y := capAlpha s) (by linarith) hαπ.le
        (by linarith)
    rw [hcos, Real.cos_neg] at h1
    linarith

/-- The derivative of the parametrised curve `u ↦ f (capPt s u)`. -/
def capDeriv (f : ℂ → ℂ) (s u : ℝ) : ℂ :=
  deriv f (capPt s u) * (-(Complex.I * (s : ℂ) * Complex.exp ((u : ℂ) * Complex.I)))

lemma norm_capDeriv {f : ℂ → ℂ} {s u : ℝ} (hs : 0 < s) :
    ‖capDeriv f s u‖ = s * ‖deriv f (capPt s u)‖ := by
  rw [capDeriv, norm_mul, norm_neg, norm_mul, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  ring

lemma hasDerivAt_comp_capPt {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.ball (0 : ℂ) 1))
    {s u : ℝ} (hu : capPt s u ∈ Metric.ball (0 : ℂ) 1) :
    HasDerivAt (fun v => f (capPt s v)) (capDeriv f s u) u := by
  have h1 : HasDerivAt f (deriv f (capPt s u)) (capPt s u) :=
    (hf.differentiableOn.differentiableAt (isOpen_ball.mem_nhds hu)).hasDerivAt
  have h2 := h1.comp u (hasDerivAt_capPt s u)
  have h4 : (deriv f (capPt s u) * -(Complex.I * (s : ℂ) * Complex.exp ((u : ℂ) * Complex.I)))
      = capDeriv f s u := by
    rw [capDeriv]
  rw [h4] at h2
  exact h2


/-- The integral of the speed over the whole arc is the (real part of the) arc length. -/
lemma integral_arc_eq (f : ℂ → ℂ) {s : ℝ} (hs : 0 < s) (hs2 : s < 2) :
    ∫ u in (-(capAlpha s))..(capAlpha s), s * ‖deriv f (capPt s u)‖ = (capLen f s).toReal := by
  rw [intervalIntegral.integral_of_le (by linarith [capAlpha_pos hs2])]
  rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall
      (fun u => by positivity)) (by
        exact (measurable_const.mul
          (((measurable_deriv f).comp (continuous_capPt s).measurable).norm)).aestronglyMeasurable)]
  congr 1
  exact setLIntegral_congr (MeasureTheory.Ioo_ae_eq_Ioc (a := -(capAlpha s))
    (b := capAlpha s)).symm


/-- The basic estimate for the ends of the arc: on a sub-interval the image is bounded by the
integral of the speed. -/
lemma norm_sub_le_integral_capPt {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.ball (0 : ℂ) 1))
    {s : ℝ} (hs : 0 < s) (hs2 : s < 2) {τ τ' : ℝ}
    (hτ : -(capAlpha s) < τ) (hle : τ ≤ τ') (hτ' : τ' < capAlpha s) :
    ‖f (capPt s τ') - f (capPt s τ)‖ ≤ ∫ u in τ..τ', s * ‖deriv f (capPt s u)‖ := by
  have hmem : ∀ u ∈ Set.uIcc τ τ', u ∈ Set.Ioo (-(capAlpha s)) (capAlpha s) := by
    intro u hu
    rw [Set.uIcc_of_le hle] at hu
    exact ⟨by linarith [hu.1, hτ], by linarith [hu.2, hτ']⟩
  have hbase : ContinuousOn (fun u => f (capPt s u)) (Set.Icc τ τ') := by
    rw [← Set.uIcc_of_le hle]
    exact (hf.continuousOn).comp (continuous_capPt s).continuousOn fun u hu =>
      capPt_mem_ball_of_mem_Ioo hs hs2 (hmem u hu)
  have hderivF : ∀ u ∈ Set.Ioo τ τ', HasDerivAt (fun v => f (capPt s v)) (capDeriv f s u) u := by
    intro u hu
    exact hasDerivAt_comp_capPt hf
      (capPt_mem_ball_of_mem_Ioo hs hs2 ⟨by linarith [hu.1, hτ], by linarith [hu.2, hτ']⟩)
  have hcontD : ContinuousOn (capDeriv f s) (Set.uIcc τ τ') := by
    have h1 : ContinuousOn (fun u => deriv f (capPt s u)) (Set.uIcc τ τ') :=
      (hf.deriv.continuousOn).comp (continuous_capPt s).continuousOn
        (fun u hu => capPt_mem_ball_of_mem_Ioo hs hs2 (hmem u hu))
    have h2 : Continuous fun u : ℝ =>
        -(Complex.I * (s : ℂ) * Complex.exp ((u : ℂ) * Complex.I)) := by fun_prop
    have h3 := h1.mul h2.continuousOn
    have h4 : ((fun u : ℝ => deriv f (capPt s u)) *
        fun u : ℝ => -(Complex.I * (s : ℂ) * Complex.exp ((u : ℂ) * Complex.I))) = capDeriv f s := by
      funext u; rw [Pi.mul_apply]; rfl
    rwa [h4] at h3
  have hint : IntervalIntegrable (capDeriv f s) volume τ τ' := hcontD.intervalIntegrable
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle hbase hderivF hint
  rw [← hftc]
  refine le_trans (intervalIntegral.norm_integral_le_integral_norm hle) ?_
  exact le_of_eq (intervalIntegral.integral_congr fun u _ => norm_capDeriv hs)


/-- A real interval integral is bounded by the `toReal` of the corresponding `lintegral`. -/
lemma integral_le_lintegral_toReal {h : ℝ → ℝ} (hh : ∀ u, 0 ≤ h u) (hm : Measurable h)
    {a b : ℝ} (hab : a ≤ b)
    (hfin : (∫⁻ u in Set.Ioo a b, ENNReal.ofReal (h u)) ≠ ⊤) :
    ∫ u in a..b, h u ≤ (∫⁻ u in Set.Ioo a b, ENNReal.ofReal (h u)).toReal := by
  rw [intervalIntegral.integral_of_le hab]
  rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hh)
    hm.aestronglyMeasurable]
  refine ENNReal.toReal_mono hfin ?_
  exact le_of_eq (setLIntegral_congr (MeasureTheory.Ioo_ae_eq_Ioc (a := a) (b := b))).symm

/-- The left tail of the length integral tends to zero. -/
lemma tendsto_tail_left (f : ℂ → ℂ) {s : ℝ} (hs : 0 < s) (hs2 : s < 2) (hfin : capLen f s < ⊤) :
    Tendsto (fun δ : ℝ => ∫⁻ u in Set.Ioo (-(capAlpha s)) (-(capAlpha s) + δ),
        (Set.Ioo (-(capAlpha s)) (capAlpha s)).indicator
          (fun u => ENNReal.ofReal (s * ‖deriv f (capPt s u)‖)) u)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hg : (∫⁻ u, (Set.Ioo (-(capAlpha s)) (capAlpha s)).indicator
      (fun u => ENNReal.ofReal (s * ‖deriv f (capPt s u)‖)) u) = capLen f s := by
    rw [lintegral_indicator measurableSet_Ioo]; rfl
  refine tendsto_setLIntegral_zero ?_ ?_
  · rw [hg]; exact ne_of_lt hfin
  · have h : ∀ δ : ℝ, volume (Set.Ioo (-(capAlpha s)) (-(capAlpha s) + δ)) = ENNReal.ofReal δ := by
      intro δ
      rw [Real.volume_Ioo]
      norm_num
    rw [show (volume ∘ fun δ : ℝ => Set.Ioo (-(capAlpha s)) (-(capAlpha s) + δ))
        = fun δ => ENNReal.ofReal δ from by funext δ; exact h δ]
    simpa using (ENNReal.continuous_ofReal.tendsto 0).mono_left
      (nhdsWithin_le_nhds : 𝓝[Set.Ioi (0:ℝ)] (0:ℝ) ≤ 𝓝 (0:ℝ))

/-- The right tail of the length integral tends to zero. -/
lemma tendsto_tail_right (f : ℂ → ℂ) {s : ℝ} (hs : 0 < s) (hs2 : s < 2) (hfin : capLen f s < ⊤) :
    Tendsto (fun δ : ℝ => ∫⁻ u in Set.Ioo ((capAlpha s) - δ) (capAlpha s),
        (Set.Ioo (-(capAlpha s)) (capAlpha s)).indicator
          (fun u => ENNReal.ofReal (s * ‖deriv f (capPt s u)‖)) u)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hg : (∫⁻ u, (Set.Ioo (-(capAlpha s)) (capAlpha s)).indicator
      (fun u => ENNReal.ofReal (s * ‖deriv f (capPt s u)‖)) u) = capLen f s := by
    rw [lintegral_indicator measurableSet_Ioo]; rfl
  refine tendsto_setLIntegral_zero ?_ ?_
  · rw [hg]; exact ne_of_lt hfin
  · have h : ∀ δ : ℝ, volume (Set.Ioo ((capAlpha s) - δ) (capAlpha s)) = ENNReal.ofReal δ := by
      intro δ
      rw [Real.volume_Ioo]
      norm_num
    rw [show (volume ∘ fun δ : ℝ => Set.Ioo ((capAlpha s) - δ) (capAlpha s))
        = fun δ => ENNReal.ofReal δ from by funext δ; exact h δ]
    simpa using (ENNReal.continuous_ofReal.tendsto 0).mono_left
      (nhdsWithin_le_nhds : 𝓝[Set.Ioi (0:ℝ)] (0:ℝ) ≤ 𝓝 (0:ℝ))


/-- The indicator of the arc has `lintegral` equal to `capLen`. -/
lemma lintegral_indicator_capLen (f : ℂ → ℂ) (s : ℝ) :
    (∫⁻ u, (Set.Ioo (-(capAlpha s)) (capAlpha s)).indicator
      (fun u => ENNReal.ofReal (s * ‖deriv f (capPt s u)‖)) u) = capLen f s := by
  rw [lintegral_indicator measurableSet_Ioo]; rfl

/-- The left end of the arc converges. -/
lemma exists_tendsto_capPt_left {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.ball (0 : ℂ) 1))
    {s : ℝ} (hs : 0 < s) (hs2 : s < 2) (hfin : capLen f s < ⊤) :
    ∃ a : ℂ, Tendsto (fun τ => f (capPt s τ)) (𝓝[>] (-(capAlpha s))) (𝓝 a) := by
  have hα0 : 0 < capAlpha s := capAlpha_pos hs2
  have htail := tendsto_tail_left f hs hs2 hfin
  have hmeas : Measurable (fun u : ℝ => s * ‖deriv f (capPt s u)‖) :=
    measurable_const.mul (((measurable_deriv f).comp (continuous_capPt s).measurable).norm)
  have hm : ∀ τ τ' : ℝ, -(capAlpha s) < τ → τ ≤ τ' → τ' < capAlpha s →
      (∫⁻ u in Set.Ioo τ τ', ENNReal.ofReal (s * ‖deriv f (capPt s u)‖)) ≠ ⊤ := by
    intro τ τ' h1 _ h2
    refine ne_of_lt (lt_of_le_of_lt ?_ hfin)
    rw [← lintegral_indicator_capLen f s]
    have hsub : Set.Ioo τ τ' ⊆ Set.Ioo (-(capAlpha s)) (capAlpha s) := by
      intro u hu
      rw [Set.mem_Ioo] at hu ⊢
      exact ⟨by linarith [hu.1, h1], by linarith [hu.2, h2]⟩
    calc (∫⁻ u in Set.Ioo τ τ', ENNReal.ofReal (s * ‖deriv f (capPt s u)‖))
        = ∫⁻ u in Set.Ioo τ τ', (Set.Ioo (-(capAlpha s)) (capAlpha s)).indicator
            (fun u => ENNReal.ofReal (s * ‖deriv f (capPt s u)‖)) u := by
          exact setLIntegral_congr_fun measurableSet_Ioo (fun u hu =>
            (Set.indicator_of_mem (hsub hu)
              (fun u => ENNReal.ofReal (s * ‖deriv f (capPt s u)‖))).symm)
      _ ≤ ∫⁻ u, (Set.Ioo (-(capAlpha s)) (capAlpha s)).indicator
            (fun u => ENNReal.ofReal (s * ‖deriv f (capPt s u)‖)) u :=
          setLIntegral_le_lintegral _ _
  have hcau : Cauchy (map (fun τ => f (capPt s τ)) (𝓝[>] (-(capAlpha s)))) := by
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, ?_⟩
    intro ε hε
    have hev1 : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
        (∫⁻ u in Set.Ioo (-(capAlpha s)) (-(capAlpha s) + δ),
          (Set.Ioo (-(capAlpha s)) (capAlpha s)).indicator
            (fun u => ENNReal.ofReal (s * ‖deriv f (capPt s u)‖)) u)
          < ENNReal.ofReal (ε / 2) :=
      htail.eventually (IsOpen.mem_nhds isOpen_Iio (ENNReal.ofReal_pos.mpr (by linarith)))
    have hev2 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (0 : ℝ) < δ := self_mem_nhdsWithin
    have hev3 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < 2 * capAlpha s :=
      (eventually_lt_nhds (by linarith [hα0] : (0:ℝ) < 2 * capAlpha s)).filter_mono
        (nhdsWithin_le_nhds : 𝓝[Set.Ioi (0:ℝ)] (0:ℝ) ≤ 𝓝 (0:ℝ))
    obtain ⟨δ, hδtail, hδpos, hδlt⟩ : ∃ δ : ℝ,
        ((∫⁻ u in Set.Ioo (-(capAlpha s)) (-(capAlpha s) + δ),
          (Set.Ioo (-(capAlpha s)) (capAlpha s)).indicator
            (fun u => ENNReal.ofReal (s * ‖deriv f (capPt s u)‖)) u) < ENNReal.ofReal (ε / 2))
        ∧ 0 < δ ∧ δ < 2 * capAlpha s := by
      obtain ⟨δ, h1, h23⟩ := (hev1.and (hev2.and hev3)).exists
      obtain ⟨h2, h3⟩ := h23
      exact ⟨δ, h1, h2, h3⟩
    have htne : (∫⁻ u in Set.Ioo (-(capAlpha s)) (-(capAlpha s) + δ),
        (Set.Ioo (-(capAlpha s)) (capAlpha s)).indicator
          (fun u => ENNReal.ofReal (s * ‖deriv f (capPt s u)‖)) u) ≠ ⊤ :=
      ne_of_lt (lt_trans hδtail ENNReal.ofReal_lt_top)
    refine ⟨(fun τ => f (capPt s τ)) '' Set.Ioo (-(capAlpha s)) (-(capAlpha s) + δ), ?_, ?_⟩
    · have hmem : (fun τ => f (capPt s τ)) '' Set.Ioo (-(capAlpha s)) (-(capAlpha s) + δ)
          ∈ map (fun τ => f (capPt s τ)) (𝓝[>] (-(capAlpha s))) := by
        have h4 : Set.Ioo (-(capAlpha s)) (-(capAlpha s) + δ) ∈ 𝓝[>] (-(capAlpha s)) := by
          have h1 : Set.Ioi (-(capAlpha s)) ∈ 𝓝[>] (-(capAlpha s)) := self_mem_nhdsWithin
          have h2 : Set.Iio (-(capAlpha s) + δ) ∈ 𝓝 (-(capAlpha s)) :=
            IsOpen.mem_nhds isOpen_Iio (by linarith : -(capAlpha s) < -(capAlpha s) + δ)
          have h3 : Set.Iio (-(capAlpha s) + δ) ∈ 𝓝[>] (-(capAlpha s)) :=
            (nhdsWithin_le_nhds : 𝓝[Set.Ioi (-(capAlpha s))] (-(capAlpha s)) ≤
              𝓝 (-(capAlpha s))) h2
          rw [show Set.Ioo (-(capAlpha s)) (-(capAlpha s) + δ)
              = Set.Ioi (-(capAlpha s)) ∩ Set.Iio (-(capAlpha s) + δ) from by
            ext x; simp only [Set.mem_Ioo, Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Iio]]
          exact Filter.inter_mem h1 h3
        exact Filter.mem_map.mpr (Filter.mem_of_superset h4 (fun τ hτ => ⟨τ, hτ, rfl⟩))
      exact hmem
    · rintro x ⟨τ, hτ, rfl⟩ y ⟨τ', hτ', rfl⟩
      rw [dist_eq_norm]
      have hτm : -(capAlpha s) < τ := hτ.1
      have hτ'm : τ' < capAlpha s := by linarith [hτ'.2, hδlt]
      have hτm' : -(capAlpha s) < τ' := hτ'.1
      have hstep : ∀ a b : ℝ, -(capAlpha s) < a → a ≤ b → b < -(capAlpha s) + δ →
          ‖f (capPt s b) - f (capPt s a)‖ < ε := by
        intro a b ha hab hb
        have hb' : b < capAlpha s := by linarith [hb, hδlt]
        have h1 := norm_sub_le_integral_capPt hf hs hs2 ha hab hb'
        have h2 : (∫ u in a..b, s * ‖deriv f (capPt s u)‖) ≤
            (∫⁻ u in Set.Ioo a b, ENNReal.ofReal (s * ‖deriv f (capPt s u)‖)).toReal :=
          integral_le_lintegral_toReal (fun u => by positivity) hmeas hab (hm a b ha hab hb')
        have h3 : (∫⁻ u in Set.Ioo a b, ENNReal.ofReal (s * ‖deriv f (capPt s u)‖)).toReal
            ≤ (∫⁻ u in Set.Ioo (-(capAlpha s)) (-(capAlpha s) + δ),
                (Set.Ioo (-(capAlpha s)) (capAlpha s)).indicator
                  (fun u => ENNReal.ofReal (s * ‖deriv f (capPt s u)‖)) u).toReal := by
          refine ENNReal.toReal_mono htne ?_
          have hsub2 : Set.Ioo a b ⊆ Set.Ioo (-(capAlpha s)) (-(capAlpha s) + δ) := by
            intro u hu
            rw [Set.mem_Ioo] at hu ⊢
            exact ⟨by linarith [hu.1, ha], by linarith [hu.2, hb]⟩
          have hsub3 : Set.Ioo a b ⊆ Set.Ioo (-(capAlpha s)) (capAlpha s) := by
            intro u hu
            rw [Set.mem_Ioo] at hu ⊢
            exact ⟨by linarith [hu.1, ha], by linarith [hu.2, hb]⟩
          calc (∫⁻ u in Set.Ioo a b, ENNReal.ofReal (s * ‖deriv f (capPt s u)‖))
              = ∫⁻ u in Set.Ioo a b, (Set.Ioo (-(capAlpha s)) (capAlpha s)).indicator
                  (fun u => ENNReal.ofReal (s * ‖deriv f (capPt s u)‖)) u := by
                exact setLIntegral_congr_fun measurableSet_Ioo (fun u hu =>
                  (Set.indicator_of_mem (hsub3 hu)
                    (fun u => ENNReal.ofReal (s * ‖deriv f (capPt s u)‖))).symm)
            _ ≤ ∫⁻ u in Set.Ioo (-(capAlpha s)) (-(capAlpha s) + δ),
                  (Set.Ioo (-(capAlpha s)) (capAlpha s)).indicator
                    (fun u => ENNReal.ofReal (s * ‖deriv f (capPt s u)‖)) u :=
                lintegral_mono_set hsub2
        have h4 : (∫⁻ u in Set.Ioo (-(capAlpha s)) (-(capAlpha s) + δ),
            (Set.Ioo (-(capAlpha s)) (capAlpha s)).indicator
              (fun u => ENNReal.ofReal (s * ‖deriv f (capPt s u)‖)) u).toReal < ε := by
          have h5 := (ENNReal.toReal_lt_toReal htne ENNReal.ofReal_ne_top).mpr hδtail
          rw [ENNReal.toReal_ofReal (by linarith)] at h5
          linarith
        linarith [h1, h2, h3, h4]
      rcases le_total τ τ' with hle | hle
      · rw [← norm_neg, neg_sub]
        exact hstep τ τ' hτm hle hτ'.2
      · exact hstep τ' τ hτm' hle hτ.2
  obtain ⟨a, ha⟩ := CompleteSpace.complete hcau
  exact ⟨a, ha⟩

/-- A sub-interval of the arc has finite `lintegral`. -/
lemma lintegral_Ioo_ne_top {f : ℂ → ℂ} {s : ℝ} (hfin : capLen f s < ⊤) {τ τ' : ℝ}
    (hτ : -(capAlpha s) < τ) (hτ' : τ' < capAlpha s) :
    (∫⁻ u in Set.Ioo τ τ', ENNReal.ofReal (s * ‖deriv f (capPt s u)‖)) ≠ ⊤ := by
  refine ne_of_lt (lt_of_le_of_lt ?_ hfin)
  rw [← lintegral_indicator_capLen f s]
  have hsub : Set.Ioo τ τ' ⊆ Set.Ioo (-(capAlpha s)) (capAlpha s) := fun u hu => by
    rw [Set.mem_Ioo] at hu ⊢
    exact ⟨by linarith [hu.1, hτ], by linarith [hu.2, hτ']⟩
  calc (∫⁻ u in Set.Ioo τ τ', ENNReal.ofReal (s * ‖deriv f (capPt s u)‖))
      = ∫⁻ u in Set.Ioo τ τ', (Set.Ioo (-(capAlpha s)) (capAlpha s)).indicator
          (fun u => ENNReal.ofReal (s * ‖deriv f (capPt s u)‖)) u := by
        exact setLIntegral_congr_fun measurableSet_Ioo (fun u hu =>
          (Set.indicator_of_mem (hsub hu)
            (fun u => ENNReal.ofReal (s * ‖deriv f (capPt s u)‖))).symm)
    _ ≤ ∫⁻ u, (Set.Ioo (-(capAlpha s)) (capAlpha s)).indicator
          (fun u => ENNReal.ofReal (s * ‖deriv f (capPt s u)‖)) u :=
        setLIntegral_le_lintegral _ _

/-- The integral of the speed over a sub-interval of the arc is at most the (real) `capLen`. -/
lemma integral_capPt_le_capLen {f : ℂ → ℂ} {s : ℝ} (hs : 0 < s) (hfin : capLen f s < ⊤)
    {τ τ' : ℝ} (hτ : -(capAlpha s) < τ) (hτ' : τ' < capAlpha s) (hle : τ ≤ τ') :
    (∫ u in τ..τ', s * ‖deriv f (capPt s u)‖) ≤ (capLen f s).toReal := by
  have hmeas : Measurable (fun u : ℝ => s * ‖deriv f (capPt s u)‖) :=
    measurable_const.mul (((measurable_deriv f).comp (continuous_capPt s).measurable).norm)
  refine le_trans (integral_le_lintegral_toReal (fun u => by
    have := norm_nonneg (deriv f (capPt s u)); positivity) hmeas hle
    (lintegral_Ioo_ne_top hfin hτ hτ')) ?_
  refine ENNReal.toReal_mono (ne_of_lt hfin) ?_
  have hsub : Set.Ioo τ τ' ⊆ Set.Ioo (-(capAlpha s)) (capAlpha s) := fun u hu => by
    rw [Set.mem_Ioo] at hu ⊢
    exact ⟨by linarith [hu.1, hτ], by linarith [hu.2, hτ']⟩
  calc (∫⁻ u in Set.Ioo τ τ', ENNReal.ofReal (s * ‖deriv f (capPt s u)‖))
      = ∫⁻ u in Set.Ioo τ τ', (Set.Ioo (-(capAlpha s)) (capAlpha s)).indicator
          (fun u => ENNReal.ofReal (s * ‖deriv f (capPt s u)‖)) u := by
        exact setLIntegral_congr_fun measurableSet_Ioo (fun u hu =>
          (Set.indicator_of_mem (hsub hu)
            (fun u => ENNReal.ofReal (s * ‖deriv f (capPt s u)‖))).symm)
    _ ≤ ∫⁻ u, (Set.Ioo (-(capAlpha s)) (capAlpha s)).indicator
          (fun u => ENNReal.ofReal (s * ‖deriv f (capPt s u)‖)) u :=
        setLIntegral_le_lintegral _ _
    _ = capLen f s := lintegral_indicator_capLen f s

/-- The right end of the arc converges. -/
lemma exists_tendsto_capPt_right {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.ball (0 : ℂ) 1))
    {s : ℝ} (hs : 0 < s) (hs2 : s < 2) (hfin : capLen f s < ⊤) :
    ∃ b : ℂ, Tendsto (fun τ => f (capPt s τ)) (𝓝[<] (capAlpha s)) (𝓝 b) := by
  have hα0 : 0 < capAlpha s := capAlpha_pos hs2
  have htail := tendsto_tail_right f hs hs2 hfin
  have hmeas : Measurable (fun u : ℝ => s * ‖deriv f (capPt s u)‖) :=
    measurable_const.mul (((measurable_deriv f).comp (continuous_capPt s).measurable).norm)
  have hcau : Cauchy (map (fun τ => f (capPt s τ)) (𝓝[<] (capAlpha s))) := by
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, ?_⟩
    intro ε hε
    have hev1 : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
        (∫⁻ u in Set.Ioo ((capAlpha s) - δ) (capAlpha s),
          (Set.Ioo (-(capAlpha s)) (capAlpha s)).indicator
            (fun u => ENNReal.ofReal (s * ‖deriv f (capPt s u)‖)) u)
          < ENNReal.ofReal (ε / 2) :=
      htail.eventually (IsOpen.mem_nhds isOpen_Iio (ENNReal.ofReal_pos.mpr (by linarith)))
    have hev2 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (0 : ℝ) < δ := self_mem_nhdsWithin
    have hev3 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < 2 * capAlpha s :=
      (eventually_lt_nhds (by linarith [hα0] : (0:ℝ) < 2 * capAlpha s)).filter_mono
        (nhdsWithin_le_nhds : 𝓝[Set.Ioi (0:ℝ)] (0:ℝ) ≤ 𝓝 (0:ℝ))
    obtain ⟨δ, hδtail, hδpos, hδlt⟩ : ∃ δ : ℝ,
        ((∫⁻ u in Set.Ioo ((capAlpha s) - δ) (capAlpha s),
          (Set.Ioo (-(capAlpha s)) (capAlpha s)).indicator
            (fun u => ENNReal.ofReal (s * ‖deriv f (capPt s u)‖)) u) < ENNReal.ofReal (ε / 2))
        ∧ 0 < δ ∧ δ < 2 * capAlpha s := by
      obtain ⟨δ, h1, h23⟩ := (hev1.and (hev2.and hev3)).exists
      obtain ⟨h2, h3⟩ := h23
      exact ⟨δ, h1, h2, h3⟩
    have htne : (∫⁻ u in Set.Ioo ((capAlpha s) - δ) (capAlpha s),
        (Set.Ioo (-(capAlpha s)) (capAlpha s)).indicator
          (fun u => ENNReal.ofReal (s * ‖deriv f (capPt s u)‖)) u) ≠ ⊤ :=
      ne_of_lt (lt_trans hδtail ENNReal.ofReal_lt_top)
    refine ⟨(fun τ => f (capPt s τ)) '' Set.Ioo ((capAlpha s) - δ) (capAlpha s), ?_, ?_⟩
    · have h4 : Set.Ioo ((capAlpha s) - δ) (capAlpha s) ∈ 𝓝[<] (capAlpha s) := by
        have h1 : Set.Iio (capAlpha s) ∈ 𝓝[<] (capAlpha s) := self_mem_nhdsWithin
        have h2 : Set.Ioi ((capAlpha s) - δ) ∈ 𝓝 (capAlpha s) :=
          IsOpen.mem_nhds isOpen_Ioi (by linarith : (capAlpha s) - δ < capAlpha s)
        have h3 : Set.Ioi ((capAlpha s) - δ) ∈ 𝓝[<] (capAlpha s) :=
          (nhdsWithin_le_nhds : 𝓝[Set.Iio (capAlpha s)] (capAlpha s) ≤
            𝓝 (capAlpha s)) h2
        rw [show Set.Ioo ((capAlpha s) - δ) (capAlpha s)
            = Set.Ioi ((capAlpha s) - δ) ∩ Set.Iio (capAlpha s) from by
          ext x; simp only [Set.mem_Ioo, Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Iio]]
        exact Filter.inter_mem h3 h1
      exact Filter.mem_map.mpr (Filter.mem_of_superset h4 (fun τ hτ => ⟨τ, hτ, rfl⟩))
    · rintro x ⟨τ, hτ, rfl⟩ y ⟨τ', hτ', rfl⟩
      rw [dist_eq_norm]
      have hτm : (capAlpha s) - δ < τ := hτ.1
      have hτm' : (capAlpha s) - δ < τ' := hτ'.1
      have hstep : ∀ a b : ℝ, (capAlpha s) - δ < a → a ≤ b → b < capAlpha s →
          ‖f (capPt s b) - f (capPt s a)‖ < ε := by
        intro a b ha hab hb
        have ha' : -(capAlpha s) < a := by linarith [ha, hδlt]
        have h1 := norm_sub_le_integral_capPt hf hs hs2 ha' hab hb
        have h41 : (∫⁻ u in Set.Ioo a b, ENNReal.ofReal (s * ‖deriv f (capPt s u)‖)) ≠ ⊤ := by
          refine ne_of_lt (lt_of_le_of_lt ?_ hfin)
          rw [← lintegral_indicator_capLen f s]
          have hsub3 : Set.Ioo a b ⊆ Set.Ioo (-(capAlpha s)) (capAlpha s) := by
            intro u hu
            rw [Set.mem_Ioo] at hu ⊢
            exact ⟨by linarith [hu.1, ha'], by linarith [hu.2, hb]⟩
          calc (∫⁻ u in Set.Ioo a b, ENNReal.ofReal (s * ‖deriv f (capPt s u)‖))
              = ∫⁻ u in Set.Ioo a b, (Set.Ioo (-(capAlpha s)) (capAlpha s)).indicator
                  (fun u => ENNReal.ofReal (s * ‖deriv f (capPt s u)‖)) u := by
                exact setLIntegral_congr_fun measurableSet_Ioo (fun u hu =>
                  (Set.indicator_of_mem (hsub3 hu)
                    (fun u => ENNReal.ofReal (s * ‖deriv f (capPt s u)‖))).symm)
            _ ≤ ∫⁻ u, (Set.Ioo (-(capAlpha s)) (capAlpha s)).indicator
                  (fun u => ENNReal.ofReal (s * ‖deriv f (capPt s u)‖)) u :=
                setLIntegral_le_lintegral _ _
        have h3 : (∫⁻ u in Set.Ioo a b, ENNReal.ofReal (s * ‖deriv f (capPt s u)‖)).toReal ≤
            (∫⁻ u in Set.Ioo ((capAlpha s) - δ) (capAlpha s),
                (Set.Ioo (-(capAlpha s)) (capAlpha s)).indicator
                  (fun u => ENNReal.ofReal (s * ‖deriv f (capPt s u)‖)) u).toReal := by
          refine ENNReal.toReal_mono htne ?_
          have hsub2 : Set.Ioo a b ⊆ Set.Ioo ((capAlpha s) - δ) (capAlpha s) := by
            intro u hu
            rw [Set.mem_Ioo] at hu ⊢
            exact ⟨by linarith [hu.1, ha], by linarith [hu.2, hb]⟩
          have hsub3 : Set.Ioo a b ⊆ Set.Ioo (-(capAlpha s)) (capAlpha s) := by
            intro u hu
            rw [Set.mem_Ioo] at hu ⊢
            exact ⟨by linarith [hu.1, ha'], by linarith [hu.2, hb]⟩
          calc (∫⁻ u in Set.Ioo a b, ENNReal.ofReal (s * ‖deriv f (capPt s u)‖))
              = ∫⁻ u in Set.Ioo a b, (Set.Ioo (-(capAlpha s)) (capAlpha s)).indicator
                  (fun u => ENNReal.ofReal (s * ‖deriv f (capPt s u)‖)) u := by
                exact setLIntegral_congr_fun measurableSet_Ioo (fun u hu =>
                  (Set.indicator_of_mem (hsub3 hu)
                    (fun u => ENNReal.ofReal (s * ‖deriv f (capPt s u)‖))).symm)
            _ ≤ ∫⁻ u in Set.Ioo ((capAlpha s) - δ) (capAlpha s),
                  (Set.Ioo (-(capAlpha s)) (capAlpha s)).indicator
                    (fun u => ENNReal.ofReal (s * ‖deriv f (capPt s u)‖)) u :=
                lintegral_mono_set hsub2
        have h2' : (∫ u in a..b, s * ‖deriv f (capPt s u)‖) ≤
            (∫⁻ u in Set.Ioo a b, ENNReal.ofReal (s * ‖deriv f (capPt s u)‖)).toReal :=
          integral_le_lintegral_toReal (fun u => by
            have := norm_nonneg (deriv f (capPt s u)); positivity) hmeas hab h41
        have h4 : (∫⁻ u in Set.Ioo ((capAlpha s) - δ) (capAlpha s),
            (Set.Ioo (-(capAlpha s)) (capAlpha s)).indicator
              (fun u => ENNReal.ofReal (s * ‖deriv f (capPt s u)‖)) u).toReal < ε := by
          have h5 := (ENNReal.toReal_lt_toReal htne ENNReal.ofReal_ne_top).mpr hδtail
          rw [ENNReal.toReal_ofReal (by linarith)] at h5
          linarith
        linarith [h1, h2', h3, h4]
      rcases le_total τ τ' with hle | hle
      · rw [← norm_neg, neg_sub]
        exact hstep τ τ' hτm hle hτ'.2
      · exact hstep τ' τ hτm' hle hτ.2
  obtain ⟨b, hb⟩ := CompleteSpace.complete hcau
  exact ⟨b, hb⟩

/-- **The two endpoints of the cap arc.**  They exist, and their distance is at most the length
`capLen f s` of the image arc. -/
theorem exists_tendsto_capPt {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.ball (0 : ℂ) 1))
    {s : ℝ} (hs : 0 < s) (hs2 : s < 2) (hfin : capLen f s < ⊤) :
    ∃ a b : ℂ,
      Tendsto (fun τ => f (capPt s τ)) (𝓝[>] (-(capAlpha s))) (𝓝 a) ∧
      Tendsto (fun τ => f (capPt s τ)) (𝓝[<] (capAlpha s)) (𝓝 b) ∧
      ‖a - b‖ ≤ (capLen f s).toReal := by
  obtain ⟨a, ha⟩ := exists_tendsto_capPt_left hf hs hs2 hfin
  obtain ⟨b, hb⟩ := exists_tendsto_capPt_right hf hs hs2 hfin
  refine ⟨a, b, ha, hb, ?_⟩
  have hC : ∀ τ : ℝ, -(capAlpha s) < τ → τ < capAlpha s →
      ‖f (capPt s τ) - b‖ ≤ (capLen f s).toReal := by
    intro τ hτ1 hτ2
    have hlim : Tendsto (fun τ' : ℝ => ‖f (capPt s τ) - f (capPt s τ')‖)
        (𝓝[<] (capAlpha s)) (𝓝 ‖f (capPt s τ) - b‖) := by
      have h1 : Tendsto (fun τ' : ℝ => f (capPt s τ) - f (capPt s τ'))
          (𝓝[<] (capAlpha s)) (𝓝 (f (capPt s τ) - b)) :=
        tendsto_const_nhds.sub hb
      exact h1.norm
    refine le_of_tendsto hlim ?_
    have hev1 : ∀ᶠ τ' : ℝ in 𝓝[<] (capAlpha s), τ < τ' :=
      (nhdsWithin_le_nhds : 𝓝[Set.Iio (capAlpha s)] (capAlpha s) ≤ 𝓝 (capAlpha s))
        (IsOpen.mem_nhds isOpen_Ioi hτ2)
    have hev2 : ∀ᶠ τ' : ℝ in 𝓝[<] (capAlpha s), τ' < capAlpha s :=
      (self_mem_nhdsWithin : Set.Iio (capAlpha s) ∈ 𝓝[<] (capAlpha s))
    filter_upwards [hev1, hev2] with τ' hlt hlt2
    have hle : τ ≤ τ' := le_of_lt hlt
    have h1 := norm_sub_le_integral_capPt hf hs hs2 hτ1 hle hlt2
    rw [← norm_neg, neg_sub] at h1
    exact le_trans h1 (integral_capPt_le_capLen hs hfin hτ1 hlt2 hle)
  have hlim2 : Tendsto (fun τ : ℝ => ‖f (capPt s τ) - b‖)
      (𝓝[>] (-(capAlpha s))) (𝓝 ‖a - b‖) := by
    have h1 : Tendsto (fun τ : ℝ => f (capPt s τ) - b)
        (𝓝[>] (-(capAlpha s))) (𝓝 (a - b)) := ha.sub tendsto_const_nhds
    exact h1.norm
  refine le_of_tendsto hlim2 ?_
  have hev3 : ∀ᶠ τ : ℝ in 𝓝[>] (-(capAlpha s)), τ < capAlpha s :=
    (eventually_lt_nhds (by linarith [capAlpha_pos hs2] : -(capAlpha s) < capAlpha s)).filter_mono
      (nhdsWithin_le_nhds : 𝓝[Set.Ioi (-(capAlpha s))] (-(capAlpha s)) ≤ 𝓝 (-(capAlpha s)))
  have hev4 : ∀ᶠ τ : ℝ in 𝓝[>] (-(capAlpha s)), -(capAlpha s) < τ :=
    (self_mem_nhdsWithin : Set.Ioi (-(capAlpha s)) ∈ 𝓝[>] (-(capAlpha s)))
  filter_upwards [hev3, hev4] with τ h1 h2
  exact hC τ h2 h1

end Work.Smooth.SphereJordan.Caratheodory
