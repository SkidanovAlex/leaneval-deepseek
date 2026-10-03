import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.LocallyUniformLimit

namespace Commons.Analysis.Complex

open Filter Metric Set

/-- If a sequence of functions converges uniformly on a compact set `s`, and so do their
derivatives, and the limit `H` is continuous and zero-free on `s`, then the logarithmic
derivatives converge uniformly on `s`. -/
lemma tendstoUniformlyOn_logDeriv_of_tendstoUniformlyOn {F : ℕ → ℂ → ℂ} {H : ℂ → ℂ}
    {s : Set ℂ}
    (hsc : IsCompact s)
    (hHc : ContinuousOn H s) (hHd : ContinuousOn (fun z => deriv H z) s)
    (hne : ∀ z ∈ s, H z ≠ 0)
    (hF : TendstoUniformlyOn F H atTop s)
    (hFd : TendstoUniformlyOn (fun n z => deriv (F n) z) (fun z => deriv H z) atTop s) :
    TendstoUniformlyOn (fun n z => logDeriv (F n) z) (fun z => logDeriv H z) atTop s := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  rcases s.eq_empty_or_nonempty with rfl | hsne
  · exact Filter.Eventually.of_forall fun n => by simp
  have hHcnorm : ContinuousOn (fun z => ‖H z‖) s := hHc.norm
  have hHdnorm : ContinuousOn (fun z => ‖deriv H z‖) s := hHd.norm
  obtain ⟨x₀, hx₀, hmin⟩ := hsc.exists_isMinOn hsne hHcnorm
  obtain ⟨x₁, hx₁, hmax⟩ := hsc.exists_isMaxOn hsne hHcnorm
  obtain ⟨x₂, hx₂, hmax₂⟩ := hsc.exists_isMaxOn hsne hHdnorm
  set δ := ‖H x₀‖ with hδdef
  set M0 := ‖H x₁‖ with hM0def
  set M1 := ‖deriv H x₂‖ with hM1def
  have hδpos : 0 < δ := by rw [hδdef]; exact norm_pos_iff.mpr (hne x₀ hx₀)
  have hHle : ∀ z ∈ s, ‖H z‖ ≤ M0 := fun z hz => hmax hz
  have hHge : ∀ z ∈ s, δ ≤ ‖H z‖ := fun z hz => hmin hz
  have hdHle : ∀ z ∈ s, ‖deriv H z‖ ≤ M1 := fun z hz => hmax₂ hz
  set e := min (δ / 2) (ε * ((δ / 2) * δ) / (4 * (M0 + M1 + 1))) with hedef
  have hepos : 0 < e := by
    have h1 : (0 : ℝ) < δ / 2 := by linarith
    have h2 : (0 : ℝ) < ε * ((δ / 2) * δ) / (4 * (M0 + M1 + 1)) := by
      apply div_pos
      · exact mul_pos hε (mul_pos h1 hδpos)
      · positivity
    rw [hedef]; exact lt_min h1 h2
  have he_le : e ≤ ε * ((δ / 2) * δ) / (4 * (M0 + M1 + 1)) := by
    rw [hedef]; exact min_le_right _ _
  have he_le2 : e ≤ δ / 2 := by rw [hedef]; exact min_le_left _ _
  have hFev : ∀ᶠ n in atTop, ∀ z ∈ s, ‖H z - F n z‖ < e := by
    have h := (Metric.tendstoUniformlyOn_iff.mp hF) e hepos
    filter_upwards [h] with n hn z hz
    have h' := hn z hz
    rwa [dist_eq_norm] at h'
  have hFdev : ∀ᶠ n in atTop, ∀ z ∈ s, ‖deriv (F n) z - deriv H z‖ < e := by
    have h := (Metric.tendstoUniformlyOn_iff.mp hFd) e hepos
    filter_upwards [h] with n hn z hz
    have h' := hn z hz
    rwa [dist_eq_norm, norm_sub_rev] at h'
  filter_upwards [hFev, hFdev] with n hnF hnFd
  intro z hz
  rw [dist_eq_norm, norm_sub_rev]
  have hnFz : ‖H z - F n z‖ < e := hnF z hz
  have hndz : ‖deriv (F n) z - deriv H z‖ < e := hnFd z hz
  have hFnlow : δ / 2 ≤ ‖F n z‖ := by
    have h1 : ‖H z‖ ≤ ‖F n z‖ + ‖H z - F n z‖ := by
      have hz' : H z = F n z + (H z - F n z) := by ring
      calc ‖H z‖ = ‖F n z + (H z - F n z)‖ := by conv_lhs => rw [hz']
        _ ≤ ‖F n z‖ + ‖H z - F n z‖ := norm_add_le (F n z) (H z - F n z)
    have h2 : δ ≤ ‖H z‖ := hHge z hz
    linarith
  have hb : F n z ≠ 0 := by
    have : 0 < ‖F n z‖ := by linarith
    exact norm_ne_zero_iff.mp (ne_of_gt this)
  have hb0 : H z ≠ 0 := hne z hz
  have hkey : logDeriv (F n) z - logDeriv H z
      = (deriv (F n) z * H z - F n z * deriv H z) / (F n z * H z) := by
    rw [logDeriv_apply, logDeriv_apply]
    exact div_sub_div _ _ hb hb0
  rw [hkey]
  have hnum : ‖deriv (F n) z * H z - F n z * deriv H z‖ ≤ e * (M0 + M1) := by
    have hdecomp : deriv (F n) z * H z - F n z * deriv H z
        = (deriv (F n) z - deriv H z) * H z + deriv H z * (H z - F n z) := by ring
    rw [hdecomp]
    calc ‖(deriv (F n) z - deriv H z) * H z + deriv H z * (H z - F n z)‖
        ≤ ‖(deriv (F n) z - deriv H z) * H z‖ + ‖deriv H z * (H z - F n z)‖ :=
          norm_add_le ((deriv (F n) z - deriv H z) * H z) (deriv H z * (H z - F n z))
      _ = ‖deriv (F n) z - deriv H z‖ * ‖H z‖ + ‖deriv H z‖ * ‖H z - F n z‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ e * M0 + M1 * e := by
          have h1 : ‖deriv (F n) z - deriv H z‖ * ‖H z‖ ≤ e * M0 :=
            mul_le_mul (le_of_lt hndz) (hHle z hz) (norm_nonneg _) (le_of_lt hepos)
          have h2 : ‖deriv H z‖ * ‖H z - F n z‖ ≤ M1 * e :=
            mul_le_mul (hdHle z hz) (le_of_lt hnFz) (norm_nonneg _) (norm_nonneg _)
          linarith
      _ = e * (M0 + M1) := by ring
  have hden : (δ / 2) * δ ≤ ‖F n z * H z‖ := by
    rw [norm_mul]
    exact mul_le_mul hFnlow (hHge z hz) (by linarith) (norm_nonneg _)
  have hbnd : ‖(deriv (F n) z * H z - F n z * deriv H z) / (F n z * H z)‖
      ≤ e * (M0 + M1) / ((δ / 2) * δ) := by
    rw [norm_div]
    exact div_le_div₀ (by positivity) hnum (by positivity) hden
  have hfin : e * (M0 + M1) / ((δ / 2) * δ) < ε := by
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (δ / 2) * δ)]
    have hB : 0 < M0 + M1 + 1 := by positivity
    have hM : 0 ≤ M0 + M1 := by positivity
    have hstep1 : e * (M0 + M1) ≤ (ε * ((δ / 2) * δ) / (4 * (M0 + M1 + 1))) * (M0 + M1 + 1) := by
      have h1 : e * (M0 + M1) ≤ (ε * ((δ / 2) * δ) / (4 * (M0 + M1 + 1))) * (M0 + M1) :=
        mul_le_mul_of_nonneg_right he_le hM
      have h2 : (ε * ((δ / 2) * δ) / (4 * (M0 + M1 + 1))) * (M0 + M1) ≤
          (ε * ((δ / 2) * δ) / (4 * (M0 + M1 + 1))) * (M0 + M1 + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
    have hstep2 : (ε * ((δ / 2) * δ) / (4 * (M0 + M1 + 1))) * (M0 + M1 + 1)
        = ε * ((δ / 2) * δ) / 4 := by
      field_simp
    have hstep3 : ε * ((δ / 2) * δ) / 4 < ε * ((δ / 2) * δ) := by
      have hp : 0 < ε * ((δ / 2) * δ) := by positivity
      linarith
    linarith
  linarith

theorem tendsto_circleIntegral_logDeriv_of_tendstoLocallyUniformlyOn
    {F : ℕ → ℂ → ℂ} {H : ℂ → ℂ} {c : ℂ} {R ρ : ℝ} (hR : 0 < R) (hρ : R < ρ)
    (hF : ∀ n, ∀ z ∈ Metric.ball c ρ, AnalyticAt ℂ (F n) z)
    (hH : ∀ z ∈ Metric.ball c ρ, AnalyticAt ℂ H z)
    (hne : ∀ z ∈ Metric.sphere c R, H z ≠ 0)
    (hconv : TendstoLocallyUniformlyOn F H Filter.atTop (Metric.ball c ρ)) :
    Filter.Tendsto (fun n => ∮ z in C(c, R), logDeriv (F n) z) Filter.atTop
      (nhds (∮ z in C(c, R), logDeriv H z)) := by
  have hsub : Metric.sphere c R ⊆ Metric.ball c ρ := by
    intro z hz
    rw [Metric.mem_sphere] at hz
    rw [Metric.mem_ball]
    rw [hz]
    exact hρ
  have hconvS : TendstoUniformlyOn F H atTop (Metric.sphere c R) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball).mp hconv _
      hsub (isCompact_sphere c R)
  have hFdiff : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) (Metric.ball c ρ) :=
    Eventually.of_forall fun n z hz => (hF n z hz).differentiableAt.differentiableWithinAt
  have hconvD := hconv.deriv hFdiff isOpen_ball
  have hconvDS : TendstoUniformlyOn (fun n z => deriv (F n) z) (fun z => deriv H z) atTop
      (Metric.sphere c R) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball).mp hconvD _
      hsub (isCompact_sphere c R)
  have hHcont : ContinuousOn H (Metric.sphere c R) :=
    fun z hz => ((hH z (hsub hz)).continuousAt).continuousWithinAt
  have hHdcont : ContinuousOn (fun z => deriv H z) (Metric.sphere c R) :=
    fun z hz => ((hH z (hsub hz)).deriv.continuousAt).continuousWithinAt
  have hlogconv : TendstoUniformlyOn (fun n z => logDeriv (F n) z) (fun z => logDeriv H z)
      atTop (Metric.sphere c R) :=
    tendstoUniformlyOn_logDeriv_of_tendstoUniformlyOn (isCompact_sphere c R) hHcont hHdcont
      hne hconvS hconvDS
  have hHcontnorm : ContinuousOn (fun z => ‖H z‖) (Metric.sphere c R) := hHcont.norm
  obtain ⟨δ, hδpos, hδle⟩ := (isCompact_sphere c R).exists_forall_le' hHcontnorm
    (a := 0) (fun z hz => by rw [norm_pos_iff]; exact hne z hz)
  have hcont : ∀ᶠ n in atTop, ContinuousOn (fun z => logDeriv (F n) z) (Metric.sphere c R) := by
    have hev : ∀ᶠ n in atTop, ∀ z ∈ Metric.sphere c R, ‖H z - F n z‖ < δ / 2 := by
      have h := (Metric.tendstoUniformlyOn_iff.mp hconvS) (δ / 2) (by linarith)
      filter_upwards [h] with n hn z hz
      have h' := hn z hz
      rwa [dist_eq_norm] at h'
    filter_upwards [hev] with n hn
    intro z hz
    have hFnne : F n z ≠ 0 := by
      have h1 : ‖H z‖ ≤ ‖F n z‖ + ‖H z - F n z‖ := by
        have hz' : H z = F n z + (H z - F n z) := by ring
        calc ‖H z‖ = ‖F n z + (H z - F n z)‖ := by conv_lhs => rw [hz']
          _ ≤ ‖F n z‖ + ‖H z - F n z‖ := norm_add_le (F n z) (H z - F n z)
      have h2 : δ ≤ ‖H z‖ := hδle z hz
      have h3 : ‖H z - F n z‖ < δ / 2 := hn z hz
      have : 0 < ‖F n z‖ := by linarith
      exact norm_ne_zero_iff.mp (ne_of_gt this)
    have hzan : AnalyticAt ℂ (F n) z := hF n z (hsub hz)
    have hc : ContinuousAt (fun w => logDeriv (F n) w) z := by
      change ContinuousAt (deriv (F n) / F n) z
      exact (hzan.deriv.continuousAt).div hzan.continuousAt hFnne
    exact hc.continuousWithinAt
  exact hlogconv.tendsto_circleIntegral_of_continuousOn hR.le hcont

end Commons.Analysis.Complex