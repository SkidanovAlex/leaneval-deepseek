import Mathlib
import Submission.Work.Drive.exists_close_nonzero_curvature

/-!
# A `C²`-close knot with nowhere vanishing curvature

Refinement of `Work.Drive.exists_close_nonzero_curvature` (which produces a `C¹`-close knot with
nowhere vanishing curvature): the same construction also controls the **second** derivative, so the
approximation can be made `C²`-small.  Everything of substance is the machinery copied from that
module (analyticity of the curvature vector, the finite zero set of inflections in the fundamental
period, the local factorisation at an inflection, the trigonometric perturbation killing the
first-order term, and the compact reminder argument).  The only new ingredient here is that the
core perturbation lemma returns an *interval* `(0, τ₁)` of admissible perturbation sizes `τ`, hence
`τ` may be chosen so small that `τ • deriv (deriv φ)` is below the required `C²` threshold.
-/

namespace Work.Drive
open LeanEval.KnotTheory.Quadrisecant
open Filter
open scoped Topology

private lemma periodic_deriv' {f : ℝ → Space} {c : ℝ} (h : Function.Periodic f c) :
    Function.Periodic (deriv f) c := by
  intro x
  have hx : deriv (fun y : ℝ => f (y + c)) x = deriv f x := by
    rw [show (fun y : ℝ => f (y + c)) = f from funext h]
  rwa [deriv_comp_add_const f c x] at hx

private lemma exists_norm_bound_of_periodic {f : ℝ → Space} {c : ℝ} (hc : 0 < c)
    (hf : Continuous f) (hper : Function.Periodic f c) :
    ∃ M : ℝ, 0 < M ∧ ∀ t : ℝ, ‖f t‖ ≤ M := by
  obtain ⟨x₀, hx₀, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0, le_rfl, hc.le⟩ hf.continuousOn.norm
  refine ⟨max (‖f x₀‖) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun t => ?_⟩
  obtain ⟨y, hy, hty⟩ := hper.exists_mem_Ico hc t 0
  have hy' : y ∈ Set.Icc 0 c := Set.Ico_subset_Icc_self (by simpa using hy)
  calc ‖f t‖ = ‖f y‖ := by rw [hty]
    _ ≤ ‖f x₀‖ := hmax hy'
    _ ≤ max (‖f x₀‖) 1 := le_max_left _ _

private lemma continuous_cross3 {f g : ℝ → Space} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun t => cross3 (f t) (g t)) := by
  have h : Continuous (fun p : Space × Space => cross3 p.1 p.2) := by
    simpa [cross3] using Commons.Analysis.CrossProduct.cross3_contDiff.continuous
  exact h.comp (hf.prodMk hg)

private lemma inner_cross3_self_right (u w : Space) : inner ℝ (cross3 u w) w = 0 := by
  have h2 : inner ℝ (cross3 w u) w = 0 := by
    simpa [cross3] using Commons.Analysis.CrossProduct.inner_cross3_self_left w u
  have h : cross3 u w = -cross3 w u := by
    rw [cross3_anticomm u w]; simp
  rw [h, inner_neg_left, h2, neg_zero]

private lemma li_of_cross3 {A v W₀ : Space} {c : ℝ} (hA : A ≠ 0) (hv : v ≠ 0)
    (horth : inner ℝ A v = 0) (hc : c ≠ 0) (hW : W₀ = c • cross3 v A) :
    LinearIndependent ℝ ![A, W₀] := by
  have hvv : inner ℝ v v ≠ 0 := by
    rw [real_inner_self_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)
  have hAA : inner ℝ A A ≠ 0 := by
    rw [real_inner_self_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hA)
  have hcv : cross3 v A ≠ 0 := by
    intro h0
    rcases (Commons.Analysis.CrossProduct.cross3_eq_zero_iff_smul v A).mp h0 with hv0 | ⟨t, ht⟩
    · exact hv hv0
    · have h2 : t * inner ℝ v v = 0 := by
        have h3 := horth
        rw [ht, real_inner_smul_left] at h3
        exact h3
      exact hA (by rw [ht, (mul_eq_zero.mp h2).resolve_right hvv, zero_smul])
  have hcross : cross3 A (cross3 v A) ≠ 0 := by
    intro h0
    rcases (Commons.Analysis.CrossProduct.cross3_eq_zero_iff_smul A (cross3 v A)).mp h0 with hA0 | ⟨t, ht⟩
    · exact hA hA0
    · have h2 : inner ℝ (cross3 v A) A = 0 := inner_cross3_self_right v A
      rw [ht, real_inner_smul_left] at h2
      have ht0 : t = 0 := (mul_eq_zero.mp h2).resolve_right hAA
      exact hcv (by rw [ht, ht0, zero_smul])
  have hWA : cross3 A W₀ ≠ 0 := by
    rw [hW, cross3_smul_right]
    exact smul_ne_zero hc hcross
  rw [← cross3_ne_zero_iff_linearIndependent_local]
  exact hWA

/-- The set of inflection parameters in the fundamental period is finite. -/
private lemma finite_inflection_set {r : ℝ → Space} (hr : IsSmoothKnot r) :
    {t : ℝ | t ∈ Set.Icc 0 period ∧ inflec r t = 0}.Finite := by
  have h1 : (⊤ : WithTop ℕ∞) + 1 = ⊤ := by simp
  have hvel : ContDiff ℝ ⊤ (velocity r) := h1 ▸ hr.smooth.deriv'
  have hacc : ContDiff ℝ ⊤ (accel r) := h1 ▸ hvel.deriv'
  have hcross : ContDiff ℝ ⊤ (fun p : Space × Space => cross3 p.1 p.2) := by
    simpa [cross3] using Commons.Analysis.CrossProduct.cross3_contDiff
  have hVdiff : ContDiff ℝ ⊤ (inflec r) := hcross.comp (hvel.prodMk hacc)
  have han : AnalyticOnNhd ℝ (fun t : ℝ => ‖inflec r t‖ ^ 2) Set.univ :=
    contDiff_omega_iff_analyticOnNhd.mp ((contDiff_norm_sq ℝ).comp hVdiff)
  have hVper : ∀ t : ℝ, inflec r (t + period) = inflec r t := by
    intro t
    have hv : velocity r (t + period) = velocity r t := hr.velocity_periodic t
    have ha : accel r (t + period) = accel r t :=
      periodic_deriv' (f := velocity r) hr.velocity_periodic t
    simp only [inflec, hv, ha]
  have hper : Function.Periodic (fun t : ℝ => ‖inflec r t‖ ^ 2) period := by
    intro t
    show ‖inflec r (t + period)‖ ^ 2 = ‖inflec r t‖ ^ 2
    rw [hVper t]
  obtain ⟨t₁, ht₁, hLI⟩ := exists_noninflection_point hr
  have hne : ∃ x ∈ Set.Icc 0 period, ‖inflec r x‖ ^ 2 ≠ 0 := by
    refine ⟨t₁, ht₁, ?_⟩
    have hz : inflec r t₁ ≠ 0 := fun h0 => (cross3_ne_zero_iff_linearIndependent_local _ _).mpr hLI h0
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
  have hfin := Commons.Analysis.Analytic.finite_zeros_of_analytic_periodic period_pos han hper hne
  refine hfin.subset ?_
  intro t ht
  exact ⟨ht.1, by rw [ht.2]; simp⟩

/-- Local data at an inflection parameter. -/
private structure FactorData (r : ℝ → Space) (t : ℝ) where
  n : ℕ
  fac : ℝ → Space
  A : Space
  ρ : ℝ
  hn : 1 ≤ n
  hρ : 0 < ρ
  hcont : ContinuousAt fac t
  hfac_t : fac t = A
  hA : A ≠ 0
  horth : inner ℝ A (velocity r t) = 0
  hfac_eq : ∀ s : ℝ, |s - t| < ρ → inflec r s = (s - t) ^ n • fac s

private lemma exists_local_factorization {r : ℝ → Space} (hr : IsSmoothKnot r)
    {t₀ : ℝ} (ht₀ : inflec r t₀ = 0) : Nonempty (FactorData r t₀) := by
  have h1 : (⊤ : WithTop ℕ∞) + 1 = ⊤ := by simp
  have hvel : ContDiff ℝ ⊤ (velocity r) := h1 ▸ hr.smooth.deriv'
  have hacc : ContDiff ℝ ⊤ (accel r) := h1 ▸ hvel.deriv'
  have hcross : ContDiff ℝ ⊤ (fun p : Space × Space => cross3 p.1 p.2) := by
    simpa [cross3] using Commons.Analysis.CrossProduct.cross3_contDiff
  have hVdiff : ContDiff ℝ ⊤ (inflec r) := hcross.comp (hvel.prodMk hacc)
  have hVan : AnalyticAt ℝ (inflec r) t₀ :=
    AnalyticOn.analyticAt Filter.univ_mem ((contDiff_omega_iff_analyticOnNhd.mp hVdiff).analyticOn)
  have hne : ¬ ∀ᶠ z in 𝓝 t₀, inflec r z = 0 := by
    intro hz
    have hEq : Set.EqOn (inflec r) 0 Set.univ :=
      (contDiff_omega_iff_analyticOnNhd.mp hVdiff).eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_univ (Set.mem_univ t₀) hz
    obtain ⟨t₁, -, hLI⟩ := exists_noninflection_point hr
    exact (cross3_ne_zero_iff_linearIndependent_local _ _).mpr hLI (hEq (Set.mem_univ t₁))
  obtain ⟨n, g, hgan, hgne, hgeq⟩ :=
    (AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff hVan).mpr hne
  obtain ⟨ρ, hρ, hρb⟩ := Metric.eventually_nhds_iff.mp hgeq
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · exfalso
      have hge : inflec r =ᶠ[𝓝 t₀] g := by
        filter_upwards [hgeq] with z hz
        rw [hz, hn, pow_zero, one_smul]
      have hgt : inflec r t₀ = g t₀ := tendsto_nhds_unique hVan.continuousAt
        (Tendsto.congr' hge.symm hgan.continuousAt)
      exact hgne (by rw [← hgt]; exact ht₀)
    · exact hn
  have horth : inner ℝ (g t₀) (velocity r t₀) = 0 := by
    let F : ℝ → ℝ := fun z => inner ℝ (g z) (velocity r z)
    have hFt : F t₀ = inner ℝ (g t₀) (velocity r t₀) := rfl
    rw [← hFt]
    have hFcont : ContinuousAt F t₀ := hgan.continuousAt.inner hvel.continuous.continuousAt
    have hpunct : F =ᶠ[𝓝[≠] t₀] (fun _ => (0 : ℝ)) := by
      filter_upwards [hgeq.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hzne
      change inner ℝ (g z) (velocity r z) = 0
      have hpow : (z - t₀) ^ n ≠ 0 := pow_ne_zero n (sub_ne_zero.mpr hzne)
      have h0 : inner ℝ (inflec r z) (velocity r z) = 0 := by
        show inner ℝ (cross3 (velocity r z) (accel r z)) (velocity r z) = 0
        rw [cross3]
        exact Commons.Analysis.CrossProduct.inner_cross3_self_left _ _
      have h1' : (z - t₀) ^ n * inner ℝ (g z) (velocity r z) = 0 := by
        rw [← real_inner_smul_left (g z) (velocity r z) ((z - t₀) ^ n), ← hz]
        exact h0
      exact (mul_eq_zero.mp h1').resolve_left hpow
    have h2 : Tendsto F (𝓝[≠] t₀) (𝓝 0) :=
      Tendsto.congr' hpunct.symm tendsto_const_nhds
    have h4 : Tendsto F (𝓝[≠] t₀) (𝓝 (F t₀)) :=
      hFcont.tendsto.mono_left nhdsWithin_le_nhds
    exact tendsto_nhds_unique h4 h2
  exact ⟨⟨n, g, g t₀, ρ, hn1, hρ, hgan.continuousAt, rfl, hgne, horth, hρb⟩⟩



private lemma local_nonvanishing {V W Q Vfac : ℝ → Space} {t₀ : ℝ} {n : ℕ} (hn : 1 ≤ n)
    {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hfac : ∀ t : ℝ, |t - t₀| < ρ₀ → V t = (t - t₀) ^ n • Vfac t)
    {A W₀ : Space} (hVc : ContinuousAt Vfac t₀) (hVt : Vfac t₀ = A)
    (hWc : ContinuousAt W t₀) (hW0 : W t₀ = W₀)
    (hLI : LinearIndependent ℝ ![A, W₀]) (hQc : ContinuousAt Q t₀) :
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ρ₀ ∧
      ∀ τ ∈ Set.Ioo 0 τ₀, ∀ t : ℝ, |t - t₀| < ρ → V t + τ • W t + τ ^ 2 • Q t ≠ 0 := by
  have hpair : ∀ s t : ℝ, s • A + t • W₀ = 0 → s = 0 ∧ t = 0 :=
    (LinearIndependent.pair_iff).mp hLI
  have hWne : W₀ ≠ 0 := by
    intro hW
    have h1 := (hpair 0 1 (by rw [hW]; simp)).2
    norm_num at h1
  -- the cone constant: `c * (|a| + b) <= ‖a • A + b • W₀‖` for `b >= 0`
  set P : Set (ℝ × ℝ) := {p : ℝ × ℝ | |p.1| + p.2 = 1 ∧ 0 ≤ p.2} with hP
  have hPne : P.Nonempty := ⟨(0, 1), by simp [hP]⟩
  have hPclosed : IsClosed P := by
    have h1 : P = {p : ℝ × ℝ | |p.1| + p.2 = 1} ∩ {p : ℝ × ℝ | 0 ≤ p.2} := by
      ext p; simp [hP, and_comm]
    rw [h1]
    exact IsClosed.inter (isClosed_eq (by fun_prop) continuous_const)
      (isClosed_le continuous_const continuous_snd)
  have hPsub : P ⊆ Set.Icc (-1:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1 := by
    intro p hp
    obtain ⟨h1, h2⟩ := hp
    have h3 : |p.1| ≤ 1 := by linarith [abs_nonneg p.1]
    exact ⟨⟨neg_le_of_abs_le h3, le_of_abs_le h3⟩, ⟨h2, by linarith [abs_nonneg p.1]⟩⟩
  have hPcomp : IsCompact P := (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hPclosed hPsub
  have hcont : ContinuousOn (fun p : ℝ × ℝ => ‖p.1 • A + p.2 • W₀‖) P := by fun_prop
  obtain ⟨p₀, hp₀, hmin⟩ := hPcomp.exists_isMinOn hPne hcont
  have hnn : p₀.1 • A + p₀.2 • W₀ ≠ 0 := by
    intro hzero
    obtain ⟨h1, h2⟩ := hpair p₀.1 p₀.2 hzero
    have h4 := hp₀.1
    rw [h1, h2, abs_zero] at h4
    norm_num at h4
  set c : ℝ := ‖p₀.1 • A + p₀.2 • W₀‖ with hc
  have hcpos : 0 < c := by rw [hc]; exact norm_pos_iff.mpr hnn
  have hminc : ∀ p ∈ P, c ≤ ‖p.1 • A + p.2 • W₀‖ := by
    intro p hp; rw [hc]; exact hmin hp
  have hcone : ∀ α β : ℝ, 0 ≤ β → c * (|α| + β) ≤ ‖α • A + β • W₀‖ := by
    intro α β hβ
    by_cases hlam : |α| + β = 0
    · have hα : α = 0 := abs_eq_zero.mp (le_antisymm (by linarith) (abs_nonneg α))
      have hβ0 : β = 0 := by linarith [abs_nonneg α]
      rw [hα, hβ0]; simp
    · have hlpos : 0 < |α| + β := lt_of_le_of_ne (by positivity) (Ne.symm hlam)
      have hmem : ((α / (|α| + β), β / (|α| + β)) : ℝ × ℝ) ∈ P := by
        have h1 : |α / (|α| + β)| = |α| / (|α| + β) := by
          rw [abs_div, abs_of_pos hlpos]
        exact ⟨by rw [h1, ← add_div, div_eq_one_iff_eq (ne_of_gt hlpos)], by positivity⟩
      have hkey := hminc _ hmem
      have hdec : α • A + β • W₀
          = (|α| + β) • ((α / (|α| + β)) • A + (β / (|α| + β)) • W₀) := by
        rw [smul_add, smul_smul, smul_smul, mul_div_cancel₀ α (ne_of_gt hlpos),
          mul_div_cancel₀ β (ne_of_gt hlpos)]
      rw [hdec, norm_smul, Real.norm_of_nonneg hlpos.le]
      calc c * (|α| + β)
          ≤ ‖(α / (|α| + β)) • A + (β / (|α| + β)) • W₀‖ * (|α| + β) :=
            mul_le_mul_of_nonneg_right hkey hlpos.le
        _ = (|α| + β) * ‖(α / (|α| + β)) • A + (β / (|α| + β)) • W₀‖ := by ring
  have hcW : c ≤ ‖W₀‖ := by
    have := hcone 0 1 (by norm_num)
    simpa using this
  -- continuity data on a small ball
  have hVev : ∀ᶠ t in 𝓝 t₀, ‖Vfac t - A‖ ≤ c / 8 := by
    have ht := hVc.tendsto
    rw [hVt] at ht
    have h2 := (Metric.tendsto_nhds.mp ht) (c / 8) (by linarith)
    filter_upwards [h2] with t ht'
    rw [dist_eq_norm] at ht'
    exact le_of_lt ht'
  have hWev : ∀ᶠ t in 𝓝 t₀, ‖W t - W₀‖ ≤ c / 8 := by
    have ht := hWc.tendsto
    rw [hW0] at ht
    have h2 := (Metric.tendsto_nhds.mp ht) (c / 8) (by linarith)
    filter_upwards [h2] with t ht'
    rw [dist_eq_norm] at ht'
    exact le_of_lt ht'
  have hQev : ∀ᶠ t in 𝓝 t₀, ‖Q t - Q t₀‖ ≤ 1 := by
    have ht := hQc.tendsto
    have h2 := (Metric.tendsto_nhds.mp ht) 1 (by norm_num)
    filter_upwards [h2] with t ht'
    rw [dist_eq_norm] at ht'
    exact le_of_lt ht'
  obtain ⟨ρ₁, hρ₁pos, hρ₁⟩ := Metric.eventually_nhds_iff.mp (hVev.and (hWev.and hQev))
  have hVb : ∀ t : ℝ, |t - t₀| < ρ₁ → ‖Vfac t - A‖ ≤ c / 8 := fun t ht =>
    (hρ₁ (by rwa [Real.dist_eq])).1
  have hWb : ∀ t : ℝ, |t - t₀| < ρ₁ → ‖W t - W₀‖ ≤ c / 8 := fun t ht =>
    (hρ₁ (by rwa [Real.dist_eq])).2.1
  have hQb : ∀ t : ℝ, |t - t₀| < ρ₁ → ‖Q t - Q t₀‖ ≤ 1 := fun t ht =>
    (hρ₁ (by rwa [Real.dist_eq])).2.2
  refine ⟨min 1 (c / (8 * (‖Q t₀‖ + 1) + 8)), lt_min one_pos (by positivity), min ρ₀ ρ₁,
    lt_min hρ₀ hρ₁pos, min_le_left _ _, ?_⟩
  · intro τ hτ t ht
    have hτpos : 0 < τ := hτ.1
    have hτ1 : τ < 1 := lt_of_lt_of_le hτ.2 (min_le_left _ _)
    have hτ2 : τ < c / (8 * (‖Q t₀‖ + 1) + 8) := lt_of_lt_of_le hτ.2 (min_le_right _ _)
    have htm : |t - t₀| < ρ₁ := lt_of_lt_of_le ht (min_le_right _ _)
    have hfac1 : V t = (t - t₀) ^ n • Vfac t := hfac t (lt_of_lt_of_le ht (min_le_left _ _))
    have hVb' := hVb t htm
    have hWb' := hWb t htm
    have hQt₀ : ‖Q t₀‖ ≤ ‖Q t₀‖ + 1 := by linarith
    have hQt : ‖Q t‖ ≤ ‖Q t₀‖ + 1 := by
      have h5 : ‖Q t‖ - ‖Q t₀‖ ≤ ‖Q t - Q t₀‖ :=
        le_trans (le_abs_self _) (abs_norm_sub_norm_le _ _)
      have h6 : ‖Q t - Q t₀‖ ≤ 1 := hQb t htm
      linarith
    have hMQτ : τ * (‖Q t₀‖ + 1) < c / 8 := by
      have h4 : τ * (8 * (‖Q t₀‖ + 1) + 8) < c := by
        have h5 : c / (8 * (‖Q t₀‖ + 1) + 8) * (8 * (‖Q t₀‖ + 1) + 8) = c := by
          have hne : (8 * (‖Q t₀‖ + 1) + 8) ≠ 0 := by positivity
          field_simp
        have h6 := mul_lt_mul_of_pos_right hτ2 (by positivity : (0:ℝ) < 8 * (‖Q t₀‖ + 1) + 8)
        rwa [h5] at h6
      nlinarith [hτpos, hτ1, h4]
    by_cases ht0 : t = t₀
    · intro hzero
      have hV0 : V t = 0 := by
        rw [hfac1, ht0, sub_self, zero_pow (by omega : n ≠ 0), zero_smul]
      rw [hV0, zero_add] at hzero
      have h2 : W t + τ • Q t = 0 := by
        have h3 : τ • (W t + τ • Q t) = 0 := by
          have h4 : τ • (W t + τ • Q t) = τ • W t + τ ^ 2 • Q t := by
            rw [smul_add, pow_two, smul_smul]
          rw [h4]
          exact hzero
        exact (smul_eq_zero.mp h3).resolve_left (ne_of_gt hτpos)
      have hWt : W t = W₀ := by rw [ht0]; exact hW0
      have h4 : W₀ + τ • Q t = 0 := by rw [← hWt]; exact h2
      have h5 : ‖W₀‖ = τ * ‖Q t‖ := by
        have h6 : W₀ = -(τ • Q t) := by
          rw [eq_neg_iff_add_eq_zero]; exact h4
        rw [h6, norm_neg, norm_smul, Real.norm_of_nonneg hτpos.le]
      have h7 : τ * ‖Q t‖ < ‖W₀‖ := by
        have h8 : τ * ‖Q t‖ ≤ τ * (‖Q t₀‖ + 1) :=
          mul_le_mul_of_nonneg_left hQt hτpos.le
        linarith [hMQτ, hcW]
      linarith
    · have hsne : t - t₀ ≠ 0 := sub_ne_zero.mpr ht0
      have hsn : 0 < |t - t₀| ^ n := pow_pos (abs_pos.mpr hsne) n
      intro hzero
      have hs0 : (t - t₀) ^ n • Vfac t + τ • W t + τ ^ 2 • Q t = 0 := by
        rw [← hzero, hfac1]
      have hsum : (t - t₀) ^ n • (Vfac t - A) + τ • (W t - W₀) + τ ^ 2 • Q t
          = -((t - t₀) ^ n • A + τ • W₀) := by
        refine eq_neg_iff_add_eq_zero.mpr ?_
        have h2 : (t - t₀) ^ n • Vfac t
            = (t - t₀) ^ n • A + (t - t₀) ^ n • (Vfac t - A) := by
          rw [← smul_add, add_sub_cancel]
        have h3 : τ • W t = τ • W₀ + τ • (W t - W₀) := by
          rw [← smul_add, add_sub_cancel]
        rw [h2, h3] at hs0
        rw [← hs0]
        abel
      have hYX : ‖(t - t₀) ^ n • A + τ • W₀‖
          = ‖(t - t₀) ^ n • (Vfac t - A) + τ • (W t - W₀) + τ ^ 2 • Q t‖ := by
        rw [hsum, norm_neg]
      have hlow : c * (|t - t₀| ^ n + τ)
          ≤ ‖(t - t₀) ^ n • A + τ • W₀‖ := by
        have h1 := hcone ((t - t₀) ^ n) τ hτpos.le
        rwa [abs_pow] at h1
      have hhigh : ‖(t - t₀) ^ n • (Vfac t - A) + τ • (W t - W₀) + τ ^ 2 • Q t‖
          ≤ (c / 2) * (|t - t₀| ^ n + τ) := by
        have e1 : ‖(t - t₀) ^ n • (Vfac t - A)‖ = |t - t₀| ^ n * ‖Vfac t - A‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_pow]
        have e2 : ‖τ • (W t - W₀)‖ = τ * ‖W t - W₀‖ := by
          rw [norm_smul, Real.norm_of_nonneg hτpos.le]
        have e3 : ‖τ ^ 2 • Q t‖ = τ ^ 2 * ‖Q t‖ := by
          rw [norm_smul, Real.norm_of_nonneg (by positivity)]
        have hsplit : ‖(t - t₀) ^ n • (Vfac t - A) + τ • (W t - W₀) + τ ^ 2 • Q t‖
            ≤ ‖(t - t₀) ^ n • (Vfac t - A)‖ + ‖τ • (W t - W₀)‖ + ‖τ ^ 2 • Q t‖ := by
          have h1 := norm_add_le ((t - t₀) ^ n • (Vfac t - A) + τ • (W t - W₀)) (τ ^ 2 • Q t)
          have h2 := norm_add_le ((t - t₀) ^ n • (Vfac t - A)) (τ • (W t - W₀))
          linarith
        rw [e1, e2, e3] at hsplit
        have hτMQ : τ ^ 2 * ‖Q t‖ ≤ τ * (c / 8) := by
          have h1 : τ * ‖Q t‖ ≤ τ * (‖Q t₀‖ + 1) := mul_le_mul_of_nonneg_left hQt hτpos.le
          have h2 : τ * (τ * ‖Q t‖) ≤ τ * (c / 8) := by
            exact mul_le_mul_of_nonneg_left (by linarith [hMQτ, h1]) hτpos.le
          nlinarith [h2, hτpos]
        nlinarith [hsplit, hVb', hWb', hτMQ, hcpos, hsn, hτpos]
      have hfin : (c / 2) * (|t - t₀| ^ n + τ) < c * (|t - t₀| ^ n + τ) := by
        have hpos : 0 < |t - t₀| ^ n + τ := by linarith
        nlinarith [hcpos, hpos]
      linarith [hYX, hlow, hhigh, hfin]


/-- **Core perturbation lemma.**  There are an analytic `period`-periodic `φ` and `τ₁ > 0` such
that for every `τ ∈ (0, τ₁)` the curve `r + τ φ` has nowhere vanishing curvature vector, i.e.
`velocity × acceleration` is nonzero for the perturbed curve. -/
private lemma exists_small_perturbation_nonvanishing {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ∃ (φ : ℝ → Space) (τ₁ : ℝ), ContDiff ℝ ⊤ φ ∧ Function.Periodic φ period ∧ 0 < τ₁ ∧
      ∀ τ ∈ Set.Ioo 0 τ₁, ∀ t : ℝ,
        cross3 (velocity r t + τ • deriv φ t) (accel r t + τ • deriv (deriv φ) t) ≠ 0 := by
  have h1 : (⊤ : WithTop ℕ∞) + 1 = ⊤ := by simp
  have hvel : ContDiff ℝ ⊤ (velocity r) := h1 ▸ hr.smooth.deriv'
  have hacc : ContDiff ℝ ⊤ (accel r) := h1 ▸ hvel.deriv'
  have hvper : Function.Periodic (velocity r) period := hr.velocity_periodic
  have haper : Function.Periodic (accel r) period := periodic_deriv' hvper
  have hVcont : Continuous (inflec r) := by
    show Continuous (fun t => cross3 (velocity r t) (accel r t))
    exact continuous_cross3 hvel.continuous hacc.continuous
  have hVper : Function.Periodic (inflec r) period := by
    intro t
    show cross3 (velocity r (t + period)) (accel r (t + period)) = cross3 (velocity r t) (accel r t)
    rw [hvper t, haper t]
  -- the finite set of inflection parameters in the fundamental period
  have hZfin : ({t : ℝ | t ∈ Set.Icc 0 period ∧ inflec r t = 0} ∩ Set.Ico 0 period).Finite :=
    (finite_inflection_set hr).subset Set.inter_subset_left
  set S : Finset ℝ := hZfin.toFinset with hSdef
  have hSmem : ∀ i : ℝ, i ∈ S ↔ inflec r i = 0 ∧ i ∈ Set.Ico 0 period := by
    intro i
    rw [hSdef, Set.Finite.mem_toFinset]
    exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨Set.Ico_subset_Icc_self h.2, h.1⟩, h.2⟩⟩
  have hSsub : ∀ i ∈ S, i ∈ Set.Ico 0 period := fun i hi => ((hSmem i).mp hi).2
  -- the local factor data and the perturbing curve
  let D : (i : ℝ) → i ∈ S → FactorData r i :=
    fun i hi => Classical.choice (exists_local_factorization hr ((hSmem i).mp hi).1)
  let B : ℝ → Space := fun i => if hi : i ∈ S then (D i hi).A else 0
  obtain ⟨φ, hφdiff, hφper, hφd1, hφd2⟩ := exists_trig_perturbation S hSsub B
  have hφ1diff : ContDiff ℝ ⊤ (deriv φ) := h1 ▸ hφdiff.deriv'
  have hφ2diff : ContDiff ℝ ⊤ (deriv (deriv φ)) := h1 ▸ hφ1diff.deriv'
  have hφ1per : Function.Periodic (deriv φ) period := periodic_deriv' hφper
  have hφ2per : Function.Periodic (deriv (deriv φ)) period := periodic_deriv' hφ1per
  have hφ1c : Continuous (deriv φ) := hφ1diff.continuous
  have hφ2c : Continuous (deriv (deriv φ)) := hφ2diff.continuous
  let W : ℝ → Space :=
    fun t => cross3 (deriv φ t) (accel r t) + cross3 (velocity r t) (deriv (deriv φ) t)
  let Q : ℝ → Space := fun t => cross3 (deriv φ t) (deriv (deriv φ) t)
  have hWc : Continuous W := by
    show Continuous (fun t =>
      cross3 (deriv φ t) (accel r t) + cross3 (velocity r t) (deriv (deriv φ) t))
    exact (continuous_cross3 hφ1c hacc.continuous).add (continuous_cross3 hvel.continuous hφ2c)
  have hQc : Continuous Q := by
    show Continuous (fun t => cross3 (deriv φ t) (deriv (deriv φ) t))
    exact continuous_cross3 hφ1c hφ2c
  have hWper : Function.Periodic W period := by
    intro t
    show cross3 (deriv φ (t + period)) (accel r (t + period))
        + cross3 (velocity r (t + period)) (deriv (deriv φ) (t + period))
      = cross3 (deriv φ t) (accel r t) + cross3 (velocity r t) (deriv (deriv φ) t)
    rw [hφ1per t, haper t, hvper t, hφ2per t]
  have hQper : Function.Periodic Q period := by
    intro t
    show cross3 (deriv φ (t + period)) (deriv (deriv φ) (t + period))
      = cross3 (deriv φ t) (deriv (deriv φ) t)
    rw [hφ1per t, hφ2per t]
  obtain ⟨MW, hMWpos, hMW⟩ := exists_norm_bound_of_periodic period_pos hWc hWper
  obtain ⟨MQ, hMQpos, hMQ⟩ := exists_norm_bound_of_periodic period_pos hQc hQper
  -- local non-vanishing near every inflection parameter
  have hstep : ∀ i : ℝ, ∃ τ₀ ρ : ℝ, i ∈ S → 0 < τ₀ ∧ 0 < ρ ∧
      ∀ τ ∈ Set.Ioo 0 τ₀, ∀ t : ℝ, |t - i| < ρ → inflec r t + τ • W t + τ ^ 2 • Q t ≠ 0 := by
    intro i
    by_cases hi : i ∈ S
    · obtain ⟨c, hc, hcφ⟩ := hφd2 i hi
      have hB : B i = (D i hi).A := by
        show (if hi : i ∈ S then (D i hi).A else 0) = (D i hi).A
        rw [dif_pos hi]
      have hφ2' : deriv (deriv φ) i = c • (D i hi).A := by rw [hcφ, hB]
      have hφ1' : deriv φ i = 0 := hφd1 i hi
      have hWi : W i = c • cross3 (velocity r i) (D i hi).A := by
        show cross3 (deriv φ i) (accel r i) + cross3 (velocity r i) (deriv (deriv φ) i) = _
        rw [hφ1', hφ2', cross3_zero_left, zero_add, cross3_smul_right]
      have hLI : LinearIndependent ℝ ![(D i hi).A, c • cross3 (velocity r i) (D i hi).A] :=
        li_of_cross3 (D i hi).hA (hr.regular i) (D i hi).horth hc rfl
      obtain ⟨τ₀, hτ₀, ρ', hρ', -, hnv⟩ :=
        local_nonvanishing (V := inflec r) (W := W) (Q := Q) (Vfac := (D i hi).fac) (t₀ := i)
          (n := (D i hi).n) (D i hi).hn (D i hi).hρ (D i hi).hfac_eq (D i hi).hcont
          (D i hi).hfac_t hWc.continuousAt hWi hLI hQc.continuousAt
      exact ⟨τ₀, ρ', fun _ => ⟨hτ₀, hρ', hnv⟩⟩
    · exact ⟨1, 1, fun h => absurd h hi⟩
  let τF : ℝ → ℝ := fun i => Classical.choose (hstep i)
  let ρF : ℝ → ℝ := fun i => Classical.choose (Classical.choose_spec (hstep i))
  have hτF : ∀ i ∈ S, 0 < τF i ∧ 0 < ρF i ∧
      ∀ τ ∈ Set.Ioo 0 (τF i), ∀ t : ℝ, |t - i| < ρF i →
        inflec r t + τ • W t + τ ^ 2 • Q t ≠ 0 :=
    fun i hi => (Classical.choose_spec (Classical.choose_spec (hstep i))) hi
  -- the compact set of parameters far from every inflection point and its translates
  let K : Set ℝ := {t : ℝ | t ∈ Set.Icc 0 period ∧
    ∀ i ∈ S, ∀ k : ℤ, ρF i ≤ |t - (i + k * period)|}
  have hKclosed : IsClosed K := by
    have hEq : K = Set.Icc 0 period ∩
        ⋂ (i : {x // x ∈ S}), ⋂ (k : ℤ), {t : ℝ | ρF i.1 ≤ |t - (i.1 + k * period)|} := by
      ext t
      simp only [K, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_Icc,
        Subtype.forall]
    rw [hEq]
    refine isClosed_Icc.inter (isClosed_iInter fun i => isClosed_iInter fun k => ?_)
    exact isClosed_le continuous_const ((continuous_id.sub continuous_const).abs)
  have hKcomp : IsCompact K := isCompact_Icc.of_isClosed_subset hKclosed (fun t ht => ht.1)
  have hVne : ∀ t ∈ K, inflec r t ≠ 0 := by
    intro t ht h0
    rcases lt_or_eq_of_le ht.1.2 with hlt | heq
    · have htS : t ∈ S := (hSmem t).mpr ⟨h0, ⟨ht.1.1, hlt⟩⟩
      have hcond := ht.2 t htS 0
      simp only [Int.cast_zero, zero_mul, add_zero, sub_self, abs_zero] at hcond
      exact absurd hcond (not_le.mpr (hτF t htS).2.1)
    · have h0' : inflec r 0 = 0 := by
        have h2 : inflec r (0 + period) = inflec r 0 := hVper 0
        rw [zero_add] at h2
        rw [← h2, ← heq]
        exact h0
      have h0S : (0 : ℝ) ∈ S := (hSmem 0).mpr ⟨h0', ⟨le_refl 0, period_pos⟩⟩
      have hcond := ht.2 0 h0S 1
      rw [heq] at hcond
      norm_num at hcond
      exact absurd hcond (not_le.mpr (hτF 0 h0S).2.1)
  have hKbound : ∃ c : ℝ, 0 < c ∧ ∀ t ∈ K, c ≤ ‖inflec r t‖ := by
    by_cases hKne : K.Nonempty
    · obtain ⟨t₀, ht₀, hmin⟩ := hKcomp.exists_isMinOn hKne hVcont.continuousOn.norm
      refine ⟨‖inflec r t₀‖, norm_pos_iff.mpr (hVne t₀ ht₀), fun t ht => hmin ht⟩
    · exact ⟨1, one_pos, fun t ht => absurd ⟨t, ht⟩ hKne⟩
  obtain ⟨c, hcpos, hcbound⟩ := hKbound
  -- the uniform threshold
  let τS : ℝ := if h : S.Nonempty then S.inf' h τF else 1
  have hτSpos : 0 < τS := by
    change 0 < (if h : S.Nonempty then S.inf' h τF else 1)
    split_ifs with h
    · exact (Finset.lt_inf'_iff h).mpr fun i hi => (hτF i hi).1
    · exact one_pos
  have hτSle : ∀ i ∈ S, τS ≤ τF i := by
    intro i hi
    change (if h : S.Nonempty then S.inf' h τF else 1) ≤ τF i
    split_ifs with h
    · exact Finset.inf'_le τF hi
    · exact absurd ⟨i, hi⟩ h
  refine ⟨φ, min 1 (min τS (c / (2 * (MW + MQ + 1)))), hφdiff, hφper, ?_, ?_⟩
  · exact lt_min one_pos (lt_min hτSpos (div_pos hcpos (by positivity)))
  · intro τ hτ t
    -- bilinearity: the perturbed curvature vector is `inflec + τ W + τ² Q`
    have hbil : ∀ (τ : ℝ) (t : ℝ),
        cross3 (velocity r t + τ • deriv φ t) (accel r t + τ • deriv (deriv φ) t)
          = inflec r t + τ • W t + τ ^ 2 • Q t := by
      intro τ t
      show cross3 (velocity r t + τ • deriv φ t) (accel r t + τ • deriv (deriv φ) t)
        = cross3 (velocity r t) (accel r t)
          + τ • (cross3 (deriv φ t) (accel r t) + cross3 (velocity r t) (deriv (deriv φ) t))
          + τ ^ 2 • cross3 (deriv φ t) (deriv (deriv φ) t)
      rw [cross3_add_left, cross3_add_right, cross3_add_right, cross3_smul_left,
        cross3_smul_left, cross3_smul_right, cross3_smul_right]
      simp only [smul_add, smul_smul, pow_two]
      abel
    have hFper : Function.Periodic (fun x : ℝ => inflec r x + τ • W x + τ ^ 2 • Q x) period := by
      intro x
      simp only [hVper x, hWper x, hQper x]
    obtain ⟨t₀, ht₀, ht₀eq⟩ := hFper.exists_mem_Ico period_pos t 0
    have ht₀' : t₀ ∈ Set.Ico 0 period := by simpa using ht₀
    have hkey : inflec r t₀ + τ • W t₀ + τ ^ 2 • Q t₀ ≠ 0 := by
      by_cases hcase : ∃ i ∈ S, ∃ k : ℤ, |t₀ - (i + k * period)| < ρF i
      · obtain ⟨i, hi, k, hk⟩ := hcase
        have hτ1min : min 1 (min τS (c / (2 * (MW + MQ + 1)))) ≤ τS :=
          le_trans (min_le_right _ _) (min_le_left _ _)
        have hτlt : τ < τF i := lt_of_lt_of_le (lt_of_lt_of_le hτ.2 hτ1min) (hτSle i hi)
        have hnv := (hτF i hi).2.2 τ ⟨hτ.1, hτlt⟩
        have hfac : (t₀ - k * period) - i = t₀ - (i + k * period) := by ring
        have hnv' := hnv (t₀ - k * period) (by rw [hfac]; exact hk)
        have htr : inflec r t₀ + τ • W t₀ + τ ^ 2 • Q t₀
            = inflec r (t₀ - k * period) + τ • W (t₀ - k * period)
              + τ ^ 2 • Q (t₀ - k * period) := by
          have hh := hFper.int_mul k (t₀ - k * period)
          have hx : t₀ - k * period + k * period = t₀ := by ring
          rw [hx] at hh
          simpa using hh
        rw [htr]; exact hnv'
      · have hKmem : t₀ ∈ K := ⟨Set.Ico_subset_Icc_self ht₀', fun i hi k => by
          by_contra hcon
          exact hcase ⟨i, hi, k, not_le.mp hcon⟩⟩
        have hVb := hcbound t₀ hKmem
        have hτ1le1 : τ ≤ 1 := le_of_lt (lt_of_lt_of_le hτ.2 (min_le_left _ _))
        have hτle : τ ≤ c / (2 * (MW + MQ + 1)) :=
          le_of_lt (lt_of_lt_of_le hτ.2
            (le_trans (min_le_right _ _) (min_le_right _ _)))
        have hWb := hMW t₀
        have hQb := hMQ t₀
        have hMs : (0 : ℝ) < MW + MQ + 1 := by linarith
        have hrest : ‖τ • W t₀ + τ ^ 2 • Q t₀‖ < c := by
          have h1 : ‖τ • W t₀ + τ ^ 2 • Q t₀‖ ≤ τ * MW + τ ^ 2 * MQ := by
            have hstep1 : ‖τ • W t₀ + τ ^ 2 • Q t₀‖ ≤ ‖τ • W t₀‖ + ‖τ ^ 2 • Q t₀‖ :=
              norm_add_le _ _
            have hstep2 : ‖τ • W t₀‖ = τ * ‖W t₀‖ := by
              rw [norm_smul, Real.norm_of_nonneg hτ.1.le]
            have hstep3 : ‖τ ^ 2 • Q t₀‖ = τ ^ 2 * ‖Q t₀‖ := by
              rw [norm_smul, Real.norm_of_nonneg (by positivity)]
            have hstep4 : τ * ‖W t₀‖ ≤ τ * MW := mul_le_mul_of_nonneg_left hWb hτ.1.le
            have hstep5 : τ ^ 2 * ‖Q t₀‖ ≤ τ ^ 2 * MQ :=
              mul_le_mul_of_nonneg_left hQb (by positivity)
            linarith
          have h2 : τ * MW + τ ^ 2 * MQ ≤ τ * MW + τ * MQ := by
            have h2a : τ ^ 2 ≤ τ := by nlinarith [hτ.1.le, hτ1le1]
            have h2b : τ ^ 2 * MQ ≤ τ * MQ := mul_le_mul_of_nonneg_right h2a hMQpos.le
            linarith
          have h3 : τ * MW + τ * MQ ≤ τ * (MW + MQ + 1) := by
            nlinarith [hτ.1.le, hMWpos, hMQpos]
          have h4 : τ * (MW + MQ + 1) ≤ c / 2 := by
            have h5 : (c / (2 * (MW + MQ + 1))) * (MW + MQ + 1) = c / 2 := by
              have hne : (2 * (MW + MQ + 1)) ≠ 0 := by linarith
              field_simp
            have h6 := mul_le_mul_of_nonneg_right hτle hMs.le
            rw [h5] at h6
            exact h6
          have h5 : c / 2 < c := by linarith
          linarith
        intro hzero
        have heq : ‖inflec r t₀‖ = ‖τ • W t₀ + τ ^ 2 • Q t₀‖ := by
          have h1 : inflec r t₀ = -(τ • W t₀ + τ ^ 2 • Q t₀) := by
            rw [eq_neg_iff_add_eq_zero, ← add_assoc]
            exact hzero
          rw [h1, norm_neg]
        linarith
    intro hcon
    exact hkey (by rw [← ht₀eq, ← hbil τ t, hcon])


/-- **Every smooth knot has `C²`-close perturbations with nowhere vanishing curvature.** -/
theorem exists_close_nonzero_curvature_c2 {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r) (ε : ℝ) (hε : 0 < ε) :
    ∃ r' : ℝ → LeanEval.KnotTheory.Quadrisecant.Space,
      LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r' ∧
      (∀ t : ℝ, LinearIndependent ℝ
        ![LeanEval.KnotTheory.Quadrisecant.velocity r' t,
          deriv (LeanEval.KnotTheory.Quadrisecant.velocity r') t]) ∧
      ∀ t : ℝ, ‖r' t - r t‖ < ε ∧
        ‖LeanEval.KnotTheory.Quadrisecant.velocity r' t -
          LeanEval.KnotTheory.Quadrisecant.velocity r t‖ < ε ∧
        ‖deriv (deriv r') t - deriv (deriv r) t‖ < ε := by
  obtain ⟨ε₁, hε₁pos, hε₁⟩ := smallCorrectionKnot hr
  obtain ⟨φ, τ₁, hφdiff, hφper, hτ₁pos, hφnv⟩ := exists_small_perturbation_nonvanishing hr
  have h1 : (⊤ : WithTop ℕ∞) + 1 = ⊤ := by simp
  have hvel : ContDiff ℝ ⊤ (velocity r) := h1 ▸ hr.smooth.deriv'
  have hφ1diff : ContDiff ℝ ⊤ (deriv φ) := h1 ▸ hφdiff.deriv'
  have hφ2diff : ContDiff ℝ ⊤ (deriv (deriv φ)) := h1 ▸ hφ1diff.deriv'
  have hφ1per : Function.Periodic (deriv φ) period := periodic_deriv' hφper
  have hφ2per : Function.Periodic (deriv (deriv φ)) period := periodic_deriv' hφ1per
  obtain ⟨Mφ, hMφpos, hMφ⟩ := exists_norm_bound_of_periodic period_pos hφdiff.continuous hφper
  obtain ⟨Mφ', hMφ'pos, hMφ'⟩ :=
    exists_norm_bound_of_periodic period_pos hφ1diff.continuous hφ1per
  obtain ⟨Mφ'', hMφ''pos, hMφ''⟩ :=
    exists_norm_bound_of_periodic period_pos hφ2diff.continuous hφ2per
  set c1 : ℝ := ε / (2 * (Mφ + 1)) with hc1
  set c2 : ℝ := ε / (2 * (Mφ' + 1)) with hc2
  set c3 : ℝ := ε / (2 * (Mφ'' + 1)) with hc3
  set c4 : ℝ := ε₁ / (2 * (Mφ + 1)) with hc4
  set c5 : ℝ := ε₁ / (2 * (Mφ' + 1)) with hc5
  set c6 : ℝ := τ₁ / 2 with hc6
  set τ : ℝ := min c1 (min c2 (min c3 (min c4 (min c5 c6)))) with hτ
  have hτpos : 0 < τ := by
    rw [hτ]
    refine lt_min ?_ (lt_min ?_ (lt_min ?_ (lt_min ?_ (lt_min ?_ ?_))))
    · rw [hc1]; positivity
    · rw [hc2]; positivity
    · rw [hc3]; positivity
    · rw [hc4]; positivity
    · rw [hc5]; positivity
    · rw [hc6]; linarith
  have hτc1 : τ ≤ c1 := by rw [hτ]; exact min_le_left _ _
  have hτc2 : τ ≤ c2 := by
    rw [hτ]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hτc3 : τ ≤ c3 := by
    rw [hτ]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hτc4 : τ ≤ c4 := by
    rw [hτ]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hτc5 : τ ≤ c5 := by
    rw [hτ]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hτc6 : τ ≤ c6 := by
    rw [hτ]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))))
  have hττ₁ : τ < τ₁ := by rw [hc6] at hτc6; linarith
  -- smallness of `τ` against each of the continuous bounds
  have hbd : ∀ (b M C : ℝ), b = C / (2 * (M + 1)) → 0 < M → τ ≤ b → τ * M < C := by
    intro b M C hbeq hM htb
    have h4 : τ * (M + 1) ≤ C / 2 := by
      have h5 : (C / (2 * (M + 1))) * (M + 1) = C / 2 := by
        have hne : (2 * (M + 1)) ≠ 0 := by positivity
        field_simp
      have h6 := mul_le_mul_of_nonneg_right (hbeq ▸ htb) (by positivity : (0:ℝ) ≤ M + 1)
      rwa [h5] at h6
    nlinarith [hτpos, hM, h4]
  have hτc1' : τ * Mφ < ε := hbd c1 Mφ ε hc1 hMφpos hτc1
  have hτc2' : τ * Mφ' < ε := hbd c2 Mφ' ε hc2 hMφ'pos hτc2
  have hτc3' : τ * Mφ'' < ε := hbd c3 Mφ'' ε hc3 hMφ''pos hτc3
  have hτc4' : τ * Mφ < ε₁ := hbd c4 Mφ ε₁ hc4 hMφpos hτc4
  have hτc5' : τ * Mφ' < ε₁ := hbd c5 Mφ' ε₁ hc5 hMφ'pos hτc5
  -- the perturbed curve
  have hderiv_r' : ∀ t : ℝ, deriv (fun s : ℝ => r s + τ • φ s) t = velocity r t + τ • deriv φ t := by
    intro t
    have h2 : HasDerivAt (fun s : ℝ => r s + τ • φ s) (velocity r t + τ • deriv φ t) t :=
      ((hr.smooth.differentiable (by decide) t).hasDerivAt).add
        (((hφdiff.differentiable (by decide) t).hasDerivAt).const_smul τ)
    exact h2.deriv
  have hvel_eq : velocity (fun s : ℝ => r s + τ • φ s) = fun s => velocity r s + τ • deriv φ s :=
    funext hderiv_r'
  have hderiv_v' : ∀ t : ℝ, deriv (velocity (fun s : ℝ => r s + τ • φ s)) t
      = accel r t + τ • deriv (deriv φ) t := by
    intro t
    rw [hvel_eq]
    have h2 : HasDerivAt (fun s : ℝ => velocity r s + τ • deriv φ s)
        (accel r t + τ • deriv (deriv φ) t) t :=
      ((hvel.differentiable (by decide) t).hasDerivAt).add
        (((hφ1diff.differentiable (by decide) t).hasDerivAt).const_smul τ)
    exact h2.deriv
  have hderiv2 : ∀ t : ℝ, deriv (deriv (fun s : ℝ => r s + τ • φ s)) t
      = deriv (deriv r) t + τ • deriv (deriv φ) t := by
    intro t
    have hfun : deriv (fun s : ℝ => r s + τ • φ s)
        = fun s : ℝ => deriv r s + τ • deriv φ s := by
      funext s
      simpa only [velocity] using hderiv_r' s
    rw [hfun]
    have h2 : HasDerivAt (fun s : ℝ => deriv r s + τ • deriv φ s)
        (deriv (deriv r) t + τ • deriv (deriv φ) t) t :=
      ((hvel.differentiable (by decide) t).hasDerivAt).add
        (((hφ1diff.differentiable (by decide) t).hasDerivAt).const_smul τ)
    exact h2.deriv
  have hwper : Function.Periodic (fun t : ℝ => τ • φ t) period := by
    intro t
    simp only [hφper t]
  have hwvel : ∀ t : ℝ, velocity (fun s : ℝ => τ • φ s) t = τ • deriv φ t := by
    intro t
    exact (((hφdiff.differentiable (by decide) t).hasDerivAt).const_smul τ).deriv
  refine ⟨fun t => r t + τ • φ t, ?_, ?_, ?_⟩
  · -- the perturbed curve is a smooth knot
    refine hε₁ _ (ContDiff.const_smul τ hφdiff) hwper ?_
    intro t
    constructor
    · show ‖τ • φ t‖ < ε₁
      rw [norm_smul, Real.norm_of_nonneg hτpos.le]
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hMφ t) hτpos.le) hτc4'
    · rw [hwvel t, norm_smul, Real.norm_of_nonneg hτpos.le]
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hMφ' t) hτpos.le) hτc5'
  · -- nowhere vanishing curvature
    intro t
    rw [← cross3_ne_zero_iff_linearIndependent_local]
    show cross3 (deriv (fun s : ℝ => r s + τ • φ s) t)
      (deriv (velocity (fun s : ℝ => r s + τ • φ s)) t) ≠ 0
    rw [hderiv_r' t, hderiv_v' t]
    exact hφnv τ ⟨hτpos, hττ₁⟩ t
  · -- closeness, now including the second derivative
    intro t
    refine ⟨?_, ?_, ?_⟩
    · have h2 : (fun s : ℝ => r s + τ • φ s) t - r t = τ • φ t := by
        show r t + τ • φ t - r t = τ • φ t
        rw [add_sub_cancel_left]
      rw [h2, norm_smul, Real.norm_of_nonneg hτpos.le]
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hMφ t) hτpos.le) hτc1'
    · show ‖deriv (fun s : ℝ => r s + τ • φ s) t - velocity r t‖ < ε
      rw [hderiv_r' t, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hτpos.le]
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hMφ' t) hτpos.le) hτc2'
    · have h3 : deriv (deriv (fun s : ℝ => r s + τ • φ s)) t - deriv (deriv r) t
          = τ • deriv (deriv φ) t := by
        rw [hderiv2 t]
        abel
      rw [h3, norm_smul, Real.norm_of_nonneg hτpos.le]
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hMφ'' t) hτpos.le) hτc3'

end Work.Drive
