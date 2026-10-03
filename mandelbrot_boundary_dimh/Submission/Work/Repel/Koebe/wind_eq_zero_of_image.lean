import Mathlib
import Submission.Work.Repel.Koebe.Setup
import Submission.Work.Repel.Koebe.ExteriorWindingDefs
import Submission.Lib.Unif2.Commons.Analysis.Complex.circleIntegral_logDeriv_eq_divisor
import Submission.Lib.Unif2.Commons.Analysis.Complex.circleIntegral_logDeriv_eq_zero_of_ne_zero
import Submission.Lib.Unif2.Commons.Analysis.Complex.zeroFactor_g
import Submission.Lib.Unif2.Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn

open MeasureTheory Filter Topology Complex
open scoped Topology BigOperators

namespace Work.Repel.Koebe

/-- Algebraic identity underlying the change of variables `v ↦ v⁻¹` inside a circle integral. -/
private lemma smul_inv_key (c x : ℂ) (hc : c ≠ 0) :
    (c * I) * ((c ^ 2)⁻¹ * x) = (c⁻¹ * I) * x := by
  field_simp

/-- **Change of variables `v ↦ v⁻¹` in a circle integral.**  Integrating `K` over the circle of
radius `ρ⁻¹` is the same as integrating `K (v⁻¹) / v²` over the circle of radius `ρ`. -/
lemma circleIntegral_inv_comp {K : ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ) :
    (∮ v in C(0, ρ), (v ^ 2)⁻¹ * K v⁻¹) = ∮ z in C(0, ρ⁻¹), K z := by
  rw [circleIntegral, circleIntegral]
  set g : ℝ → ℂ := fun s => deriv (circleMap 0 ρ⁻¹) s • K (circleMap 0 ρ⁻¹ s) with hg
  have hcv := intervalIntegral.integral_comp_sub_left (a := 0) (b := 2 * Real.pi) g (2 * Real.pi)
  rw [show (2:ℝ) * Real.pi - 2 * Real.pi = 0 from by ring,
      show (2:ℝ) * Real.pi - 0 = 2 * Real.pi from by ring] at hcv
  rw [← hcv]
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [hg]
  rw [deriv_circleMap, deriv_circleMap]
  have hcm : circleMap 0 ρ⁻¹ (2 * Real.pi - θ) = (circleMap 0 ρ θ)⁻¹ := by
    rw [circleMap_zero_inv]
    have h2 : (2 * Real.pi - θ) = -θ + 2 * Real.pi := by ring
    rw [h2]
    exact periodic_circleMap 0 ρ⁻¹ (-θ)
  rw [hcm]
  have hc : circleMap 0 ρ θ ≠ 0 := by
    rw [circleMap_zero]
    exact mul_ne_zero (ofReal_ne_zero.mpr hρ.ne') (Complex.exp_ne_zero _)
  exact smul_inv_key _ _ hc

/-- **`Phi` is analytic on the unit disc, from a bound on `g z - z` at infinity.** -/
lemma analyticOnNhd_Phi_of_bound {g : ℂ → ℂ} {ζ : ℂ}
    (hg : ∀ z : ℂ, 1 < ‖z‖ → AnalyticAt ℂ g z)
    (hbound : ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, R ≤ ‖z‖ → ‖g z - z‖ ≤ 1 / 2) :
    AnalyticOnNhd ℂ (Phi g ζ) (Metric.ball 0 1) := by
  obtain ⟨R, hRpos, hRb⟩ := hbound
  have han : ∀ v ∈ Metric.ball 0 1, v ≠ 0 → AnalyticAt ℂ (Phi g ζ) v := by
    intro v hv1 hv0
    have hphi := analyticAt_phi_of_ne hg hv0 (by simpa [Metric.mem_ball, dist_zero_right] using hv1)
    change AnalyticAt ℂ (fun w : ℂ => w * phi g w + 1 - w * ζ) v
    exact ((analyticAt_id.mul hphi).add (analyticAt_const (v := (1:ℂ)))).sub
      (analyticAt_id.mul (analyticAt_const (v := ζ)))
  have hcont : ContinuousAt (Phi g ζ) 0 := by
    rw [Metric.continuousAt_iff]
    intro ε hε
    refine ⟨min (1 / (R + 1)) (ε / (‖ζ‖ + 1)), lt_min (by positivity) (by positivity), ?_⟩
    intro v hv
    rw [dist_eq_norm, sub_zero] at hv
    have hv1 : ‖v‖ < 1 / (R + 1) := lt_of_lt_of_le hv (min_le_left _ _)
    have hv2 : ‖v‖ < ε / (‖ζ‖ + 1) := lt_of_lt_of_le hv (min_le_right _ _)
    have hphiB : ‖phi g v‖ ≤ 1 / 2 := by
      rcases eq_or_ne v 0 with rfl | hv0
      · simp [phi_zero]
      · rw [phi_apply hv0]
        refine hRb v⁻¹ ?_
        rw [norm_inv]
        have hlt : R + 1 < ‖v‖⁻¹ := by
          have h := one_div_lt_one_div_of_lt (show (0:ℝ) < ‖v‖ from norm_pos_iff.mpr hv0) hv1
          simpa [one_div, inv_inv] using h
        linarith
    have hval : Phi g ζ v - 1 = v * (phi g v - ζ) := by
      simp only [Phi]; ring
    rw [show Phi g ζ 0 = 1 from Phi_zero g ζ]
    rw [dist_eq_norm, hval, norm_mul]
    have h1 : ‖phi g v - ζ‖ ≤ 1 / 2 + ‖ζ‖ := by
      calc ‖phi g v - ζ‖ ≤ ‖phi g v‖ + ‖ζ‖ := norm_sub_le _ _
        _ ≤ 1 / 2 + ‖ζ‖ := by linarith
    have h2 : ‖v‖ * (1 / 2 + ‖ζ‖) < ε := by
      have hz1 : 0 < ‖ζ‖ + 1 := by linarith [norm_nonneg ζ]
      have hpos : 0 < 1 / 2 + ‖ζ‖ := by linarith [norm_nonneg ζ]
      calc ‖v‖ * (1 / 2 + ‖ζ‖) < (ε / (‖ζ‖ + 1)) * (1 / 2 + ‖ζ‖) :=
            mul_lt_mul_of_pos_right hv2 hpos
        _ ≤ (ε / (‖ζ‖ + 1)) * (‖ζ‖ + 1) :=
            mul_le_mul_of_nonneg_left (by linarith [norm_nonneg ζ]) (by positivity)
        _ = ε := by rw [div_mul_cancel₀ ε (ne_of_gt hz1)]
    calc ‖v‖ * ‖phi g v - ζ‖ ≤ ‖v‖ * (1 / 2 + ‖ζ‖) := mul_le_mul_of_nonneg_left h1 (norm_nonneg v)
      _ < ε := h2
  intro v hv
  rcases eq_or_ne v 0 with rfl | hv0
  · refine Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ hcont
    have hb : Metric.ball (0:ℂ) 1 ∈ 𝓝[≠] (0:ℂ) :=
      Filter.mem_inf_of_left (Metric.ball_mem_nhds (0:ℂ) one_pos)
    filter_upwards [hb, self_mem_nhdsWithin] with w hw hw0
    exact (han w hw hw0).differentiableAt
  · exact han v hv hv0

/-- **Derivative of `Phi` at `v = z₀⁻¹`.**  For `z₀ ≠ 0` with `g` analytic at `z₀`,
`deriv (Phi g ζ) z₀⁻¹ = (g z₀ - ζ) - z₀ · deriv g z₀`. -/
lemma deriv_Phi_inv {g : ℂ → ℂ} {ζ : ℂ} {z₀ : ℂ} (hz₀ : 0 < ‖z₀‖) (hg : AnalyticAt ℂ g z₀) :
    deriv (Phi g ζ) z₀⁻¹ = (g z₀ - ζ) - z₀ * deriv g z₀ := by
  have hz₀ne : z₀ ≠ 0 := norm_pos_iff.mp hz₀
  have hvne : z₀⁻¹ ≠ 0 := inv_ne_zero hz₀ne
  have hev : Phi g ζ =ᶠ[𝓝 z₀⁻¹] fun w : ℂ => w * (g w⁻¹ - ζ) := by
    filter_upwards [isOpen_ne.mem_nhds hvne] with w hw
    exact Phi_apply g ζ hw
  rw [hev.deriv_eq]
  have hG : HasDerivAt (fun w : ℂ => g w⁻¹ - ζ)
      (deriv g z₀ * (-(z₀⁻¹ ^ 2)⁻¹)) z₀⁻¹ := by
    have hg' : HasDerivAt g (deriv g z₀) ((fun y : ℂ => y⁻¹) z₀⁻¹) := by
      simpa [inv_inv] using hg.differentiableAt.hasDerivAt
    have h2 := hg'.comp (z₀⁻¹) (hasDerivAt_inv hvne)
    have h3 := h2.sub_const ζ
    convert h3 using 2
    simp
  have hF : HasDerivAt (fun w : ℂ => w * (g w⁻¹ - ζ))
      (1 * (g z₀⁻¹⁻¹ - ζ) + z₀⁻¹ * (deriv g z₀ * (-(z₀⁻¹ ^ 2)⁻¹))) z₀⁻¹ :=
    (hasDerivAt_id z₀⁻¹).mul hG
  rw [hF.deriv]
  simp only [inv_inv, one_mul]
  field_simp
  ring

/-- **Pointwise change of variables for the logarithmic derivative under inversion.** -/
lemma logDeriv_comp_inv {g : ℂ → ℂ} {ζ : ℂ} {v : ℂ}
    (hv : v ≠ 0) (hvn : ‖v‖ < 1) (hg : AnalyticAt ℂ g v⁻¹) (hne : g v⁻¹ ≠ ζ) :
    logDeriv (fun w : ℂ => g w - ζ) v⁻¹ * (v ^ 2)⁻¹ = v⁻¹ - logDeriv (Phi g ζ) v := by
  have hdiffv : DifferentiableAt ℂ (fun w : ℂ => g w⁻¹ - ζ) v :=
    ((hg.differentiableAt).comp v (differentiableAt_inv hv)).sub_const ζ
  have hcomp : logDeriv (fun w : ℂ => g w⁻¹ - ζ) v
      = logDeriv (fun w : ℂ => g w - ζ) v⁻¹ * deriv (fun w : ℂ => w⁻¹) v := by
    have h := logDeriv_comp (f := fun w : ℂ => g w - ζ) (g := fun w : ℂ => w⁻¹) (x := v)
      ((hg.sub analyticAt_const).differentiableAt) (differentiableAt_inv hv)
    exact h
  rw [deriv_inv] at hcomp
  have hev : Phi g ζ =ᶠ[𝓝 v] fun w : ℂ => w * (g w⁻¹ - ζ) := by
    filter_upwards [isOpen_ne.mem_nhds hv] with w hw
    exact Phi_apply g ζ hw
  have hlogPhi : logDeriv (Phi g ζ) v
      = v⁻¹ + logDeriv (fun w : ℂ => g w⁻¹ - ζ) v := by
    have hΦ : logDeriv (Phi g ζ) v
        = logDeriv ((fun w : ℂ => w) * (fun w : ℂ => g w⁻¹ - ζ)) v := by
      rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.self_of_nhds]
      rfl
    rw [hΦ, logDeriv_mul (f := fun w : ℂ => w) (g := fun w : ℂ => g w⁻¹ - ζ) v hv
      (sub_ne_zero.mpr hne) differentiableAt_id hdiffv, logDeriv_id', one_div]
  rw [hlogPhi, hcomp]
  field_simp
  ring

/-- **Winding number of a univalent exterior map about a value it takes outside the curve.**

Let `g` be analytic and injective on the exterior `{1 < ‖z‖}` of the unit disc, and suppose
`‖g z - z‖ ≤ 1/2` for all large `z`.  If `ζ = g z₀` for some `z₀` with `r < ‖z₀‖` and `1 < r`,
then the winding number of the curve `z ↦ g z`, `‖z‖ = r`, about `ζ` vanishes. -/
theorem wind_eq_zero_of_image {g : ℂ → ℂ} {ζ : ℂ} {r : ℝ} {z₀ : ℂ} (hr : 1 < r)
    (hg : ∀ z : ℂ, 1 < ‖z‖ → AnalyticAt ℂ g z)
    (hbound : ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ‖g z - z‖ ≤ 1 / 2)
    (hinj : Set.InjOn g {z : ℂ | 1 < ‖z‖}) (hz₀ : r < ‖z₀‖) (hval : g z₀ = ζ) :
    wind g r ζ = 0 := by
  obtain ⟨R₀, hR₀⟩ := hbound
  have hbound' : ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, R ≤ ‖z‖ → ‖g z - z‖ ≤ 1 / 2 :=
    ⟨max R₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _),
      fun z hz => hR₀ z (le_trans (le_max_left _ _) hz)⟩
  have hr0 : 0 < r := lt_trans one_pos hr
  have hz₀pos : 0 < ‖z₀‖ := lt_trans hr0 hz₀
  have hz₀ne : z₀ ≠ 0 := norm_pos_iff.mp hz₀pos
  have hz₀one : 1 < ‖z₀‖ := lt_trans hr hz₀
  have hgz₀ : AnalyticAt ℂ g z₀ := hg z₀ hz₀one
  set ρ : ℝ := 1 / r with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; positivity
  have hρlt : ρ < 1 := by rw [hρdef, one_div]; exact inv_lt_one_of_one_lt₀ hr
  set v₀ : ℂ := z₀⁻¹ with hv₀def
  have hv₀norm : ‖v₀‖ < ρ := by
    rw [hv₀def, hρdef, norm_inv, one_div]
    exact (inv_lt_inv₀ hz₀pos hr0).mpr hz₀
  -- Phi is analytic on the unit disc, hence on ball 0 R₁ for ρ < R₁ < 1
  have hPhi_an : AnalyticOnNhd ℂ (Phi g ζ) (Metric.ball 0 1) := analyticOnNhd_Phi_of_bound hg hbound'
  set R₁ : ℝ := (ρ + 1) / 2 with hR₁def
  have hρR₁ : ρ < R₁ := by rw [hR₁def]; linarith
  have hR₁1 : R₁ < 1 := by rw [hR₁def]; linarith
  have hPhi_an₁ : AnalyticOnNhd ℂ (Phi g ζ) (Metric.ball 0 R₁) :=
    hPhi_an.mono (Metric.ball_subset_ball hR₁1.le)
  -- Phi does not vanish on the circle of radius ρ
  have hPhi_ne : ∀ z ∈ Metric.sphere (0:ℂ) ρ, Phi g ζ z ≠ 0 := by
    intro z hz hzero
    have hzn : ‖z‖ = ρ := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
    have hzne : z ≠ 0 := by intro h; rw [h, norm_zero] at hzn; linarith [hρpos]
    rw [Phi_apply g ζ hzne] at hzero
    rcases mul_eq_zero.mp hzero with h | h
    · exact hzne h
    · have hgz : g z⁻¹ = ζ := sub_eq_zero.mp h
      have h1 : 1 < ‖z⁻¹‖ := by
        rw [norm_inv, hzn, hρdef, one_div, inv_inv]; exact hr
      have heq : z⁻¹ = z₀ := hinj h1 hz₀one (by rw [hgz, hval])
      have hnormz : ‖z⁻¹‖ = r := by rw [norm_inv, hzn, hρdef, one_div, inv_inv]
      have : ‖z₀‖ = r := by rw [← heq, hnormz]
      linarith [hz₀]
  -- the divisor of Phi on ball 0 ρ is the Dirac mass at v₀
  have hv₀_mem : v₀ ∈ Metric.ball (0:ℂ) ρ := by
    rw [Metric.mem_ball, dist_zero_right]; exact hv₀norm
  have hPhi_v₀ : Phi g ζ v₀ = 0 := by
    rw [hv₀def, Phi_apply g ζ (inv_ne_zero hz₀ne), inv_inv, hval]; ring
  have hderivg : deriv g z₀ ≠ 0 := by
    refine Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn (r := ‖z₀‖ - 1)
      (by linarith) hgz₀ (hinj.mono ?_)
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    rw [Set.mem_setOf_eq]
    have h1 : ‖z₀‖ ≤ ‖z₀ - w‖ + ‖w‖ := by
      calc ‖z₀‖ = ‖(z₀ - w) + w‖ := by ring_nf
        _ ≤ ‖z₀ - w‖ + ‖w‖ := norm_add_le _ _
    have h2 : ‖z₀ - w‖ = ‖w - z₀‖ := norm_sub_rev z₀ w
    linarith
  have hderivPhi : deriv (Phi g ζ) v₀ ≠ 0 := by
    have h : deriv (Phi g ζ) z₀⁻¹ = (g z₀ - ζ) - z₀ * deriv g z₀ :=
      deriv_Phi_inv (ζ := ζ) hz₀pos hgz₀
    rw [hv₀def, h, hval, sub_self, zero_sub, neg_ne_zero]
    exact mul_ne_zero hz₀ne hderivg
  have hΦ_at_v₀ : AnalyticAt ℂ (Phi g ζ) v₀ :=
    hPhi_an₁ v₀ (by rw [Metric.mem_ball, dist_zero_right]; exact lt_trans hv₀norm hρR₁)
  have hord : meromorphicOrderAt (Phi g ζ) v₀ = 1 := by
    rw [hΦ_at_v₀.meromorphicOrderAt_eq,
      AnalyticAt.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hΦ_at_v₀ hPhi_v₀ hderivPhi]
    simp
  have hPhi_mero : MeromorphicOn (Phi g ζ) (Metric.ball (0:ℂ) ρ) :=
    (hPhi_an₁.mono (Metric.ball_subset_ball hρR₁.le)).meromorphicOn
  have hdiv : ∀ u : ℂ, (MeromorphicOn.divisor (Phi g ζ) (Metric.ball (0:ℂ) ρ)) u
      = if u = v₀ then 1 else 0 := by
    intro u
    rw [MeromorphicOn.divisor_def]
    by_cases hu : u ∈ Metric.ball (0:ℂ) ρ
    · rw [if_pos ⟨hPhi_mero, hu⟩]
      by_cases huv : u = v₀
      · rw [huv, hord, if_pos rfl]; rfl
      · rw [if_neg huv]
        have hne : Phi g ζ u ≠ 0 := by
          rcases eq_or_ne u 0 with rfl | hu0
          · rw [Phi_zero]; norm_num
          · rw [Phi_apply g ζ hu0]
            intro hzero
            rcases mul_eq_zero.mp hzero with h | h
            · exact hu0 h
            · have hgu : g u⁻¹ = ζ := sub_eq_zero.mp h
              have h1 : 1 < ‖u⁻¹‖ := by
                rw [norm_inv]
                refine (one_lt_inv₀ (norm_pos_iff.mpr hu0)).mpr ?_
                rw [Metric.mem_ball, dist_zero_right] at hu
                linarith [hu, hρlt]
              have heq : u⁻¹ = z₀ := hinj h1 hz₀one (by rw [hgu, hval])
              exact huv (by rw [hv₀def, ← heq, inv_inv])
        have huan : AnalyticAt ℂ (Phi g ζ) u := hPhi_an₁ u (Metric.ball_subset_ball hρR₁.le hu)
        rw [Commons.Analysis.Complex.meromorphicOrderAt_eq_zero_of_ne_zero huan hne]
        rfl
    · have huv : u ≠ v₀ := fun h => hu (by rw [h]; exact hv₀_mem)
      rw [if_neg (fun hcon => hu hcon.2), if_neg huv]
  have hfinsum : (∑ᶠ u : ℂ, ((MeromorphicOn.divisor (Phi g ζ) (Metric.ball (0:ℂ) ρ)) u : ℂ)) = 1 := by
    rw [finsum_eq_single _ v₀ (fun u hu => by rw [hdiv u, if_neg hu]; simp)]
    rw [hdiv v₀, if_pos rfl]; norm_num
  have hI : (∮ v in C(0, ρ), logDeriv (Phi g ζ) v) = 2 * ↑Real.pi * Complex.I := by
    rw [Commons.Analysis.Complex.circleIntegral_logDeriv_eq_divisor hρpos hρR₁ hPhi_an₁ hPhi_ne,
      hfinsum]
    ring
  -- wind g r ζ = (2πi)⁻¹ ∮ logDeriv (g - ζ)
  have hwind : wind g r ζ = (2 * ↑Real.pi * Complex.I)⁻¹ *
      (∮ z in C(0, r), logDeriv (fun w : ℂ => g w - ζ) z) := by
    rw [wind]
    congr 1
    apply circleIntegral.integral_congr hr0.le
    intro z hz
    rw [logDeriv_apply, deriv_sub_const]
  have hρinv : ρ⁻¹ = r := by rw [hρdef, one_div, inv_inv]
  have hCV := circleIntegral_inv_comp (K := fun z : ℂ => logDeriv (fun w : ℂ => g w - ζ) z) hρpos
  rw [hρinv] at hCV
  have hpt : ∀ v ∈ Metric.sphere (0:ℂ) ρ,
      (v ^ 2)⁻¹ * logDeriv (fun w : ℂ => g w - ζ) v⁻¹ = v⁻¹ - logDeriv (Phi g ζ) v := by
    intro v hv
    have hvn : ‖v‖ = ρ := by simpa [Metric.mem_sphere, dist_eq_norm] using hv
    have hvne : v ≠ 0 := by intro h; rw [h, norm_zero] at hvn; linarith [hρpos]
    have hv1 : ‖v‖ < 1 := by rw [hvn]; exact hρlt
    have hgan : AnalyticAt ℂ g v⁻¹ := by
      refine hg v⁻¹ ?_
      rw [norm_inv, hvn, hρdef, one_div, inv_inv]; exact hr
    have hne : g v⁻¹ ≠ ζ := by
      intro hcon
      have h1 : 1 < ‖v⁻¹‖ := by rw [norm_inv, hvn, hρdef, one_div, inv_inv]; exact hr
      have heq : v⁻¹ = z₀ := hinj h1 hz₀one (by rw [hcon, hval])
      have hv_eq : v = v₀ := by rw [hv₀def, ← heq, inv_inv]
      rw [hv_eq] at hvn
      linarith [hv₀norm, hvn]
    rw [mul_comm]
    exact logDeriv_comp_inv hvne hv1 hgan hne
  have hci1 : CircleIntegrable (fun v : ℂ => v⁻¹) 0 ρ := by
    refine ContinuousOn.circleIntegrable hρpos.le ?_
    refine ContinuousOn.inv₀ continuousOn_id ?_
    intro v hv
    have hvn : ‖v‖ = ρ := by simpa [Metric.mem_sphere, dist_eq_norm] using hv
    intro h0
    rw [h0, norm_zero] at hvn
    linarith [hρpos]
  have hci2 : CircleIntegrable (fun v : ℂ => logDeriv (Phi g ζ) v) 0 ρ := by
    refine ContinuousOn.circleIntegrable hρpos.le ?_
    have hsub : Metric.sphere (0:ℂ) ρ ⊆ Metric.ball (0:ℂ) R₁ := Metric.sphere_subset_ball hρR₁
    have hderiv : ContinuousOn (deriv (Phi g ζ)) (Metric.sphere (0:ℂ) ρ) :=
      (hPhi_an₁.deriv.continuousOn).mono hsub
    have hcont : ContinuousOn (Phi g ζ) (Metric.sphere (0:ℂ) ρ) :=
      hPhi_an₁.continuousOn.mono hsub
    have hthis : ContinuousOn (fun v : ℂ => deriv (Phi g ζ) v / Phi g ζ v) (Metric.sphere (0:ℂ) ρ) :=
      hderiv.div hcont hPhi_ne
    simpa only [logDeriv_apply] using hthis
  have hkey : (∮ z in C(0, r), logDeriv (fun w : ℂ => g w - ζ) z) = 0 := by
    rw [← hCV, circleIntegral.integral_congr hρpos.le hpt,
      circleIntegral.integral_sub hci1 hci2]
    rw [show (∮ v in C(0, ρ), v⁻¹) = 2 * ↑Real.pi * Complex.I from by
      simpa using circleIntegral.integral_sub_center_inv (0:ℂ) (ne_of_gt hρpos), hI]
    ring
  rw [hwind, hkey]
  ring

end Work.Repel.Koebe
