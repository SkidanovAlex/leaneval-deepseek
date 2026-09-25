/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Real analyticity of the truncated Cauchy transform of an analytic function

This file proves `Work.NN.Core.TelTwoDF.analyticOn_cauchyTransform_disc`.

The route implemented here is *subtraction using a fibre `∂̄`-primitive*, which avoids both the
moment computation and any division of real analytic functions:

* `Work.NN.Core.TelTwoDF.exists_analytic_fibre_dbar_primitive` provides, near the pole, a real
  analytic `A` with `g (update z s w) = ∂̄_w (A (z, ·)) w`;
* `Work.NN.Core.TelTwoDF.integral_cut_dbarC_div` (a cut version of the Pompeiu formula) evaluates
  `∫ χ w * ∂̄A w / (w - a)` as the *point value* `-π A a` plus an integral in which the pole is
  shielded by `∂̄χ`;
* cutting the disc into a small disc around the pole and its complement, and moving the surviving
  pole into a bounded weight (`((w - z₀ s)⁻¹)` times a numerator vanishing at `z₀ s`), all three
  terms become integrals over `ℂ` of a bounded measurable compactly supported weight against a
  function that is real analytic on a *product* neighbourhood:
  `Work.NN.Core.TelTwoDF.analyticOn_integral_of_bounded_support` then gives the analyticity in `z`.
-/
import Mathlib
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Core.TelTwoDF.analyticOn_integral_of_bounded_support
import Submission.Work.NN.Core.TelTwoDF.exists_analytic_fibre_dbar_primitive
import Submission.Work.NN.Core.TelTwoDF.integral_cut_dbarC_div
import Submission.Work.NN.Core.TelTwoDF.analyticOn_update_comp
import Submission.Work.NN.Core.TelTwoDF.exists_bound_div_sub_of_vanishing
import Submission.Work.NN.Core.fiberPot

open MeasureTheory Metric Set
open scoped Topology

namespace Work.NN.Core.TelTwoDF

private lemma tsupport_mul_subset_left {f g : ℂ → ℂ} :
    tsupport (fun w : ℂ => f w * g w) ⊆ tsupport f :=
  closure_minimal (fun w hw => subset_tsupport f (Function.support_mul_subset_left f g hw))
    (isClosed_tsupport f)

private lemma tsupport_mul_subset_right {f g : ℂ → ℂ} :
    tsupport (fun w : ℂ => f w * g w) ⊆ tsupport g :=
  closure_minimal (fun w hw => subset_tsupport g (Function.support_mul_subset_right f g hw))
    (isClosed_tsupport g)

private lemma tsupport_div_subset_tsupport {ψ : ℂ → ℂ} {c : ℂ} :
    tsupport (fun w : ℂ => ψ w / (w - c)) ⊆ tsupport ψ := by
  refine closure_minimal ?_ (isClosed_tsupport ψ)
  intro w hw
  exact subset_tsupport ψ (by
    rw [Function.mem_support] at hw ⊢
    intro h0
    exact hw (by rw [h0, zero_div]))

private lemma tsupport_div_subset {ψ : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hzero : ∀ w : ℂ, ‖w - c‖ < r → ψ w = 0) :
    tsupport (fun w : ℂ => ψ w / (w - c)) ⊆ {w : ℂ | r ≤ ‖w - c‖} := by
  refine closure_minimal ?_
    (isClosed_le continuous_const ((continuous_id.sub continuous_const).norm))
  intro w hw
  by_contra hcon
  exact (Function.mem_support.mp hw) (by rw [hzero w (not_le.mp hcon), zero_div])

private lemma notMem_closedBall_iff {c w : ℂ} {r : ℝ} (h : w ∉ Metric.closedBall c r) :
    r < ‖w - c‖ := by
  rw [Metric.mem_closedBall, dist_eq_norm] at h
  exact not_le.mp h

/-- Cancellation comparing the cut integrand with its weighted form. -/
private lemma mul_div_cancel_left'' {x y b A : ℂ} (hb : x = 0 → b = 0) :
    b * A / y = (b / x) * (A * (x / y)) := by
  by_cases hx : x = 0
  · have hb0 : b = 0 := hb hx
    simp [hx, hb0]
  · by_cases hy : y = 0
    · simp [hy]
    · field_simp

private lemma isOpen_target {n : ℕ} (s : Fin n) {R : ℝ} {Q : Fin n → ℝ} :
    IsOpen {z : Fin n → ℂ | ‖z s‖ < R ∧ ∀ k, k ≠ s → ‖z k‖ < Q k} := by
  have h1 : IsOpen {z : Fin n → ℂ | ‖z s‖ < R} :=
    isOpen_lt ((continuous_apply s).norm) continuous_const
  have h2 : IsOpen {z : Fin n → ℂ | ∀ k, k ≠ s → ‖z k‖ < Q k} := by
    have he : {z : Fin n → ℂ | ∀ k, k ≠ s → ‖z k‖ < Q k}
        = ⋂ k : {k : Fin n // k ≠ s}, {z : Fin n → ℂ | ‖z k.1‖ < Q k.1} := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      exact ⟨fun h k => h k.1 k.2, fun h k hk => h ⟨k, hk⟩⟩
    rw [he]
    exact isOpen_iInter_of_finite fun k =>
      isOpen_lt ((continuous_apply k.1).norm) continuous_const
  exact h1.inter h2

private lemma local_analytic {n : ℕ} (s : Fin n) {R : ℝ} (hR : 0 < R) {Q : Fin n → ℝ}
    (hQ : ∀ k, 0 < Q k) (hQs : R < Q s) {g : (Fin n → ℂ) → ℂ}
    (hg : AnalyticOn ℝ g (Work.CR.Flat.polydisc 0 Q)) {z₀ : Fin n → ℂ}
    (hz₀ : ‖z₀ s‖ < R) (hz₀Q : ∀ k, k ≠ s → ‖z₀ k‖ < Q k) :
    ∃ Ω₁ : Set (Fin n → ℂ), IsOpen Ω₁ ∧ z₀ ∈ Ω₁ ∧
      (∀ z ∈ Ω₁, ‖z s‖ < R ∧ ∀ k, k ≠ s → ‖z k‖ < Q k) ∧
      AnalyticOn ℝ (fun z : Fin n → ℂ => ∫ w in Metric.ball (0:ℂ) R,
        g (Function.update z s w) / (w - z s)) Ω₁ := by
  classical
  -- ## Setup
  have hΩopen := isOpen_target s (R := R) (Q := Q)
  obtain ⟨ε₀, hε₀pos, hε₀sub⟩ := Metric.mem_nhds_iff.mp (hΩopen.mem_nhds ⟨hz₀, hz₀Q⟩)
  have hQs' : 0 < Q s := hQ s
  have hz₀Q' : z₀ ∈ Work.CR.Flat.polydisc 0 Q := by
    rw [Work.CR.Flat.mem_polydisc]
    intro k
    by_cases hk : k = s
    · subst hk; simpa only [Pi.zero_apply, sub_zero] using lt_trans hz₀ hQs
    · simpa only [Pi.zero_apply, sub_zero] using hz₀Q k hk
  have hE := analyticOn_update_comp s hQs' hg
  have hqmem : ((z₀, z₀ s) : (Fin n → ℂ) × ℂ) ∈
      Work.CR.Flat.polydisc 0 Q ×ˢ Metric.ball (0:ℂ) (Q s) :=
    ⟨hz₀Q', by simpa using lt_trans hz₀ hQs⟩
  obtain ⟨U, hUopen, hqU, hUsub, A, hAan, hAeq⟩ :=
    exists_analytic_fibre_dbar_primitive
      ((Work.CR.Flat.isOpen_polydisc 0 Q).prod Metric.isOpen_ball) hE hqmem
  obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp (hUopen.mem_nhds hqU)
  -- ## The numerical scale
  set c : ℝ := min (min ε₀ δ) (min (R - ‖z₀ s‖) (Q s - R)) with hcdef
  have hcpos : 0 < c := by
    rw [hcdef]
    exact lt_min (lt_min hε₀pos hδpos) (lt_min (by linarith) (by linarith))
  have hcε : c ≤ ε₀ := by rw [hcdef]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hcδ : c ≤ δ := by rw [hcdef]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hcR : c ≤ R - ‖z₀ s‖ := by rw [hcdef]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hcQ : c ≤ Q s - R := by rw [hcdef]; exact (min_le_right _ _).trans (min_le_right _ _)
  -- ## The cutoff
  set bump : ContDiffBump (z₀ s) := ⟨c/100, c/50, by linarith, by linarith⟩ with hbumpdef
  set χ : ℂ → ℂ := fun w => ((bump w : ℝ) : ℂ) with hχdef
  have hχcd : ContDiff ℝ 1 χ := by
    rw [hχdef]
    exact (Complex.ofRealCLM.contDiff (n := (1 : WithTop ℕ∞))).comp
      (bump.contDiff (n := (1 : ℕ∞)))
  have hχone : ∀ w : ℂ, ‖w - z₀ s‖ ≤ c/100 → χ w = 1 := by
    intro w hw
    have h1 : bump w = 1 :=
      bump.one_of_mem_closedBall (by rw [Metric.mem_closedBall, dist_eq_norm]; exact hw)
    simp only [hχdef, h1, Complex.ofReal_one]
  have hχsupp : ∀ w : ℂ, c/50 ≤ ‖w - z₀ s‖ → χ w = 0 := by
    intro w hw
    have h2 : bump w = 0 := by
      by_contra hne
      have hmem : w ∈ Function.support (bump : ℂ → ℝ) := Function.mem_support.mpr hne
      rw [ContDiffBump.support_eq] at hmem
      rw [Metric.mem_ball, dist_eq_norm] at hmem
      exact absurd hmem (not_lt.mpr hw)
    simp only [hχdef, h2, Complex.ofReal_zero]
  have hχtsupp : tsupport χ ⊆ Metric.closedBall (z₀ s) (c/50) := by
    refine closure_minimal ?_ isClosed_closedBall
    intro w hw
    by_contra hw'
    have hge : c/50 ≤ ‖w - z₀ s‖ := le_of_lt (notMem_closedBall_iff hw')
    exact (Function.mem_support.mp hw) (hχsupp w hge)
  have hχc : HasCompactSupport χ :=
    (isCompact_closedBall (z₀ s) (c/50)).of_isClosed_subset (isClosed_tsupport χ) hχtsupp
  have hdbarχ_zero : ∀ w : ℂ, ‖w - z₀ s‖ < c/100 → Work.CR.Flat.dbarC χ w = 0 := by
    intro w hw
    have hev : χ =ᶠ[𝓝 w] fun _ => (1 : ℂ) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds (show w ∈ Metric.ball (z₀ s) (c/100) from by
        rw [Metric.mem_ball, dist_eq_norm]; exact hw)] with y hy
      exact hχone y (le_of_lt (by rw [Metric.mem_ball, dist_eq_norm] at hy; exact hy))
    rw [Work.CR.Flat.dbarC, hev.fderiv_eq]
    have h0 : fderiv ℝ (fun _ : ℂ => (1:ℂ)) w = 0 := by
      have h1 := congrFun (fderiv_one (𝕜 := ℝ) (E := ℂ) (F := ℂ)) w
      simpa using h1
    rw [h0]
    simp
  -- ## The domains
  set Ω₁ : Set (Fin n → ℂ) := Metric.ball z₀ (c/1000) with hΩ₁def
  have hΩ₁open : IsOpen Ω₁ := Metric.isOpen_ball
  have hz₀Ω₁ : z₀ ∈ Ω₁ := Metric.mem_ball_self (by linarith)
  have hΩ₁sub : Ω₁ ⊆ {z : Fin n → ℂ | ‖z s‖ < R ∧ ∀ k, k ≠ s → ‖z k‖ < Q k} :=
    fun z hz => hε₀sub (Metric.ball_subset_ball (by linarith) hz)
  set U₁ : Set ℂ := {w : ℂ | c/500 < ‖w - z₀ s‖ ∧ ‖w - z₀ s‖ < c/20} with hU₁def
  set U₂ : Set ℂ := {w : ℂ | c/500 < ‖w - z₀ s‖ ∧ ‖w‖ < R + c/2} with hU₂def
  have hU₁open : IsOpen U₁ := by
    rw [hU₁def]
    exact (isOpen_lt continuous_const ((continuous_id.sub continuous_const).norm)).inter
      (isOpen_lt ((continuous_id.sub continuous_const).norm) continuous_const)
  have hU₂open : IsOpen U₂ := by
    rw [hU₂def]
    exact (isOpen_lt continuous_const ((continuous_id.sub continuous_const).norm)).inter
      (isOpen_lt continuous_norm continuous_const)
  -- ## The integrands
  let F₁ : (Fin n → ℂ) × ℂ → ℂ := fun p => A p * ((p.2 - z₀ s)/(p.2 - p.1 s))
  let F₂ : (Fin n → ℂ) × ℂ → ℂ := fun p =>
    g (Function.update p.1 s p.2) * ((p.2 - z₀ s)/(p.2 - p.1 s))
  have hfibre : AnalyticOn ℝ (fun p : (Fin n → ℂ) × ℂ => g (Function.update p.1 s p.2))
      (Ω₁ ×ˢ U₂) := by
    refine hE.mono ?_
    intro p hp
    obtain ⟨hp1, hp2⟩ := hp
    rw [hU₂def] at hp2
    refine ⟨?_, ?_⟩
    · rw [Work.CR.Flat.mem_polydisc]
      intro k
      have hmem := hΩ₁sub hp1
      have h1 : ‖p.1 k‖ < Q k := by
        by_cases hk : k = s
        · subst hk; exact lt_trans hmem.1 hQs
        · exact hmem.2 k hk
      simpa only [Pi.zero_apply, sub_zero] using h1
    · rw [Metric.mem_ball, dist_eq_norm, sub_zero]
      have h1 : R + c/2 ≤ (R + Q s)/2 := by linarith [hcQ]
      have h2 : (R + Q s)/2 < Q s := by linarith
      linarith [hp2.2, h1, h2]
  have hnum : AnalyticOn ℝ (fun p : (Fin n → ℂ) × ℂ => p.2 - z₀ s) (Ω₁ ×ˢ (U₁ ∪ U₂)) := by
    have h2 : AnalyticOn ℝ (fun p : (Fin n → ℂ) × ℂ => p.2) (Ω₁ ×ˢ (U₁ ∪ U₂)) :=
      ContinuousLinearMap.analyticOn (ContinuousLinearMap.snd ℝ (Fin n → ℂ) ℂ) _
    exact h2.sub analyticOn_const
  have hden : AnalyticOn ℝ (fun p : (Fin n → ℂ) × ℂ => p.2 - p.1 s) (Ω₁ ×ˢ (U₁ ∪ U₂)) := by
    have h2 : AnalyticOn ℝ (fun p : (Fin n → ℂ) × ℂ => p.2) (Ω₁ ×ˢ (U₁ ∪ U₂)) :=
      ContinuousLinearMap.analyticOn (ContinuousLinearMap.snd ℝ (Fin n → ℂ) ℂ) _
    have h1 : AnalyticOn ℝ (fun p : (Fin n → ℂ) × ℂ => p.1 s) (Ω₁ ×ˢ (U₁ ∪ U₂)) :=
      ContinuousLinearMap.analyticOn
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) s).comp
          (ContinuousLinearMap.fst ℝ (Fin n → ℂ) ℂ)) _
    exact h2.sub h1
  have hden_ne : ∀ p ∈ Ω₁ ×ˢ (U₁ ∪ U₂), p.2 - p.1 s ≠ 0 := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := hp
    have hz1 : ‖p.1 s - z₀ s‖ < c/1000 := by
      have h1 : ‖p.1 - z₀‖ < c/1000 := by
        have := Metric.mem_ball.mp hp1; rwa [dist_eq_norm] at this
      have h2 : ‖p.1 s - z₀ s‖ ≤ ‖p.1 - z₀‖ := by
        simpa only [Pi.sub_apply] using norm_le_pi_norm (p.1 - z₀) s
      linarith
    have hge : c/500 < ‖p.2 - z₀ s‖ := by
      rcases hp2 with h2 | h2
      · rw [hU₁def] at h2; exact h2.1
      · rw [hU₂def] at h2; exact h2.1
    have hlow : ‖p.2 - z₀ s‖ ≤ ‖p.2 - p.1 s‖ + ‖p.1 s - z₀ s‖ := by
      have h := norm_add_le (p.2 - p.1 s) (p.1 s - z₀ s)
      have he : p.2 - p.1 s + (p.1 s - z₀ s) = p.2 - z₀ s := by ring
      rw [he] at h; exact h
    intro hcon
    rw [hcon, norm_zero] at hlow
    linarith
  have hQfac : AnalyticOn ℝ (fun p : (Fin n → ℂ) × ℂ => (p.2 - z₀ s)/(p.2 - p.1 s))
      (Ω₁ ×ˢ (U₁ ∪ U₂)) := hnum.div hden hden_ne
  have hF₁an : AnalyticOn ℝ F₁ (Ω₁ ×ˢ U₁) := by
    have hA1 : AnalyticOn ℝ A (Ω₁ ×ˢ U₁) := hAan.mono (by
      intro p hp
      obtain ⟨hp1, hp2⟩ := hp
      rw [hU₁def] at hp2
      refine hδsub ?_
      rw [Metric.mem_ball, Prod.dist_eq]
      have h1 : ‖p.1 - z₀‖ < c/1000 := by
        have := Metric.mem_ball.mp hp1; rwa [dist_eq_norm] at this
      have h2 : ‖p.2 - z₀ s‖ < c/20 := hp2.2
      rw [dist_eq_norm, dist_eq_norm]
      exact max_lt (by linarith [hcδ, hcpos, h1]) (by linarith [hcδ, hcpos, h2]))
    exact hA1.mul (hQfac.mono (Set.prod_mono (Subset.refl _) Set.subset_union_left))
  have hF₂an : AnalyticOn ℝ F₂ (Ω₁ ×ˢ U₂) :=
    hfibre.mul (hQfac.mono (Set.prod_mono (Subset.refl _) Set.subset_union_right))
  -- ## The weights
  set ib : ℂ → ℂ := (Metric.ball (0:ℂ) R).indicator (fun _ => (1:ℂ)) with hibdef
  have hib_zero : ∀ w : ℂ, w ∉ Metric.ball (0:ℂ) R → ib w = 0 := by
    intro w hw; rw [hibdef]; exact Set.indicator_of_notMem hw _
  have hib_one : ∀ w ∈ Metric.ball (0:ℂ) R, ib w = 1 := by
    intro w hw; rw [hibdef]; exact Set.indicator_of_mem hw _
  have hib_meas : Measurable ib := by
    rw [hibdef]; exact measurable_const.indicator measurableSet_ball
  have hib_tsupp : tsupport ib ⊆ Metric.closedBall (0:ℂ) R := by
    refine closure_minimal ?_ isClosed_closedBall
    intro w hw
    by_contra hcon
    exact (Function.mem_support.mp hw) (hib_zero w (fun h => hcon (Metric.ball_subset_closedBall h)))
  have hdbarχ_cont : Continuous (fun w : ℂ => Work.CR.Flat.dbarC χ w) := by
    have hf : Continuous (fun w : ℂ => fderiv ℝ χ w) := hχcd.continuous_fderiv (by norm_num)
    have h : (fun w : ℂ => Work.CR.Flat.dbarC χ w)
        = fun w : ℂ => (1/2 : ℂ) * (fderiv ℝ χ w 1 + Complex.I * fderiv ℝ χ w Complex.I) := by
      funext w
      rw [Work.CR.Flat.dbarC]
    rw [h]
    refine continuous_const.mul (Continuous.add ?_ ?_)
    · exact hf.clm_apply continuous_const
    · exact continuous_const.mul (hf.clm_apply continuous_const)
  have hdbarχ_supp : Function.support (fun w : ℂ => Work.CR.Flat.dbarC χ w) ⊆ tsupport χ := by
    intro w hw
    by_contra hw'
    have hev : χ =ᶠ[𝓝 w] fun _ => (0:ℂ) := by
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hw'] with y hy
      by_contra hy'
      exact hy (subset_tsupport χ (Function.mem_support.mpr hy'))
    refine (Function.mem_support.mp hw) ?_
    rw [Work.CR.Flat.dbarC, hev.fderiv_eq]
    have h0 : fderiv ℝ (fun _ : ℂ => (0:ℂ)) w = 0 := by
      have h1 := congrFun (fderiv_const (𝕜 := ℝ) (0 : ℂ)) w
      simpa using h1
    rw [h0]
    simp
  have hdbarχ_tsupp : tsupport (fun w : ℂ => Work.CR.Flat.dbarC χ w) ⊆ tsupport χ :=
    closure_minimal (fun w hw => hdbarχ_supp hw) (isClosed_tsupport _)
  have hdbarχ_c : HasCompactSupport (fun w : ℂ => Work.CR.Flat.dbarC χ w) :=
    (hχc.isCompact).of_isClosed_subset (isClosed_tsupport _) hdbarχ_tsupp
  have hdbarχ_bdd : ∃ C, ∀ w : ℂ, ‖Work.CR.Flat.dbarC χ w‖ ≤ C :=
    hdbarχ_cont.bounded_above_of_compact_support hdbarχ_c
  have hχ_bdd : ∃ C, ∀ w : ℂ, ‖χ w‖ ≤ C :=
    hχcd.continuous.bounded_above_of_compact_support hχc
  let K₁ : ℂ → ℂ := fun w => (Work.CR.Flat.dbarC χ w / (w - z₀ s)) * ib w
  let K₂ : ℂ → ℂ := fun w => ((1 - χ w) / (w - z₀ s)) * ib w
  have hK₁meas : AEStronglyMeasurable K₁ := by
    show AEStronglyMeasurable (fun w : ℂ => (Work.CR.Flat.dbarC χ w / (w - z₀ s)) * ib w)
    exact ((hdbarχ_cont.measurable.div (measurable_id.sub measurable_const)).mul
      hib_meas).aestronglyMeasurable
  have hK₂meas : AEStronglyMeasurable K₂ := by
    show AEStronglyMeasurable (fun w : ℂ => ((1 - χ w) / (w - z₀ s)) * ib w)
    exact ((((continuous_const.sub hχcd.continuous).measurable).div
      (measurable_id.sub measurable_const)).mul hib_meas).aestronglyMeasurable
  have hK₁c : HasCompactSupport K₁ := by
    refine hdbarχ_c.mono ?_
    show Function.support (fun w : ℂ => (Work.CR.Flat.dbarC χ w / (w - z₀ s)) * ib w) ⊆
      Function.support (fun w : ℂ => Work.CR.Flat.dbarC χ w)
    refine (Function.support_mul_subset_left _ _).trans ?_
    intro w hw
    rw [Function.mem_support] at hw ⊢
    intro h0
    exact hw (by rw [h0, zero_div])
  have hK₂c : HasCompactSupport K₂ :=
    (isCompact_closedBall (0:ℂ) R).of_isClosed_subset (isClosed_tsupport _)
      (tsupport_mul_subset_right.trans hib_tsupp)
  have hK₁tsupp : tsupport K₁ ⊆ U₁ := by
    have h2 : tsupport K₁ ⊆ tsupport (fun w : ℂ => Work.CR.Flat.dbarC χ w / (w - z₀ s)) := by
      show tsupport (fun w : ℂ => (Work.CR.Flat.dbarC χ w / (w - z₀ s)) * ib w) ⊆ _
      exact tsupport_mul_subset_left
    have h3 : tsupport (fun w : ℂ => Work.CR.Flat.dbarC χ w / (w - z₀ s)) ⊆
        tsupport (fun w : ℂ => Work.CR.Flat.dbarC χ w) := tsupport_div_subset_tsupport
    have h4 : tsupport (fun w : ℂ => Work.CR.Flat.dbarC χ w / (w - z₀ s)) ⊆
        {w : ℂ | c/100 ≤ ‖w - z₀ s‖} :=
      tsupport_div_subset (fun w hw => hdbarχ_zero w hw)
    intro w hw
    have h5 := h4 (h2 hw)
    have h6 : w ∈ Metric.closedBall (z₀ s) (c/50) := hχtsupp (hdbarχ_tsupp (h3 (h2 hw)))
    rw [Metric.mem_closedBall, dist_eq_norm] at h6
    rw [hU₁def]
    exact ⟨lt_of_lt_of_le (by linarith : c/500 < c/100) h5,
      lt_of_le_of_lt h6 (by linarith : c/50 < c/20)⟩
  have hK₂tsupp : tsupport K₂ ⊆ U₂ := by
    have h2 : tsupport K₂ ⊆ tsupport (fun w : ℂ => (1 - χ w) / (w - z₀ s)) := by
      show tsupport (fun w : ℂ => ((1 - χ w) / (w - z₀ s)) * ib w) ⊆ _
      exact tsupport_mul_subset_left
    have h4 : tsupport (fun w : ℂ => (1 - χ w) / (w - z₀ s)) ⊆ {w : ℂ | c/100 ≤ ‖w - z₀ s‖} :=
      tsupport_div_subset (fun w hw => by
        have h5 := hχone w (le_of_lt hw)
        rw [h5]; ring)
    have h6 : tsupport K₂ ⊆ tsupport ib := by
      show tsupport (fun w : ℂ => ((1 - χ w) / (w - z₀ s)) * ib w) ⊆ _
      exact tsupport_mul_subset_right
    intro w hw
    have h7 := h4 (h2 hw)
    have h8 : w ∈ Metric.closedBall (0:ℂ) R := hib_tsupp (h6 hw)
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h8
    rw [hU₂def]
    exact ⟨lt_of_lt_of_le (by linarith : c/500 < c/100) h7, by linarith⟩
  have hK₁bdd : ∃ C, ∀ w : ℂ, ‖K₁ w‖ ≤ C := by
    obtain ⟨C, hC⟩ := exists_bound_div_sub_of_vanishing (ψ := fun w => Work.CR.Flat.dbarC χ w)
      (c := z₀ s) (ρ := c/100) (by linarith) (fun w hw => hdbarχ_zero w hw) hdbarχ_bdd
    refine ⟨C, fun w => ?_⟩
    have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
    have hib1 : ‖ib w‖ ≤ 1 := by
      rw [hibdef, Set.indicator_apply]
      split_ifs <;> simp
    show ‖(Work.CR.Flat.dbarC χ w / (w - z₀ s)) * ib w‖ ≤ C
    rw [norm_mul]
    calc ‖Work.CR.Flat.dbarC χ w / (w - z₀ s)‖ * ‖ib w‖ ≤ C * 1 :=
          mul_le_mul (hC w) hib1 (norm_nonneg _) hCnn
      _ = C := by ring
  have hK₂bdd : ∃ C, ∀ w : ℂ, ‖K₂ w‖ ≤ C := by
    obtain ⟨C, hC⟩ := exists_bound_div_sub_of_vanishing (ψ := fun w => 1 - χ w)
      (c := z₀ s) (ρ := c/100) (by linarith)
      (fun w hw => by
        have h4 := hχone w (le_of_lt hw)
        rw [h4]; ring)
      (by
        obtain ⟨C, hC⟩ := hχ_bdd
        exact ⟨1 + C, fun w => by
          have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
          calc ‖1 - χ w‖ ≤ ‖(1:ℂ)‖ + ‖χ w‖ := norm_sub_le _ _
            _ ≤ 1 + C := by rw [norm_one]; linarith [hC w]⟩)
    refine ⟨C, fun w => ?_⟩
    have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
    have hib1 : ‖ib w‖ ≤ 1 := by
      rw [hibdef, Set.indicator_apply]
      split_ifs <;> simp
    show ‖((1 - χ w) / (w - z₀ s)) * ib w‖ ≤ C
    rw [norm_mul]
    calc ‖(1 - χ w) / (w - z₀ s)‖ * ‖ib w‖ ≤ C * 1 :=
          mul_le_mul (hC w) hib1 (norm_nonneg _) hCnn
      _ = C := by ring
  -- ## The pointwise identity
  have hdec : ∀ z ∈ Ω₁, (∫ w in Metric.ball (0:ℂ) R, g (Function.update z s w) / (w - z s))
      = -(Real.pi : ℂ) * A (z, z s) - (∫ w : ℂ, K₁ w * F₁ (z, w))
        + (∫ w : ℂ, K₂ w * F₂ (z, w)) := by
    intro z hz
    set a : ℂ := z s with hadef
    have hzΩ := hΩ₁sub hz
    have haR : ‖a‖ < R := by rw [hadef]; exact hzΩ.1
    -- sup bound on the data
    have hcontg : ContinuousOn (fun w : ℂ => g (Function.update z s w))
        (Metric.closedBall (0:ℂ) R) := by
      have hc : Continuous (fun x : ℂ => Function.update z s x) := by
        rw [continuous_pi_iff]
        intro k
        have hfun : (fun x : ℂ => Function.update z s x k)
            = fun x : ℂ => if k = s then x else z k := by
          funext x; rw [Function.update_apply]
        rw [hfun]
        by_cases hk : k = s
        · simp only [if_pos hk]; exact continuous_id
        · simp only [if_neg hk]; exact continuous_const
      refine hg.continuousOn.comp hc.continuousOn ?_
      intro w hw
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hw
      rw [Work.CR.Flat.mem_polydisc]
      intro k
      have hfun : Function.update z s w k = if k = s then w else z k := Function.update_apply ..
      rw [hfun]
      by_cases hk : k = s
      · rw [if_pos hk, hk]
        simp only [Pi.zero_apply, sub_zero]
        linarith [hw, hR, hQs]
      · rw [if_neg hk]
        have hmem := hzΩ.2 k hk
        simpa only [Pi.zero_apply, sub_zero] using hmem
    obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn (isCompact_closedBall (0:ℂ) R) hcontg
    obtain ⟨Cχ, hCχ⟩ := hχ_bdd
    have hCχnn : 0 ≤ Cχ := le_trans (norm_nonneg _) (hCχ 0)
    -- integrability of the two parts of the split
    have hpart1 : IntegrableOn (fun w : ℂ => χ w * g (Function.update z s w) / (w - a))
        (Metric.ball (0:ℂ) R) := by
      have hfun : (fun w : ℂ => χ w * g (Function.update z s w) / (w - a))
          = fun w : ℂ => (χ w * g (Function.update z s w)) * (w - a)⁻¹ := by
        funext w; rw [div_eq_mul_inv]
      rw [hfun]
      refine (Work.NN.Core.integrableOn_sub_inv_ball R a).bdd_mul (c := Cχ * M) ?_ ?_
      · exact ((hχcd.continuous.continuousOn.mul hcontg).mono
          Metric.ball_subset_closedBall).aestronglyMeasurable measurableSet_ball
      · rw [MeasureTheory.ae_restrict_iff' measurableSet_ball]
        refine Filter.Eventually.of_forall fun w hw => ?_
        calc ‖χ w * g (Function.update z s w)‖
            = ‖χ w‖ * ‖g (Function.update z s w)‖ := norm_mul _ _
          _ ≤ Cχ * M := mul_le_mul (hCχ w)
              (hM w (Metric.ball_subset_closedBall hw)) (norm_nonneg _) hCχnn
          _ = Cχ * M := rfl
    have hpart2 : IntegrableOn (fun w : ℂ => (1 - χ w) * g (Function.update z s w) / (w - a))
        (Metric.ball (0:ℂ) R) := by
      have hfun : (fun w : ℂ => (1 - χ w) * g (Function.update z s w) / (w - a))
          = fun w : ℂ => ((1 - χ w) * g (Function.update z s w)) * (w - a)⁻¹ := by
        funext w; rw [div_eq_mul_inv]
      rw [hfun]
      refine (Work.NN.Core.integrableOn_sub_inv_ball R a).bdd_mul (c := (1 + Cχ) * M) ?_ ?_
      · exact (((continuous_const.sub hχcd.continuous).continuousOn.mul hcontg).mono
          Metric.ball_subset_closedBall).aestronglyMeasurable measurableSet_ball
      · rw [MeasureTheory.ae_restrict_iff' measurableSet_ball]
        refine Filter.Eventually.of_forall fun w hw => ?_
        calc ‖(1 - χ w) * g (Function.update z s w)‖
            = ‖1 - χ w‖ * ‖g (Function.update z s w)‖ := norm_mul _ _
          _ ≤ (1 + Cχ) * M := by
              refine mul_le_mul ?_ (hM w (Metric.ball_subset_closedBall hw))
                (norm_nonneg _) (by linarith)
              calc ‖1 - χ w‖ ≤ ‖(1:ℂ)‖ + ‖χ w‖ := norm_sub_le _ _
                _ ≤ 1 + Cχ := by rw [norm_one]; linarith [hCχ w]
          _ = (1 + Cχ) * M := rfl
    have hsplit : (∫ w in Metric.ball (0:ℂ) R, g (Function.update z s w) / (w - a))
        = (∫ w in Metric.ball (0:ℂ) R, χ w * g (Function.update z s w) / (w - a))
          + (∫ w in Metric.ball (0:ℂ) R,
              (1 - χ w) * g (Function.update z s w) / (w - a)) := by
      rw [← MeasureTheory.integral_add hpart1 hpart2]
      refine setIntegral_congr_fun measurableSet_ball ?_
      intro w hw; ring
    -- the splitting region
    have hzU : ∀ w : ℂ, χ w ≠ 0 → (z, w) ∈ U := by
      intro w hw
      have h1 : w ∈ tsupport χ := subset_tsupport χ (Function.mem_support.mpr hw)
      have h2 : w ∈ Metric.closedBall (z₀ s) (c/50) := hχtsupp h1
      rw [Metric.mem_closedBall, dist_eq_norm] at h2
      refine hδsub ?_
      rw [Metric.mem_ball, Prod.dist_eq]
      have h3 : ‖z - z₀‖ < c/1000 := by
        have := Metric.mem_ball.mp hz; rwa [dist_eq_norm] at this
      rw [dist_eq_norm, dist_eq_norm]
      exact max_lt (by linarith [hcδ, hcpos, h3]) (by linarith [hcδ, hcpos, h2])
    -- replace the data by the fibre primitive on the first part
    have hpiece₁ : (∫ w in Metric.ball (0:ℂ) R, χ w * g (Function.update z s w) / (w - a))
        = ∫ w in Metric.ball (0:ℂ) R,
            χ w * (Work.CR.Flat.dbarC (fun x => A (z, x)) w) / (w - a) := by
      refine setIntegral_congr_fun measurableSet_ball ?_
      intro w hw
      dsimp only
      rcases eq_or_ne (χ w) 0 with h0 | h0
      · rw [h0]; ring
      · have hA' : g (Function.update z s w) = Work.CR.Flat.dbarC (fun x => A (z, x)) w := by
          simpa only [Prod.fst, Prod.snd] using hAeq (z, w) (hzU w h0)
        rw [hA']
    -- the cut identity
    have hUz : IsOpen {w : ℂ | (z, w) ∈ U} :=
      hUopen.preimage (continuous_const.prodMk continuous_id)
    have hAslice : ContDiffOn ℝ 1 (fun w : ℂ => A (z, w)) {w : ℂ | (z, w) ∈ U} := by
      have hmap : AnalyticOn ℝ (fun w : ℂ => ((z, w) : (Fin n → ℂ) × ℂ))
          {w : ℂ | (z, w) ∈ U} :=
        AnalyticOn.prod (analyticOn_const (v := z)) ((ContinuousLinearMap.id ℝ ℂ).analyticOn _)
      have hcomp : AnalyticOn ℝ (fun w : ℂ => A (z, w)) {w : ℂ | (z, w) ∈ U} :=
        hAan.comp hmap (fun w hw => hw)
      intro w hw
      exact ((hcomp w hw).contDiffWithinAt).of_le le_top
    have hχUz : tsupport χ ⊆ {w : ℂ | (z, w) ∈ U} := by
      intro w hw
      have h1 : w ∈ Metric.closedBall (z₀ s) (c/50) := hχtsupp hw
      rw [Metric.mem_closedBall, dist_eq_norm] at h1
      refine hδsub ?_
      rw [Metric.mem_ball, Prod.dist_eq]
      have h3 : ‖z - z₀‖ < c/1000 := by
        have := Metric.mem_ball.mp hz; rwa [dist_eq_norm] at this
      rw [dist_eq_norm, dist_eq_norm]
      exact max_lt (by linarith [hcδ, hcpos, h3]) (by linarith [hcδ, hcpos, h1])
    have hχsuppR : ∀ w : ℂ, R ≤ ‖w‖ → χ w = 0 := by
      intro w hw
      refine hχsupp w ?_
      have h8 : ‖w‖ ≤ ‖w - z₀ s‖ + ‖z₀ s‖ := by
        have h := norm_add_le (w - z₀ s) (z₀ s); rwa [sub_add_cancel] at h
      linarith [hcR]
    have hχ1' : ∀ w : ℂ, ‖w - a‖ < c/200 → χ w = 1 := by
      intro w hw
      refine hχone w ?_
      have h9 : ‖w - z₀ s‖ ≤ ‖w - a‖ + ‖a - z₀ s‖ := by
        have h := norm_add_le (w - a) (a - z₀ s)
        have he : w - a + (a - z₀ s) = w - z₀ s := by ring
        rw [he] at h; exact h
      have h10 : ‖a - z₀ s‖ < c/1000 := by
        rw [hadef]
        have h3 : ‖z - z₀‖ < c/1000 := by
          have := Metric.mem_ball.mp hz; rwa [dist_eq_norm] at this
        have h4 : ‖z s - z₀ s‖ ≤ ‖z - z₀‖ := by
          simpa only [Pi.sub_apply] using norm_le_pi_norm (z - z₀) s
        linarith
      linarith
    have hpiece1b : (∫ w in Metric.ball (0:ℂ) R,
          χ w * (Work.CR.Flat.dbarC (fun x => A (z, x)) w) / (w - a))
        = -(Real.pi : ℂ) * A (z, a)
          - ∫ w in Metric.ball (0:ℂ) R,
              Work.CR.Flat.dbarC χ w * A (z, w) / (w - a) :=
      integral_cut_dbarC_div hR hUz hχcd hχc hAslice hχUz hχsuppR haR
        (by linarith : (0:ℝ) < c/200) hχ1'
    -- re-express the two remaining ball integrals with the weights
    have hre1 : (∫ w in Metric.ball (0:ℂ) R, Work.CR.Flat.dbarC χ w * A (z, w) / (w - a))
        = ∫ w : ℂ, K₁ w * F₁ (z, w) := by
      rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := Metric.ball (0:ℂ) R) (f := fun w : ℂ => K₁ w * F₁ (z, w))]
      · refine setIntegral_congr_fun measurableSet_ball ?_
        intro w hw
        have hb1 : ib w = 1 := hib_one w hw
        simp only [K₁, F₁, hb1, mul_one, Prod.fst, Prod.snd]
        exact mul_div_cancel_left'' (fun hx => by
          have hw0 : w = z₀ s := sub_eq_zero.mp hx
          rw [hw0]
          exact hdbarχ_zero (z₀ s) (by rw [sub_self, norm_zero]; linarith))
      · intro w hw
        have hb0 : ib w = 0 := hib_zero w hw
        simp [K₁, hb0]
    have hre2 : (∫ w in Metric.ball (0:ℂ) R,
          (1 - χ w) * g (Function.update z s w) / (w - a))
        = ∫ w : ℂ, K₂ w * F₂ (z, w) := by
      rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := Metric.ball (0:ℂ) R) (f := fun w : ℂ => K₂ w * F₂ (z, w))]
      · refine setIntegral_congr_fun measurableSet_ball ?_
        intro w hw
        have hb1 : ib w = 1 := hib_one w hw
        simp only [K₂, F₂, hb1, mul_one, Prod.fst, Prod.snd]
        exact mul_div_cancel_left'' (fun hx => by
          have hw0 : w = z₀ s := sub_eq_zero.mp hx
          rw [hw0, hχone (z₀ s) (by rw [sub_self, norm_zero]; linarith)]
          ring)
      · intro w hw
        have hb0 : ib w = 0 := hib_zero w hw
        simp [K₂, hb0]
    rw [hsplit, hpiece₁, hpiece1b, hre1, hre2]
  -- ## The analyticity of the three pieces
  have hAcomp : AnalyticOn ℝ (fun z : Fin n → ℂ => A (z, z s)) Ω₁ := by
    have hmap : AnalyticOn ℝ (fun z : Fin n → ℂ => ((z, z s) : (Fin n → ℂ) × ℂ)) Ω₁ :=
      AnalyticOn.prod (ContinuousLinearMap.analyticOn (ContinuousLinearMap.id ℝ (Fin n → ℂ)) Ω₁)
        (ContinuousLinearMap.analyticOn
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) s) Ω₁)
    refine hAan.comp hmap ?_
    intro z hz
    refine hδsub ?_
    rw [Metric.mem_ball, Prod.dist_eq]
    have h1 : ‖z - z₀‖ < c/1000 := by
      have := Metric.mem_ball.mp hz; rwa [dist_eq_norm] at this
    have h2 : ‖z s - z₀ s‖ ≤ ‖z - z₀‖ := by
      simpa only [Pi.sub_apply] using norm_le_pi_norm (z - z₀) s
    rw [dist_eq_norm, dist_eq_norm]
    exact max_lt (by linarith [hcδ, hcpos, h1]) (by linarith [hcδ, hcpos, h1])
  have hpiece0 : AnalyticOn ℝ (fun z : Fin n → ℂ => -(Real.pi : ℂ) * A (z, z s)) Ω₁ :=
    (analyticOn_const (v := -(Real.pi : ℂ))).mul hAcomp
  have hpiece1an : AnalyticOn ℝ (fun z : Fin n → ℂ => ∫ w : ℂ, K₁ w * F₁ (z, w)) Ω₁ :=
    analyticOn_integral_of_bounded_support hΩ₁open hU₁open hK₁meas hK₁c hK₁bdd hK₁tsupp hF₁an
  have hpiece2an : AnalyticOn ℝ (fun z : Fin n → ℂ => ∫ w : ℂ, K₂ w * F₂ (z, w)) Ω₁ :=
    analyticOn_integral_of_bounded_support hΩ₁open hU₂open hK₂meas hK₂c hK₂bdd hK₂tsupp hF₂an
  refine ⟨Ω₁, hΩ₁open, hz₀Ω₁, hΩ₁sub, ?_⟩
  refine ((hpiece0.sub hpiece1an).add hpiece2an).congr fun z hz => hdec z hz

/-- Real analyticity of the truncated Cauchy transform of an analytic function.

Let `g` be real analytic on the polydisc `polydisc 0 Q` (centre `0`, multi-radius `Q > 0`) and
let `0 < R < Q s`.  Then `z ↦ ∫_{‖w‖ < R} g (update z s w) / (w - z s)` is real analytic on
`{|z s| < R} × {|z k| < Q k, k ≠ s}`.  The integrand does not depend on `z s` except through
the pole `w = z s`, which lies inside the disc of integration, and `g` is only assumed analytic
on the polydisc (no antisymmetry or closedness).

Route: subtraction plus moments.  Write `g (update z s w) = g (update z s (z s)) + (w - z s) * h`
and use `Work.NN.Core.TelTwoDF.integral_ball_inv_sub` to evaluate
`∫_{‖w‖<R} (w - z s)⁻¹ = -π * star (z s)`, which is analytic in `z`.  It remains to show that
`z ↦ ∫ h` is analytic, where `h = (g (update z s w) - g (update z s (z s))) / (w - z s)`.  The
integrand `h` is bounded but not real analytic on a neighbourhood of the pole, so the parameter
integral lemmas do not apply directly.  Instead expand the fibre function in its Taylor series
at `w = 0`: `g (update z s w) = Σ_{p,q} c_{p,q} w^p star(w)^q`, convergent with uniform bounds
on `‖w‖ ≤ R` because `R < Q s`, with coefficients analytic in the remaining variables.  The
moments `M_{p,q} = ∫_{‖w‖<R} w^p star(w)^q (w - z s)⁻¹` equal
`π/(q+1) * z^(p-q-1) * (R^(2q+2) - |z|^(2q+2))` for `q ≤ p-1` and
`-π/(q+1) * z^p * star(z)^(q+1)` for `q ≥ p`; these are polynomials in `(z, star z)`, hence
real analytic, and the series of integrals converges absolutely and locally uniformly. -/
theorem analyticOn_cauchyTransform_disc {n : ℕ} (s : Fin n) {R : ℝ} (hR : 0 < R)
    {Q : Fin n → ℝ} (hQ : ∀ k, 0 < Q k) (hQs : R < Q s)
    {g : (Fin n → ℂ) → ℂ} (hg : AnalyticOn ℝ g (Work.CR.Flat.polydisc 0 Q)) :
    AnalyticOn ℝ (fun z : Fin n → ℂ => ∫ w in Metric.ball (0 : ℂ) R,
        g (Function.update z s w) / (w - z s))
      {z : Fin n → ℂ | ‖z s‖ < R ∧ ∀ k, k ≠ s → ‖z k‖ < Q k} := by
  intro z₀ hz₀
  obtain ⟨Ω₁, hΩ₁open, hz₀Ω₁, -, han⟩ := local_analytic s hR hQ hQs hg hz₀.1 hz₀.2
  have hAt : AnalyticAt ℝ (fun z : Fin n → ℂ => ∫ w in Metric.ball (0:ℂ) R,
      g (Function.update z s w) / (w - z s)) z₀ :=
    han.analyticAt (hΩ₁open.mem_nhds hz₀Ω₁)
  exact hAt.analyticWithinAt

end Work.NN.Core.TelTwoDF
