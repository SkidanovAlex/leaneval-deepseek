import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.setup
import Submission.Work.A14D.om1_geometry
import Submission.Work.A14D.slitPieces
import Submission.Work.A14D.eqOn_of_sol_LZ
import Submission.Work.C17b.isPreconnected_slitBall

/-!
# `Work.A14D.Dzc_*` : small helpers for `D_zero_of_c_eq_zero`

Elementary facts about the slit plane `Om1 = ℂ ∖ (−∞,1]`, the operator `LZ`, and the
`log`-structured vanishing used in the proof of `Work.A14D.D_zero_of_c_eq_zero`.
-/

namespace Work.A14D

open Complex Metric Filter
open scoped Topology BigOperators
open Work.A14D

lemma Dzc_isOpen_Om1 : IsOpen Om1 := by
  have hset : Om1 = {z : ℂ | z.im ≠ 0} ∪ {z : ℂ | 1 < z.re} := rfl
  rw [hset]
  exact (isOpen_compl_singleton.preimage Complex.continuous_im).union
    (isOpen_lt continuous_const Complex.continuous_re)

/-- `Om1 = 1 − ({re < 0} ∪ {im ≠ 0})`. -/
lemma Dzc_Om1_image :
    Om1 = (fun u : ℂ => 1 - u) '' ({u : ℂ | u.re < 0} ∪ {u : ℂ | u.im ≠ 0}) := by
  ext z
  constructor
  · intro hz
    refine ⟨1 - z, ?_, by ring⟩
    rcases hz with him | hre
    · refine Or.inr ?_
      show (1 - z).im ≠ 0
      rw [Complex.sub_im, Complex.one_im, zero_sub, neg_ne_zero]
      exact him
    · refine Or.inl ?_
      show (1 - z).re < 0
      rw [Complex.sub_re, Complex.one_re]
      linarith
  · rintro ⟨u, hu, rfl⟩
    rcases hu with hre | him
    · have hre' : u.re < 0 := hre
      right
      show 1 < (1 - u).re
      rw [Complex.sub_re, Complex.one_re]
      linarith
    · have him' : u.im ≠ 0 := him
      left
      show (1 - u).im ≠ 0
      rw [Complex.sub_im, Complex.one_im, zero_sub, neg_ne_zero]
      exact him'

lemma Dzc_isPreconnected_slitSide :
    IsPreconnected ({u : ℂ | u.re < 0} ∪ {u : ℂ | u.im ≠ 0}) := by
  have h1 : IsPreconnected ({u : ℂ | u.re < 0}) := (convex_halfSpace_re_lt 0).isPreconnected
  have h2 : IsPreconnected ({u : ℂ | 0 < u.im}) := (convex_halfSpace_im_gt 0).isPreconnected
  have h3 : IsPreconnected ({u : ℂ | u.im < 0}) := (convex_halfSpace_im_lt 0).isPreconnected
  have h12 : IsPreconnected ({u : ℂ | u.re < 0} ∪ {u : ℂ | 0 < u.im}) :=
    IsPreconnected.union (-1 + Complex.I) (by simp) (by simp) h1 h2
  have h123 : IsPreconnected (({u : ℂ | u.re < 0} ∪ {u : ℂ | 0 < u.im})
      ∪ {u : ℂ | u.im < 0}) :=
    IsPreconnected.union (-1 - Complex.I) (by simp [Set.mem_union]) (by simp) h12 h3
  have hset : ({u : ℂ | u.re < 0} ∪ {u : ℂ | 0 < u.im}) ∪ {u : ℂ | u.im < 0}
      = {u : ℂ | u.re < 0} ∪ {u : ℂ | u.im ≠ 0} := by
    ext u
    constructor
    · rintro ((h | h) | h)
      · exact Or.inl h
      · exact Or.inr (ne_of_gt h)
      · exact Or.inr (ne_of_lt h)
    · rintro (h | h)
      · exact Or.inl (Or.inl h)
      · rcases lt_or_gt_of_ne h with h' | h'
        · exact Or.inr h'
        · exact Or.inl (Or.inr h')
  rwa [hset] at h123

lemma Dzc_isPreconnected_Om1 : IsPreconnected Om1 := by
  rw [Dzc_Om1_image]
  exact Dzc_isPreconnected_slitSide.image _ (continuous_const.sub continuous_id).continuousOn

lemma Dzc_isPreconnected_Om1_inter_ball (δ : ℝ) :
    IsPreconnected (Om1 ∩ Metric.ball (1 : ℂ) δ) := by
  by_cases hδ : 0 < δ
  · have h := Work.C17b.isPreconnected_slitBall hδ
    have himg : Om1 ∩ Metric.ball (1 : ℂ) δ
        = (fun u : ℂ => 1 - u) ''
            (Metric.ball (0 : ℂ) δ ∩ {u : ℂ | u.re < 0 ∨ u.im ≠ 0}) := by
      ext z
      constructor
      · rintro ⟨hz1, hz2⟩
        refine ⟨1 - z, ⟨?_, ?_⟩, by ring⟩
        · rw [Metric.mem_ball, Complex.dist_eq]
          have : 1 - z - 0 = -(z - 1) := by ring
          rw [this, norm_neg, ← Complex.dist_eq]
          exact Metric.mem_ball.mp hz2
        · rcases hz1 with him | hre
          · refine Or.inr ?_
            show (1 - z).im ≠ 0
            rw [Complex.sub_im, Complex.one_im, zero_sub, neg_ne_zero]
            exact him
          · refine Or.inl ?_
            show (1 - z).re < 0
            rw [Complex.sub_re, Complex.one_re]
            linarith
      · rintro ⟨u, ⟨hu1, hu2⟩, rfl⟩
        constructor
        · rcases hu2 with hre | him
          · have hre' : u.re < 0 := hre
            right
            show 1 < (1 - u).re
            rw [Complex.sub_re, Complex.one_re]
            linarith
          · have him' : u.im ≠ 0 := him
            left
            show (1 - u).im ≠ 0
            rw [Complex.sub_im, Complex.one_im, zero_sub, neg_ne_zero]
            exact him'
        · have h1 : dist (1 - u) 1 = dist u 0 := by
            rw [Complex.dist_eq, Complex.dist_eq]
            have : 1 - u - 1 = -u := by ring
            rw [this, norm_neg, sub_zero]
          rw [Metric.mem_ball, h1]
          exact Metric.mem_ball.mp hu1
    rw [himg]
    exact h.image _ (continuous_const.sub continuous_id).continuousOn
  · rw [Metric.ball_eq_empty.mpr (by linarith : δ ≤ 0), Set.inter_empty]
    exact isPreconnected_empty

lemma Dzc_PZ_ne_zero_of_mem_Om1 {z : ℂ} (hz : z ∈ Om1) : PZ z ≠ 0 := by
  rcases Om1_trichotomy z hz with h | h | h
  · exact PZ_ne_zero_of_im_pos h
  · exact PZ_ne_zero_of_im_neg h
  · exact PZ_ne_zero_of_mem_SU h.1

/-- `LZ` is `ℂ`-linear in the function (on an open set where `f` is holomorphic). -/
lemma Dzc_LZ_const_mul {U : Set ℂ} (hU : IsOpen U) {c : ℂ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) {z : ℂ} (hz : z ∈ U) :
    LZ (fun w => c * f w) z = c * LZ f z := by
  have hfd : DifferentiableAt ℂ f z := hf.differentiableAt (hU.mem_nhds hz)
  have hd' : DifferentiableOn ℂ (deriv f) U := hf.deriv hU
  have hf'd : DifferentiableAt ℂ (deriv f) z := hd'.differentiableAt (hU.mem_nhds hz)
  have hev : (fun w => deriv (fun v => c * f v) w) =ᶠ[𝓝 z] fun w => c * deriv f w := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact deriv_const_mul c (hf.differentiableAt (hU.mem_nhds hw))
  have h2 : deriv (fun w => deriv (fun v => c * f v) w) z
      = deriv (fun w => c * deriv f w) z := Filter.EventuallyEq.deriv_eq hev
  rw [LZ_def, LZ_def, deriv_const_mul c hfd, h2, deriv_const_mul c hf'd]
  ring

/-- Two solutions of `LZ = 0` on an open preconnected `U` (with `PZ ≠ 0` on `U`) which agree on a
nonempty open subset `V ⊆ U` agree on `U`. -/
lemma Dzc_eqOn_of_agree_open {U V : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hP : ∀ z ∈ U, PZ z ≠ 0) {g₁ g₂ : ℂ → ℂ} (h₁ : DifferentiableOn ℂ g₁ U)
    (h₂ : DifferentiableOn ℂ g₂ U) (hL₁ : ∀ z ∈ U, LZ g₁ z = 0) (hL₂ : ∀ z ∈ U, LZ g₂ z = 0)
    (hVsub : V ⊆ U) (hVo : IsOpen V) (hVne : V.Nonempty) (hag : Set.EqOn g₁ g₂ V) :
    Set.EqOn g₁ g₂ U := by
  obtain ⟨v, hv⟩ := hVne
  have hev : g₁ =ᶠ[𝓝 v] g₂ := by
    filter_upwards [hVo.mem_nhds hv] with w hw
    exact hag hw
  exact eqOn_of_sol_LZ hUo hUc hP h₁ h₂ hL₁ hL₂ (hVsub hv) hev.eq_of_nhds hev.deriv_eq

/-- A solution of `LZ = 0` on `Om1` which vanishes on a nonempty open subset of `Om1` vanishes
on `Om1`. -/
lemma Dzc_eqOn_zero_of_open {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g Om1)
    (hL : ∀ z ∈ Om1, LZ g z = 0) {V : Set ℂ} (hVo : IsOpen V) (hVsub : V ⊆ Om1)
    (hVne : V.Nonempty) (hag : Set.EqOn g 0 V) : ∀ z ∈ Om1, g z = 0 :=
  Dzc_eqOn_of_agree_open Dzc_isOpen_Om1 Dzc_isPreconnected_Om1
    (fun _ hz => Dzc_PZ_ne_zero_of_mem_Om1 hz) hg (differentiableOn_const 0) hL
    (fun z _ => by rw [LZ_def]; simp)
    hVsub hVo hVne hag


/-- `ball 1 δ ∩ Om1` is nonempty for `δ > 0`. -/
lemma Dzc_nonempty_ball_one_inter_Om1 {δ : ℝ} (hδ : 0 < δ) :
    (Metric.ball (1 : ℂ) δ ∩ Om1).Nonempty := by
  refine ⟨1 + ((δ / 2 : ℝ) : ℂ), ?_, ?_⟩
  · rw [Metric.mem_ball, Complex.dist_eq]
    have hsub : 1 + ((δ / 2 : ℝ) : ℂ) - 1 = ((δ / 2 : ℝ) : ℂ) := by ring
    rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  · right
    simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re]
    linarith

/-- If `G · log(· − 1/9) + B = 0` on the upper half of `ball (1/9) δ` (with `G` holomorphic on the
ball and `B` holomorphic on the punctured ball), then it holds everywhere off the real axis in the
ball. -/
lemma Dzc_log_structured_extend {δ : ℝ} (hδ : 0 < δ) {G B : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G (Metric.ball ninth δ))
    (hB : DifferentiableOn ℂ B (Metric.ball ninth δ \ {ninth}))
    (h : ∀ z ∈ halfU δ, G z * Complex.log (z - ninth) + B z = 0) :
    ∀ z ∈ Metric.ball ninth δ, z.im ≠ 0 → G z * Complex.log (z - ninth) + B z = 0 := by
  set F : ℂ → ℂ := fun z => G z * Complex.log (z - ninth) + B z with hFdef
  have hsub1 : slitDisk δ ⊆ Metric.ball ninth δ := Set.inter_subset_left
  have hsub2 : slitDisk δ ⊆ Metric.ball ninth δ \ {ninth} := by
    intro z hz
    refine ⟨hsub1 hz, ?_⟩
    intro hc
    have hmem : ninth ∈ slitComp := by rw [← hc]; exact hz.2
    rcases hmem with him | hre
    · exact him (by simp [ninth])
    · exact absurd hre (lt_irrefl _)
  have hd : DifferentiableOn ℂ F (slitDisk δ) := by
    rw [hFdef]
    refine (hG.mono hsub1).mul ?_ |>.add (hB.mono hsub2)
    intro z hz
    exact ((Complex.differentiableAt_log (slitComp_slitPlane hz.2)).comp z
      (differentiableAt_id.sub_const ninth)).differentiableWithinAt
  have hFzero : ∀ z ∈ slitDisk δ, F z = 0 := by
    obtain ⟨z₀, hz₀⟩ := halfUp_nonempty hδ
    have hz₀' : z₀ ∈ slitDisk δ := ⟨Set.inter_subset_left hz₀, Or.inl (ne_of_gt hz₀.2)⟩
    have hev : F =ᶠ[𝓝 z₀] 0 := by
      filter_upwards [(isOpen_halfUp δ).mem_nhds hz₀] with w hw
      exact h w hw
    have hAn : AnalyticOnNhd ℂ F (slitDisk δ) := hd.analyticOnNhd (isOpen_slitDisk δ)
    exact hAn.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (isPreconnected_slitDisk hδ) hz₀' hev
  intro z hz him
  exact hFzero z ⟨hz, Or.inl him⟩

end Work.A14D
