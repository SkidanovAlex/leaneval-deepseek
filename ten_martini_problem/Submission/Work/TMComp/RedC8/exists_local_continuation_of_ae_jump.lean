import Mathlib
import Submission.Work.TMComp.Kotani.Objects
import Submission.Work.TMComp.Kotani.GlueDefs
import Submission.Work.TMComp.Kotani.Psi_bounds
import Submission.Work.TMComp.Kotani.UniformExt
import Submission.Work.TMComp.RedC8.rectangle_extension
import Submission.Work.TMComp.LocCantor.extOn_of_cayley

/-!
# Local continuation of `mfun` from an a.e. small jump

Given the hypothesis that for a.e. phase `y` the jump of `cayley ∘ Psi(·,y)` across the real
axis is small in `L¹(a,b)` along a vanishing sequence, every phase `x` has an analytic
continuation of `mfun α lam · x` across every `E₀ ∈ (a,b)` together with the reflection
formula below the axis and positive imaginary part.

The proof: the smallness condition at a phase `y` gives, by `rectangle_extension` applied to
the (analytic off the axis, bounded by `1`) function `cayley ∘ Psi(·,y)`, an extension across
the whole rectangle `(a,b) × (-1,1)`; restricting to a ball around `E₀` and inverting the
Cayley transform (`LocCantor.extOn_of_cayley`) produces `ExtOn α lam E₀ ρ y` for a *fixed*
radius `ρ > 0`.  The hypotheses hold for a.e. `y`, and `{y | ExtOn α lam E₀ ρ y}` is closed
(`extOn_isClosed`); it is invariant under the integers (`extOn_add_one`), so the a.e.
statement (pushed by the dense group `ℤ + αℤ`, using `extOn_add_alpha`) forces it to be all of
`ℝ`.
-/

namespace Work.TMComp.RedC8

open MeasureTheory Filter Topology Set
open scoped Topology
open Work.TMComp.Kotani
open Work.TMContract

noncomputable section

/-- For a fixed radius `r > 0`, the set of phases `x` for which `mfun α lam · x` continues
analytically to the ball `B(E₀,r)` (with the reflection formula below the axis and positive
imaginary part) is closed. -/
theorem extOn_isClosed (α lam E₀ r : ℝ) (hr : 0 < r) :
    IsClosed {x : ℝ | ExtOn α lam E₀ r x} := by
  have key : ∀ u : ℕ → ℝ, (∀ n, ExtOn α lam E₀ r (u n)) → ∀ x₀ : ℝ,
      Tendsto u atTop (𝓝 x₀) → ExtOn α lam E₀ r x₀ := by
    intro u hu x₀ hutend
    have hw : ∀ n, ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f (Metric.ball (E₀ : ℂ) r) ∧
        (∀ z ∈ Metric.ball (E₀ : ℂ) r, 0 < z.im → f z = mfun α lam z (u n)) ∧
        (∀ z ∈ Metric.ball (E₀ : ℂ) r, z.im < 0 →
          f z = 1 / star (mfun α lam (star z) (α - u n))) ∧
        (∀ z ∈ Metric.ball (E₀ : ℂ) r, 0 < (f z).im) := fun n => hu n
    choose f hfan hfup hfdown hfpos using hw
    have hF : ∀ n, AnalyticOnNhd ℂ (fun z => cayley (f n z)) (Metric.ball (E₀ : ℂ) r) :=
      fun n => analyticOnNhd_cayley_comp (hfan n) (hfpos n)
    have hbg : ∀ n z, z ∈ Metric.ball (E₀ : ℂ) r → ‖cayley (f n z)‖ ≤ 1 :=
      fun n z hz => le_of_lt (norm_cayley_lt_one (hfpos n z hz))
    set g : ℂ → ℂ := fun z => if 0 < z.im then cayley (mfun α lam z x₀)
      else if z.im < 0 then cayley (1 / star (mfun α lam (star z) (α - x₀))) else 0 with hgdef
    have hgpos : ∀ z, 0 < z.im → g z = cayley (mfun α lam z x₀) := by
      intro z hz
      simp only [hgdef]
      rw [if_pos hz]
    have hgneg : ∀ z, z.im < 0 →
        g z = cayley (1 / star (mfun α lam (star z) (α - x₀))) := by
      intro z hz
      simp only [hgdef]
      rw [if_neg (not_lt.mpr (le_of_lt hz)), if_pos hz]
    have hconv : ∀ z ∈ Metric.ball (E₀ : ℂ) r, z.im ≠ 0 →
        Tendsto (fun n => cayley (f n z)) atTop (𝓝 (g z)) := by
      intro z hz hzim
      rcases lt_or_gt_of_ne hzim with hlt | hgt
      · have hcan : ContinuousAt cayley (1 / star (mfun α lam (star z) (α - x₀))) := by
          refine continuousAt_cayley ?_
          intro hc
          have him := inv_star_im_pos (mfun_im_pos' α lam (star_im_neg hlt) (α - x₀))
          rw [hc] at him
          simp at him
          exact absurd him (by norm_num)
        have h2 := hcan.tendsto.comp (tendsto_sig α lam (star_im_neg hlt) hutend)
        rw [hgneg z hlt]
        refine h2.congr' (Eventually.of_forall fun n => ?_)
        simp only [Function.comp_apply]
        rw [hfdown n z hz hlt]
      · have hcan : ContinuousAt cayley (mfun α lam z x₀) := by
          refine continuousAt_cayley ?_
          intro hc
          have him := mfun_im_pos' α lam hgt x₀
          rw [hc] at him
          simp at him
          exact absurd him (by norm_num)
        have h2 := hcan.tendsto.comp (tendsto_mfun α lam hgt hutend)
        rw [hgpos z hgt]
        refine h2.congr' (Eventually.of_forall fun n => ?_)
        simp only [Function.comp_apply]
        rw [hfup n z hz hgt]
    obtain ⟨G, hGan, hGval, hGunif, hGpt⟩ :=
      exists_analyticOnNhd_of_tendsto_offreal (E₀ : ℂ) r hr hF hbg hconv
    have hGle : ∀ z ∈ Metric.ball (E₀ : ℂ) r, ‖G z‖ ≤ 1 :=
      fun z hz => le_of_tendsto' (hGpt z hz).norm fun n => hbg n z hz
    have hGlt : ∀ z ∈ Metric.ball (E₀ : ℂ) r, ‖G z‖ < 1 := by
      intro z hz
      rcases lt_trichotomy (‖G z‖) 1 with hlt | heq | hgt
      · exact hlt
      · exfalso
        have hmax : IsMaxOn (fun w => ‖G w‖) (Metric.ball (E₀ : ℂ) r) z := by
          intro w hw
          show ‖G w‖ ≤ ‖G z‖
          rw [heq]
          exact hGle w hw
        have heqon := Complex.norm_eqOn_of_isPreconnected_of_isMaxOn
          Metric.isPreconnected_ball Metric.isOpen_ball hGan.differentiableOn hz hmax
        set z₂ : ℂ := (E₀ : ℂ) + ((r / 2 : ℝ) : ℂ) * Complex.I with hz₂def
        have hz₂im : 0 < z₂.im := by
          rw [hz₂def]
          simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
            Complex.I_re, Complex.I_im, mul_one, zero_add]
          positivity
        have hz₂mem : z₂ ∈ Metric.ball (E₀ : ℂ) r := by
          rw [Metric.mem_ball, dist_eq_norm, hz₂def,
            show (E₀ : ℂ) + ((r / 2 : ℝ) : ℂ) * Complex.I - (E₀ : ℂ)
              = ((r / 2 : ℝ) : ℂ) * Complex.I by ring,
            norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (by positivity)]
          linarith
        have h1 : ‖G z₂‖ = ‖G z‖ := heqon hz₂mem
        have h2 : ‖G z₂‖ < 1 := by
          rw [hGval z₂ hz₂mem (ne_of_gt hz₂im), hgpos z₂ hz₂im]
          exact norm_cayley_lt_one (mfun_im_pos' α lam hz₂im x₀)
        rw [h1, heq] at h2
        exact lt_irrefl 1 h2
      · exact absurd hgt (not_lt.mpr (hGle z hz))
    have hf_an : AnalyticOnNhd ℂ (fun z => cayleyInv (G z)) (Metric.ball (E₀ : ℂ) r) :=
      analyticOnNhd_cayleyInv_comp hGan hGlt
    refine ⟨fun z => cayleyInv (G z), hf_an, ?_, ?_, ?_⟩
    · intro z hz hzim
      dsimp only
      rw [hGval z hz (ne_of_gt hzim), hgpos z hzim,
        cayleyInv_cayley (mfun_im_pos' α lam hzim x₀)]
    · intro z hz hzim
      dsimp only
      rw [hGval z hz (ne_of_lt hzim), hgneg z hzim,
        cayleyInv_cayley (inv_star_im_pos (mfun_im_pos' α lam (star_im_neg hzim) (α - x₀)))]
    · intro z hz
      dsimp only
      exact im_cayleyInv_pos (hGlt z hz)
  exact IsSeqClosed.isClosed fun u x₀ hu hutend => key u hu x₀ hutend

lemma neg_one_div_im_pos_local {z : ℂ} (hz : 0 < z.im) : 0 < (-1 / z).im := by
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  have h : (-1 / z).im = z.im / ‖z‖ ^ 2 := by
    rw [show (-1 : ℂ) / z = -(1 / z) by rw [neg_div], Complex.neg_im, one_div,
      Complex.inv_im, Complex.normSq_eq_norm_sq]
    ring
  rw [h]
  exact div_pos hz (by positivity)

lemma differentiableOn_union_of_isOpen {f : ℂ → ℂ} {s t : Set ℂ} (hs : IsOpen s) (ht : IsOpen t)
    (hfs : DifferentiableOn ℂ f s) (hft : DifferentiableOn ℂ f t) :
    DifferentiableOn ℂ f (s ∪ t) := by
  intro x hx
  rcases hx with hx | hx
  · exact ((hfs x hx).differentiableAt (hs.mem_nhds hx)).differentiableWithinAt
  · exact ((hft x hx).differentiableAt (ht.mem_nhds hx)).differentiableWithinAt

lemma Psi_im_pos_offaxis (α lam y : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    0 < (Psi α lam z y).im := by
  rcases lt_or_gt_of_ne hz with hlt | hgt
  · rw [Psi, glued_of_neg α lam hlt rfl y]
    refine neg_one_div_im_pos_local ?_
    have h1 : 0 < (sigSec α lam (star z) y).im := sigSec_im_pos α lam (star_im_neg hlt) y
    have h2 : (star z).im = -z.im := by simp [Complex.star_def]
    simp only [Complex.sub_im, Complex.div_ofNat_im, h2]
    linarith
  · rw [Psi, glued_of_pos α lam hgt y]
    refine neg_one_div_im_pos_local ?_
    have h1 : z.im ≤ (mfun α lam z y).im := mfun_im_ge_self α lam hgt y
    simp only [Complex.sub_im, Complex.div_ofNat_im]
    linarith

lemma differentiableOn_inv_star_mfun_neg (α lam y : ℝ) :
    DifferentiableOn ℂ (fun z => 1 / star (mfun α lam (star z) (α - y))) {z : ℂ | z.im < 0} := by
  intro x hx
  have hxi : 0 < (star x).im := star_im_neg hx
  have hd : DifferentiableAt ℂ (fun u => 1 / mfun α lam u (α - y)) (star x) := by
    have hm : DifferentiableAt ℂ (fun u => mfun α lam u (α - y)) (star x) :=
      ((MfunProbs.mfun_differentiableOn α lam (α - y)).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hxi))
    refine DifferentiableAt.div (differentiableAt_const (1 : ℂ)) hm ?_
    exact ne_of_apply_ne Complex.im (ne_of_gt (MfunProbs.mfun_im_pos α lam hxi (α - y)))
  have h2 := hd.conj_conj
  simpa [Complex.star_def, Function.comp_def] using h2.differentiableWithinAt

lemma differentiableOn_cayley_Psi_upper (α lam y : ℝ) :
    DifferentiableOn ℂ (fun z => cayley (Psi α lam z y)) {z : ℂ | 0 < z.im} := by
  set φ : ℂ → ℂ := fun z => mfun α lam z y - z / 2 with hφ
  have hφdiff : DifferentiableOn ℂ φ {z : ℂ | 0 < z.im} := by
    rw [hφ]
    exact (MfunProbs.mfun_differentiableOn α lam y).sub (differentiableOn_id.div_const 2)
  have hφim : ∀ z ∈ {z : ℂ | 0 < z.im}, 0 < (φ z).im := by
    intro z hz
    have hzi : 0 < z.im := hz
    have him : (φ z).im = (mfun α lam z y).im - z.im / 2 := by
      rw [hφ]; simp only [Complex.sub_im, Complex.div_ofNat_im]
    have hge : z.im ≤ (mfun α lam z y).im := mfun_im_ge_self α lam hzi y
    rw [him]; linarith
  have hφne : ∀ z ∈ {z : ℂ | 0 < z.im}, φ z ≠ 0 := by
    intro z hz h0
    have hpos := hφim z hz
    rw [h0] at hpos; simp at hpos
  have hψ : DifferentiableOn ℂ (fun z => -1 / φ z) {z : ℂ | 0 < z.im} :=
    (differentiableOn_const (-1 : ℂ)).div hφdiff hφne
  have hψne : ∀ z ∈ {z : ℂ | 0 < z.im}, (-1 / φ z) + Complex.I ≠ 0 := by
    intro z hz h0
    have hpos : 0 < (-1 / φ z).im := neg_one_div_im_pos_local (hφim z hz)
    have hz0 : ((-1 / φ z) + Complex.I).im = 0 := by rw [h0]; simp
    simp only [Complex.add_im, Complex.I_im] at hz0
    linarith
  have hnum : DifferentiableOn ℂ (fun z => -1 / φ z - Complex.I) {z : ℂ | 0 < z.im} :=
    hψ.sub (differentiableOn_const _)
  have hden : DifferentiableOn ℂ (fun z => -1 / φ z + Complex.I) {z : ℂ | 0 < z.im} :=
    hψ.add (differentiableOn_const _)
  have hdiv : DifferentiableOn ℂ (fun z => cayley (-1 / φ z)) {z : ℂ | 0 < z.im} :=
    hnum.div hden hψne
  refine hdiv.congr (fun z hz => ?_)
  congr 1
  rw [Psi, glued_of_pos α lam hz y]

lemma differentiableOn_cayley_Psi_lower (α lam y : ℝ) :
    DifferentiableOn ℂ (fun z => cayley (Psi α lam z y)) {z : ℂ | z.im < 0} := by
  set φ : ℂ → ℂ := fun z => 1 / star (mfun α lam (star z) (α - y)) - z / 2 with hφ
  have hφdiff : DifferentiableOn ℂ φ {z : ℂ | z.im < 0} := by
    rw [hφ]
    exact (differentiableOn_inv_star_mfun_neg α lam y).sub (differentiableOn_id.div_const 2)
  have hφim : ∀ z ∈ {z : ℂ | z.im < 0}, 0 < (φ z).im := by
    intro z hz
    have him : (φ z).im = (sigSec α lam (star z) y).im - z.im / 2 := by
      rw [hφ]; simp only [Complex.sub_im, Complex.div_ofNat_im, sigSec]
    have hzi : z.im < 0 := hz
    have h1 : 0 < (sigSec α lam (star z) y).im := sigSec_im_pos α lam (star_im_neg hzi) y
    rw [him]; linarith
  have hφne : ∀ z ∈ {z : ℂ | z.im < 0}, φ z ≠ 0 := by
    intro z hz h0
    have hpos := hφim z hz
    rw [h0] at hpos; simp at hpos
  have hψ : DifferentiableOn ℂ (fun z => -1 / φ z) {z : ℂ | z.im < 0} :=
    (differentiableOn_const (-1 : ℂ)).div hφdiff hφne
  have hψne : ∀ z ∈ {z : ℂ | z.im < 0}, (-1 / φ z) + Complex.I ≠ 0 := by
    intro z hz h0
    have hpos : 0 < (-1 / φ z).im := neg_one_div_im_pos_local (hφim z hz)
    have hz0 : ((-1 / φ z) + Complex.I).im = 0 := by rw [h0]; simp
    simp only [Complex.add_im, Complex.I_im] at hz0
    linarith
  have hnum : DifferentiableOn ℂ (fun z => -1 / φ z - Complex.I) {z : ℂ | z.im < 0} :=
    hψ.sub (differentiableOn_const _)
  have hden : DifferentiableOn ℂ (fun z => -1 / φ z + Complex.I) {z : ℂ | z.im < 0} :=
    hψ.add (differentiableOn_const _)
  have hdiv : DifferentiableOn ℂ (fun z => cayley (-1 / φ z)) {z : ℂ | z.im < 0} :=
    hnum.div hden hψne
  refine hdiv.congr (fun z hz => ?_)
  congr 1
  rw [Psi, glued_of_neg α lam hz rfl y]
  simp only [sigSec, hφ]

lemma differentiableOn_cayley_Psi_offaxis (α lam y : ℝ) :
    DifferentiableOn ℂ (fun z => cayley (Psi α lam z y)) {z : ℂ | z.im ≠ 0} := by
  have hs : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have ht : IsOpen {z : ℂ | z.im < 0} := isOpen_lt Complex.continuous_im continuous_const
  have hunion : DifferentiableOn ℂ (fun z => cayley (Psi α lam z y))
      ({z : ℂ | 0 < z.im} ∪ {z : ℂ | z.im < 0}) :=
    differentiableOn_union_of_isOpen hs ht
      (differentiableOn_cayley_Psi_upper α lam y) (differentiableOn_cayley_Psi_lower α lam y)
  refine hunion.mono ?_
  intro z hz
  rcases lt_or_gt_of_ne hz with h | h
  · exact Or.inr h
  · exact Or.inl h

theorem extOn_of_jump (α lam a b E₀ y ρ : ℝ) (hab : a < b) (hE₀ : E₀ ∈ Set.Ioo a b)
    (hρ0 : 0 < ρ) (hρa : ρ ≤ E₀ - a) (hρb : ρ ≤ b - E₀) (hρ1 : ρ ≤ 1)
    (hjump : ∃ e : ℕ → ℝ, (∀ j : ℕ, 0 < e j ∧ e j < 1) ∧ Filter.Tendsto e Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun j : ℕ => ∫ x in Set.Icc a b,
        ‖cayley (Psi α lam ((x : ℂ) + (e j : ℂ) * Complex.I) y)
          - cayley (Psi α lam ((x : ℂ) - (e j : ℂ) * Complex.I) y)‖)
        Filter.atTop (nhds 0)) :
    ExtOn α lam E₀ ρ y := by
  set g : ℂ → ℂ := fun z => cayley (Psi α lam z y) with hg
  have hhol : DifferentiableOn ℂ g {z : ℂ | z.im ≠ 0} := differentiableOn_cayley_Psi_offaxis α lam y
  have hU : IsOpen {z : ℂ | z.im ≠ 0} :=
    Complex.continuous_im.isOpen_preimage _ isOpen_ne
  have hbound : ∀ z : ℂ, z.re ∈ Set.Icc a b → z.im ∈ Set.Icc (-1) 1 → z.im ≠ 0 → ‖g z‖ ≤ 1 := by
    intro z _ _ hz
    exact le_of_lt (norm_cayley_lt_one (Psi_im_pos_offaxis α lam y hz))
  have hjump' : ∃ e : ℕ → ℝ, (∀ j : ℕ, 0 < e j ∧ e j < (1:ℝ)) ∧ Filter.Tendsto e Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun j : ℕ => ∫ x in Set.Icc a b,
        ‖g ((x : ℂ) + (e j : ℂ) * Complex.I) - g ((x : ℂ) - (e j : ℂ) * Complex.I)‖)
        Filter.atTop (nhds 0) := by
    obtain ⟨e, he, he0, hlim⟩ := hjump
    exact ⟨e, he, he0, hlim⟩
  obtain ⟨G, hGdiff, hGval⟩ := rectangle_extension (a₁ := a) (b₁ := b) (h := 1) (M := 1)
    hab one_pos hU (fun z _ _ hz => hz) hhol hbound hjump'
  have hRopen : IsOpen {z : ℂ | z.re ∈ Set.Ioo a b ∧ z.im ∈ Set.Ioo (-1:ℝ) 1} := by
    have h1 : IsOpen {z : ℂ | z.re ∈ Set.Ioo a b} := by
      rw [show {z : ℂ | z.re ∈ Set.Ioo a b} = {z : ℂ | a < z.re} ∩ {z : ℂ | z.re < b} by
        ext z; simp only [Set.mem_ofPred_eq, Set.mem_Ioo, Set.mem_inter_iff]]
      exact (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    have h2 : IsOpen {z : ℂ | z.im ∈ Set.Ioo (-1:ℝ) 1} := by
      rw [show {z : ℂ | z.im ∈ Set.Ioo (-1:ℝ) 1} = {z : ℂ | (-1:ℝ) < z.im} ∩ {z : ℂ | z.im < 1} by
        ext z; simp only [Set.mem_ofPred_eq, Set.mem_Ioo, Set.mem_inter_iff]]
      exact (isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt Complex.continuous_im continuous_const)
    rw [show {z : ℂ | z.re ∈ Set.Ioo a b ∧ z.im ∈ Set.Ioo (-1:ℝ) 1}
        = {z : ℂ | z.re ∈ Set.Ioo a b} ∩ {z : ℂ | z.im ∈ Set.Ioo (-1:ℝ) 1} by
      ext z; simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]]
    exact h1.inter h2
  have hGanR : AnalyticOnNhd ℂ G {z : ℂ | z.re ∈ Set.Ioo a b ∧ z.im ∈ Set.Ioo (-1:ℝ) 1} :=
    (Complex.analyticOnNhd_iff_differentiableOn hRopen).mpr hGdiff
  have hsub : Metric.ball (E₀:ℂ) ρ ⊆ {z : ℂ | z.re ∈ Set.Ioo a b ∧ z.im ∈ Set.Ioo (-1:ℝ) 1} := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have hZn : ‖z - (E₀:ℂ)‖ < ρ := hz
    have hre : |z.re - E₀| ≤ ‖z - (E₀:ℂ)‖ := by
      simpa [Complex.sub_re] using Complex.abs_re_le_norm (z - (E₀:ℂ))
    have him : |z.im| ≤ ‖z - (E₀:ℂ)‖ := by
      simpa [Complex.sub_im] using Complex.abs_im_le_norm (z - (E₀:ℂ))
    have hlt_re : |z.re - E₀| < ρ := lt_of_le_of_lt hre hZn
    have hlt_im : |z.im| < ρ := lt_of_le_of_lt him hZn
    rw [Set.mem_ofPred_eq, Set.mem_Ioo, Set.mem_Ioo]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · have := (abs_lt.mp hlt_re).1; linarith
    · have := (abs_lt.mp hlt_re).2; linarith
    · have := (abs_lt.mp hlt_im).1; linarith
    · have := (abs_lt.mp hlt_im).2; linarith
  have hGan : AnalyticOnNhd ℂ G (Metric.ball (E₀:ℂ) ρ) := hGanR.mono hsub
  have hGval' : ∀ z ∈ Metric.ball (E₀:ℂ) ρ, z.im ≠ 0 → G z = cayley (Psi α lam z y) := by
    intro z hz hzim
    have h1 := hGval z (hsub hz).1 (hsub hz).2 hzim
    rw [hg] at h1
    exact h1
  have hGle : ∀ z ∈ Metric.ball (E₀:ℂ) ρ, ‖G z‖ ≤ 1 := by
    intro z hz
    rcases eq_or_ne z.im 0 with hzim | hzim
    · have hzd : dist z (E₀:ℂ) < ρ := by rwa [Metric.mem_ball] at hz
      obtain ⟨η, hη0, hηρ⟩ : ∃ η : ℝ, 0 < η ∧ dist z (E₀:ℂ) + η < ρ :=
        ⟨(ρ - dist z (E₀:ℂ)) / 2, by linarith, by linarith⟩
      have hcontG : ContinuousAt (fun w : ℂ => ‖G w‖) z :=
        ((hGan z hz).differentiableAt).continuousAt.norm
      have h1 : Tendsto (fun n : ℕ => (η / ((n:ℝ) + 1) : ℝ)) atTop (𝓝 0) := by
        have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul η
        simpa [div_eq_mul_inv] using this
      have h2 : Tendsto (fun n : ℕ => (((η / ((n:ℝ) + 1)) : ℝ) : ℂ)) atTop (𝓝 0) := by
        have hc := (Complex.continuous_ofReal.tendsto 0).comp h1
        simp only [Function.comp_def] at hc
        exact hc
      have h3 : Tendsto (fun n : ℕ => (((η / ((n:ℝ) + 1)) : ℝ) : ℂ) * Complex.I) atTop (𝓝 0) := by
        simpa using h2.mul tendsto_const_nhds
      have h4 : Tendsto (fun n : ℕ => z + (((η / ((n:ℝ) + 1)) : ℝ) : ℂ) * Complex.I) atTop (𝓝 z) := by
        simpa using tendsto_const_nhds.add h3
      have hlim : Tendsto (fun n : ℕ => ‖G (z + (((η / ((n:ℝ) + 1)) : ℝ) : ℂ) * Complex.I)‖)
          atTop (𝓝 ‖G z‖) := hcontG.tendsto.comp h4
      refine le_of_tendsto' hlim ?_
      intro n
      have hmem : z + (((η / ((n:ℝ) + 1)) : ℝ) : ℂ) * Complex.I ∈ Metric.ball (E₀:ℂ) ρ := by
        rw [Metric.mem_ball, dist_eq_norm]
        have hsplit : z + (((η / ((n:ℝ) + 1)) : ℝ) : ℂ) * Complex.I - (E₀:ℂ)
            = (z - (E₀:ℂ)) + (((η / ((n:ℝ) + 1)) : ℝ) : ℂ) * Complex.I := by ring
        rw [hsplit]
        calc ‖(z - (E₀:ℂ)) + (((η / ((n:ℝ) + 1)) : ℝ) : ℂ) * Complex.I‖
            ≤ ‖z - (E₀:ℂ)‖ + ‖(((η / ((n:ℝ) + 1)) : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
          _ = ‖z - (E₀:ℂ)‖ + η / ((n:ℝ) + 1) := by
              rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg (by positivity)]
          _ ≤ ‖z - (E₀:ℂ)‖ + η := by
              have hle : η / ((n:ℝ) + 1) ≤ η := by
                rw [div_le_iff₀ (by positivity)]
                have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
                nlinarith [hn0, hη0]
              linarith
          _ < ρ := by
              have h1 : ‖z - (E₀:ℂ)‖ = dist z (E₀:ℂ) := by rw [dist_eq_norm]
              rw [h1]; linarith
      have hne : (z + (((η / ((n:ℝ) + 1)) : ℝ) : ℂ) * Complex.I).im ≠ 0 := by
        simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_one]
        rw [hzim, zero_add]
        positivity
      rw [hGval' _ hmem hne]
      exact le_of_lt (norm_cayley_lt_one (Psi_im_pos_offaxis α lam y hne))
    · rw [hGval' z hz hzim]
      exact le_of_lt (norm_cayley_lt_one (Psi_im_pos_offaxis α lam y hzim))
  have hGlt : ∀ z ∈ Metric.ball (E₀:ℂ) ρ, ‖G z‖ < 1 := by
    intro z hz
    rcases lt_trichotomy (‖G z‖) 1 with h | h | h
    · exact h
    · exfalso
      have hmax : IsMaxOn (fun w => ‖G w‖) (Metric.ball (E₀:ℂ) ρ) z := by
        intro w hw
        show ‖G w‖ ≤ ‖G z‖
        rw [h]
        exact hGle w hw
      have heqon := Complex.norm_eqOn_of_isPreconnected_of_isMaxOn
        Metric.isPreconnected_ball Metric.isOpen_ball hGan.differentiableOn hz hmax
      set z₂ : ℂ := (E₀:ℂ) + ((ρ / 2 : ℝ) : ℂ) * Complex.I with hz₂def
      have hz₂im : 0 < z₂.im := by
        rw [hz₂def]
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_re, Complex.I_im, mul_one, zero_add]
        positivity
      have hz₂mem : z₂ ∈ Metric.ball (E₀:ℂ) ρ := by
        rw [Metric.mem_ball, dist_eq_norm, hz₂def,
          show (E₀:ℂ) + ((ρ / 2 : ℝ) : ℂ) * Complex.I - (E₀:ℂ)
            = ((ρ / 2 : ℝ) : ℂ) * Complex.I by ring,
          norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by positivity)]
        linarith
      have h1 : ‖G z₂‖ = ‖G z‖ := heqon hz₂mem
      have h2 : ‖G z₂‖ < 1 := by
        rw [hGval' z₂ hz₂mem (ne_of_gt hz₂im)]
        exact norm_cayley_lt_one (Psi_im_pos_offaxis α lam y (ne_of_gt hz₂im))
      rw [h1, h] at h2
      exact lt_irrefl 1 h2
    · exact absurd h (not_lt.mpr (hGle z hz))
  exact Work.TMComp.LocCantor.extOn_of_cayley α lam E₀ ρ y hρ0 ⟨G, hGan, hGlt, hGval'⟩

theorem exists_local_continuation_of_ae_jump (α lam a b : ℝ) (hα : Irrational α) (hab : a < b) (hae : ∀ᵐ y ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)), ∃ e : ℕ → ℝ, (∀ j : ℕ, 0 < e j ∧ e j < 1) ∧ Filter.Tendsto e Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun j : ℕ => ∫ E in a..b, ‖Work.TMComp.Kotani.cayley (Work.TMComp.Kotani.Psi α lam ((E : ℂ) + (e j : ℂ) * Complex.I) y) - Work.TMComp.Kotani.cayley (Work.TMComp.Kotani.Psi α lam ((E : ℂ) - (e j : ℂ) * Complex.I) y)‖) Filter.atTop (nhds 0)) : ∀ E₀ ∈ Set.Ioo a b, ∀ x : ℝ, ∃ f : ℂ → ℂ, AnalyticAt ℂ f (E₀ : ℂ) ∧ (∀ᶠ E in nhds (E₀ : ℂ), 0 < E.im → f E = Work.TMComp.Kotani.mfun α lam E x) ∧ (∀ᶠ E in nhds (E₀ : ℂ), E.im < 0 → f E = 1 / star (Work.TMComp.Kotani.mfun α lam (star E) (α - x))) ∧ (∀ᶠ E in nhds (E₀ : ℂ), 0 < (f E).im) := by
  intro E₀ hE₀ x
  set ρ : ℝ := min (min (E₀ - a) (b - E₀)) 1 with hρdef
  have hρ0 : 0 < ρ := by
    rw [hρdef]
    have h1 : 0 < E₀ - a := by linarith [hE₀.1]
    have h2 : 0 < b - E₀ := by linarith [hE₀.2]
    exact lt_min (lt_min h1 h2) one_pos
  have hρa : ρ ≤ E₀ - a := by
    rw [hρdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hρb : ρ ≤ b - E₀ := by
    rw [hρdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hρ1 : ρ ≤ 1 := by rw [hρdef]; exact min_le_right _ _
  have hgood : ∀ᵐ y ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)),
      ExtOn α lam E₀ ρ y := by
    filter_upwards [hae] with y hy
    obtain ⟨e, he, he0, hlim⟩ := hy
    refine extOn_of_jump α lam a b E₀ y ρ hab hE₀ hρ0 hρa hρb hρ1 ⟨e, he, he0, ?_⟩
    have hfun : (fun j : ℕ => (∫ E in a..b,
          ‖cayley (Psi α lam ((E : ℂ) + (e j : ℂ) * Complex.I) y)
            - cayley (Psi α lam ((E : ℂ) - (e j : ℂ) * Complex.I) y)‖))
        = (fun j : ℕ => ∫ x in Set.Icc a b,
          ‖cayley (Psi α lam ((x : ℂ) + (e j : ℂ) * Complex.I) y)
            - cayley (Psi α lam ((x : ℂ) - (e j : ℂ) * Complex.I) y)‖) := by
      funext j
      rw [intervalIntegral.integral_of_le hab.le]
      exact (MeasureTheory.integral_Icc_eq_integral_Ioc
        (f := fun t : ℝ => ‖cayley (Psi α lam ((t : ℂ) + (e j : ℂ) * Complex.I) y)
            - cayley (Psi α lam ((t : ℂ) - (e j : ℂ) * Complex.I) y)‖) (x := a) (y := b)).symm
    rw [hfun] at hlim
    exact hlim
  have hclosed : IsClosed {y : ℝ | ExtOn α lam E₀ ρ y} := extOn_isClosed α lam E₀ ρ hρ0
  have hne : ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ioc (0:ℝ) 1)) Set.univ ≠ 0 := by
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc]
    simp
  have hnonempty : ∃ y : ℝ, ExtOn α lam E₀ ρ y := by
    by_contra hcon
    push_neg at hcon
    have h1 : ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ioc (0:ℝ) 1))
        {y : ℝ | ¬ ExtOn α lam E₀ ρ y} = 0 := MeasureTheory.ae_iff.mp hgood
    have h2 : {y : ℝ | ¬ ExtOn α lam E₀ ρ y} = Set.univ := by
      ext y; simp [hcon y]
    rw [h2] at h1
    exact hne h1
  obtain ⟨y₀, hy₀⟩ := hnonempty
  have hGamma_dense : Dense ((AddSubgroup.closure ({α, 1} : Set ℝ)) : Set ℝ) := by
    rw [dense_addSubgroupClosure_pair_iff]
    simpa using hα
  have hinv : ∀ (γ : ℝ), γ ∈ AddSubgroup.closure ({α, 1} : Set ℝ) →
      ∀ y : ℝ, (ExtOn α lam E₀ ρ (y + γ) ↔ ExtOn α lam E₀ ρ y) := by
    intro γ hγ
    refine AddSubgroup.closure_induction (p := fun g _ => ∀ x : ℝ,
      (ExtOn α lam E₀ ρ (x + g) ↔ ExtOn α lam E₀ ρ x)) ?_ ?_ ?_ ?_ hγ
    · intro z hz x
      rcases hz with h | h
      · rw [h]; exact extOn_add_alpha α lam
      · rw [h]; exact extOn_add_one α lam
    · intro x; simp
    · intro y z hy hz hyC hzC x
      rw [show x + (y + z) = (x + y) + z by ring, hzC, hyC]
    · intro y hy hyC x
      have h := hyC (x + -y)
      rw [show (x + -y) + y = x by ring] at h
      exact h.symm
  have hall : ∀ y : ℝ, ExtOn α lam E₀ ρ y := by
    intro y
    have hx : y - y₀ ∈ closure ((AddSubgroup.closure ({α, 1} : Set ℝ)) : Set ℝ) := by
      rw [hGamma_dense.closure_eq]; exact Set.mem_univ _
    have hmem : y ∈ closure {z : ℝ | ExtOn α lam E₀ ρ z} := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      obtain ⟨γ, hγ, hγd⟩ := Metric.mem_closure_iff.mp hx ε hε
      refine ⟨y₀ + γ, (hinv γ hγ y₀).mpr hy₀, ?_⟩
      have hsplit : y - (y₀ + γ) = (y - y₀) - γ := by ring
      simpa only [dist_eq_norm, hsplit] using hγd
    rw [hclosed.closure_eq] at hmem
    exact hmem
  obtain ⟨f, hfan, hfup, hfdown, hfpos⟩ := hall x
  refine ⟨f, hfan (E₀ : ℂ) ?_, ?_, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_self]; exact hρ0
  · filter_upwards [Metric.ball_mem_nhds (E₀ : ℂ) hρ0] with E hE him
    exact hfup E hE him
  · filter_upwards [Metric.ball_mem_nhds (E₀ : ℂ) hρ0] with E hE him
    exact hfdown E hE him
  · filter_upwards [Metric.ball_mem_nhds (E₀ : ℂ) hρ0] with E hE
    exact hfpos E hE

end

end Work.TMComp.RedC8
