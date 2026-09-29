import Mathlib
import Submission.Work.TMComp.LocCantor.C8_jump
import Submission.Work.TMComp.Kotani.Objects
import Submission.Work.TMComp.Kotani.mfun_props
import Submission.Work.TMComp.Kotani.EllDerivDefs
import Submission.Work.TMComp.RedC8.ell_harmonicOnNhd

/-!
# (K2): measurability of the "excess" in the energy variable

The excess of the Kotani step is

`excess(E,ε) = ℓ(E+iε)/ε - ∫₀¹ im(-1/defect(E+iε,y)) dy`,

where `ℓ = ell α lam` is the averaged log-modulus of the `m`-function.  Here we show that for
fixed `ε > 0` the slice `E ↦ excess(E,ε)` of the real energy variable is *continuous*, hence
measurable.  Both summands are in fact continuous:

* `E ↦ ℓ(E+iε)` is the composition of `ℓ|ℍ` (continuous on the upper half plane, since it is
  harmonic there — `RedC8.ell_harmonicOnNhd`) with the vertical embedding `E ↦ E+iε`;
* `E ↦ ∫₀¹ im(-1/defect(E+iε,y)) dy` is a parameter integral; the integrand is jointly
  continuous on `ℍ × ℝ` (`continuous_defect_phase`), and since `Im(E+iε) = ε` is constant in
  `E`, the domination `|im(-1/defect)| ≤ 1/‖defect‖ ≤ 1/min(ε,1)` is uniform in `E`
  (`mfun_im_le_defect_im`), so dominated convergence gives continuity of the parameter
  integral.
-/

open MeasureTheory Filter Topology Set

noncomputable section

namespace Work.TMComp.LocCantor

open Work.TMComp.Kotani

/-- The vertical embedding `E ↦ E + iε` of the real axis into `ℂ`. -/
private theorem continuous_vertical (ε : ℝ) :
    Continuous (fun E : ℝ => (E : ℂ) + (ε : ℂ) * Complex.I) :=
  Complex.continuous_ofReal.add continuous_const

/-- The imaginary part of `E + iε` is `ε`. -/
private theorem im_vertical (ε E : ℝ) : ((E : ℂ) + (ε : ℂ) * Complex.I).im = ε := by simp

/-- `E ↦ ℓ(E+iε)` is continuous, as the slice through the upper half plane of the harmonic
(hence continuous) function `ℓ`. -/
private theorem continuous_ell_vertical (α lam : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Continuous (fun E : ℝ => ell α lam ((E : ℂ) + (ε : ℂ) * Complex.I)) := by
  have h : ContinuousOn (fun z : ℂ => ell α lam z) {z : ℂ | 0 < z.im} :=
    InnerProductSpace.HarmonicOnNhd.continuousOn (Work.TMComp.RedC8.ell_harmonicOnNhd α lam)
  have hc := h.comp_continuous (continuous_vertical ε)
    (fun E => by show 0 < ((E : ℂ) + (ε : ℂ) * Complex.I).im; rw [im_vertical]; exact hε)
  simpa [Function.comp_def] using hc

/-- The parametrized integrand `(z,y) ↦ im(-1/defect(z,y))` is continuous on `ℍ × ℝ`. -/
private theorem continuousOn_defect_im (α lam : ℝ) :
    ContinuousOn (fun p : ℂ × ℝ => (-1 / defect α lam p.1 p.2).im)
      {p : ℂ × ℝ | 0 < p.1.im} := by
  have hm1 : ContinuousOn (fun p : ℂ × ℝ => mfun α lam p.1 p.2)
      {p : ℂ × ℝ | 0 < p.1.im} := MfunProbs.mfun_continuousOn α lam
  have hm2 : ContinuousOn (fun p : ℂ × ℝ => mfun α lam p.1 (α - p.2))
      {p : ℂ × ℝ | 0 < p.1.im} := by
    have hmap : ContinuousOn (fun p : ℂ × ℝ => (p.1, α - p.2)) {p : ℂ × ℝ | 0 < p.1.im} :=
      (continuous_fst.prodMk (continuous_const.sub continuous_snd)).continuousOn
    have hcomp := (MfunProbs.mfun_continuousOn α lam).comp hmap (fun p hp => hp)
    have hfun : ((fun q : ℂ × ℝ => mfun α lam q.1 q.2) ∘ fun p : ℂ × ℝ => (p.1, α - p.2))
        = (fun p : ℂ × ℝ => mfun α lam p.1 (α - p.2)) := by
      funext p; rfl
    rwa [hfun] at hcomp
  have hm2n : ∀ p : ℂ × ℝ, p ∈ {p : ℂ × ℝ | 0 < p.1.im} →
      mfun α lam p.1 (α - p.2) ≠ 0 := fun p hp =>
    ne_of_apply_ne Complex.im (ne_of_gt (MfunProbs.mfun_im_pos α lam hp (α - p.2)))
  have hdef : ContinuousOn (fun p : ℂ × ℝ => defect α lam p.1 p.2)
      {p : ℂ × ℝ | 0 < p.1.im} := by
    have hfun : (fun p : ℂ × ℝ => defect α lam p.1 p.2)
        = (fun p : ℂ × ℝ => mfun α lam p.1 p.2 - 1 / mfun α lam p.1 (α - p.2)) := by
      funext p
      rw [defect, sSec]
    rw [hfun]
    have hnum : ContinuousOn (fun _ : ℂ × ℝ => (1 : ℂ)) {p : ℂ × ℝ | 0 < p.1.im} :=
      continuous_const.continuousOn
    exact hm1.sub (hnum.div hm2 hm2n)
  have hne : ∀ p : ℂ × ℝ, p ∈ {p : ℂ × ℝ | 0 < p.1.im} → defect α lam p.1 p.2 ≠ 0 :=
    fun p hp => defect_ne_zero α lam hp p.2
  have h3 : ContinuousOn (fun p : ℂ × ℝ => -1 / defect α lam p.1 p.2)
      {p : ℂ × ℝ | 0 < p.1.im} := by
    have hnum : ContinuousOn (fun _ : ℂ × ℝ => (-1 : ℂ)) {p : ℂ × ℝ | 0 < p.1.im} :=
      continuous_const.continuousOn
    exact hnum.div hdef hne
  exact Complex.continuous_im.comp_continuousOn h3

/-- `E ↦ ∫₀¹ im(-1/defect(E+iε,y)) dy` is continuous: dominated convergence, with the
dominating constant `1/min(ε,1)` coming from `Im(defect) ≥ Im(m) ≥ min(ε,1)`. -/
private theorem continuous_defect_integral_vertical (α lam : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Continuous (fun E : ℝ =>
      ∫ y in (0 : ℝ)..1, (-1 / defect α lam ((E : ℂ) + (ε : ℂ) * Complex.I) y).im) := by
  rw [continuous_iff_continuousAt]
  intro E₀
  have hminpos : 0 < min ε 1 := lt_min hε one_pos
  refine intervalIntegral.continuousAt_of_dominated_interval
    (F := fun (E : ℝ) (y : ℝ) => (-1 / defect α lam ((E : ℂ) + (ε : ℂ) * Complex.I) y).im)
    (x₀ := E₀) (a := 0) (b := 1) (bound := fun _ : ℝ => 1 / min ε 1) ?_ ?_ ?_ ?_
  · filter_upwards with E
    have hE : 0 < ((E : ℂ) + (ε : ℂ) * Complex.I).im := by rw [im_vertical]; exact hε
    exact (Complex.continuous_im.comp (continuous_const.div
      (continuous_defect_phase α lam hE)
      (fun y => defect_ne_zero α lam hE y))).aestronglyMeasurable
  · filter_upwards with E
    filter_upwards with y _
    have hE : 0 < ((E : ℂ) + (ε : ℂ) * Complex.I).im := by rw [im_vertical]; exact hε
    have hlow : min ε 1 ≤ (mfun α lam ((E : ℂ) + (ε : ℂ) * Complex.I) y).im :=
      mfun_im_ge α lam hminpos (min_le_right _ _)
        (by rw [im_vertical]; exact min_le_left ε 1) y
    have hdefge : min ε 1 ≤ (defect α lam ((E : ℂ) + (ε : ℂ) * Complex.I) y).im :=
      le_trans hlow (mfun_im_le_defect_im α lam hE y)
    have hnorm : min ε 1 ≤ ‖defect α lam ((E : ℂ) + (ε : ℂ) * Complex.I) y‖ :=
      le_trans hdefge (Complex.im_le_norm _)
    have h1 : |(-1 / defect α lam ((E : ℂ) + (ε : ℂ) * Complex.I) y).im|
        ≤ 1 / ‖defect α lam ((E : ℂ) + (ε : ℂ) * Complex.I) y‖ := by
      have h1' := Complex.abs_im_le_norm
        ((-1 : ℂ) / defect α lam ((E : ℂ) + (ε : ℂ) * Complex.I) y)
      rwa [norm_div, norm_neg, norm_one] at h1'
    rw [Real.norm_eq_abs]
    exact le_trans h1 (one_div_le_one_div_of_le hminpos hnorm)
  · exact continuous_const.intervalIntegrable 0 1
  · filter_upwards with y _
    have hcont_z : ContinuousOn (fun z : ℂ => (-1 / defect α lam z y).im) {z : ℂ | 0 < z.im} := by
      have hmap : ContinuousOn (fun z : ℂ => (z, y)) {z : ℂ | 0 < z.im} :=
        (continuous_id.prodMk continuous_const).continuousOn
      have hcomp := (continuousOn_defect_im α lam).comp hmap (fun z hz => hz)
      have hfun : ((fun p : ℂ × ℝ => (-1 / defect α lam p.1 p.2).im) ∘ fun z : ℂ => (z, y))
          = (fun z : ℂ => (-1 / defect α lam z y).im) := by
        funext z; rfl
      rwa [hfun] at hcomp
    have hc := hcont_z.comp_continuous (continuous_vertical ε)
      (fun E => by show 0 < ((E : ℂ) + (ε : ℂ) * Complex.I).im; rw [im_vertical]; exact hε)
    simpa [Function.comp_def] using hc.continuousAt

/-- **Target lemma.**  For `ε > 0` the excess `excess(E,ε) = ℓ(E+iε)/ε - ∫₀¹ im(-1/defect(E+iε,·))`
is a measurable function of the real energy `E`: both summands are even continuous in `E`
(`continuous_ell_vertical` and `continuous_defect_integral_vertical` above). -/
theorem K2_excess_measurable (α lam : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Measurable (fun E : ℝ => Work.TMComp.Kotani.ell α lam ((E : ℂ) + (ε : ℂ) * Complex.I) / ε
      - ∫ y in (0 : ℝ)..1, (-1 / Work.TMComp.Kotani.defect α lam ((E : ℂ) + (ε : ℂ) * Complex.I) y).im) :=
  ((continuous_ell_vertical α lam hε).measurable.div_const ε).sub
    (continuous_defect_integral_vertical α lam hε).measurable

end Work.TMComp.LocCantor
