import Mathlib
import Submission.Work.TMComp.Kotani.GlueDefs
import Submission.Work.TMComp.Kotani.Objects
import Submission.Work.TMComp.Kotani.Psi_bounds
import Submission.Work.TMComp.Kotani.mfun_props

/-!
# From a bounded Cayley transform of `Psi` to the local extension of `m`
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMComp.LocCantor

open Work.TMComp.Kotani

/-- The Cayley transform is inverted by `cayleyInv` except at the single point `-I`. -/
lemma extOn_cayleyInv_cayley_of_add_I_ne_zero {w : ℂ} (hw : w + Complex.I ≠ 0) :
    cayleyInv (cayley w) = w := by
  have h1 : (1 : ℂ) + (w - Complex.I) / (w + Complex.I) = 2 * w / (w + Complex.I) := by
    field_simp
    ring
  have h2 : (1 : ℂ) - (w - Complex.I) / (w + Complex.I) = 2 * Complex.I / (w + Complex.I) := by
    field_simp
    ring
  rw [cayleyInv, cayley, h1, h2]
  field_simp

/-- `1/(-1/X) = -X` for every `X`. -/
lemma extOn_one_div_neg_one_div (X : ℂ) : 1 / (-1 / X) = -X := by
  by_cases h : X = 0
  · simp [h]
  · field_simp

/-- `cayleyInv u ≠ 0` for `‖u‖ < 1`. -/
lemma extOn_cayleyInv_ne_zero {u : ℂ} (hu : ‖u‖ < 1) : cayleyInv u ≠ 0 := by
  intro h0
  have h1 : Complex.I * (1 + u) / (1 - u) = 0 := by simpa only [cayleyInv] using h0
  rcases div_eq_zero_iff.mp h1 with h2 | h2
  · have h3 : 1 + u = 0 := by
      rcases mul_eq_zero.mp h2 with h4 | h4
      · exact absurd h4 Complex.I_ne_zero
      · exact h4
    have h4 : u = -1 := by linear_combination h3
    rw [h4] at hu
    simp at hu
  · have h3 : u = 1 := by linear_combination -h2
    rw [h3] at hu
    simp at hu

/-- Outside the axis, `Psi` never takes the value `-I`. -/
lemma extOn_Psi_add_I_ne_zero (α lam : ℝ) (y : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    Psi α lam z y + Complex.I ≠ 0 := by
  intro hcontra
  have hPsi : Psi α lam z y = -Complex.I := by linear_combination hcontra
  have hPsi2 : (-1 : ℂ) / (glued α lam z y - z / 2) = -Complex.I := by
    simpa only [Psi] using hPsi
  have h2 : (1 : ℂ) / (glued α lam z y - z / 2) = Complex.I := by
    have h := hPsi2
    rw [neg_div] at h
    exact neg_inj.mp h
  have h3 : (glued α lam z y - z / 2)⁻¹ = Complex.I := by simpa only [one_div] using h2
  have hX : glued α lam z y - z / 2 = -Complex.I := by
    have h4 := inv_eq_iff_eq_inv.mp h3
    rwa [Complex.inv_I] at h4
  rcases lt_trichotomy z.im 0 with hneg | hzero | hpos
  · rw [glued, if_neg (not_lt.mpr (le_of_lt hneg))] at hX
    have hstar : 0 < (star z).im := by
      simpa [Complex.star_def, Complex.conj_im] using neg_pos.mpr hneg
    have hmpos : 0 < (mfun α lam (star z) (α - y)).im := MfunProbs.mfun_im_pos α lam hstar _
    have hmne : mfun α lam (star z) (α - y) ≠ 0 := fun h0 => by
      rw [h0] at hmpos; simp at hmpos
    have him : ((1 : ℂ) / star (mfun α lam (star z) (α - y))).im = z.im / 2 - 1 := by
      have h := congrArg Complex.im hX
      rw [Complex.sub_im, Complex.div_ofNat_im, Complex.neg_im, Complex.I_im] at h
      linarith
    have hpos' : 0 < ((1 : ℂ) / star (mfun α lam (star z) (α - y))).im := by
      rw [im_one_div_star]
      exact div_pos hmpos (pow_pos (norm_pos_iff.mpr hmne) 2)
    linarith
  · exact hz hzero
  · rw [glued, if_pos hpos] at hX
    have him : (mfun α lam z y).im = z.im / 2 - 1 := by
      have h := congrArg Complex.im hX
      rw [Complex.sub_im, Complex.div_ofNat_im, Complex.neg_im, Complex.I_im] at h
      linarith
    have hge := mfun_im_ge_self α lam hpos y
    linarith

/-- The inverse Cayley transform of an analytic function of modulus `< 1` is analytic. -/
lemma extOn_analyticOnNhd_cayleyInv_comp {E₀ r : ℝ} {G : ℂ → ℂ}
    (hGan : AnalyticOnNhd ℂ G (Metric.ball (E₀ : ℂ) r))
    (hGlt : ∀ z ∈ Metric.ball (E₀ : ℂ) r, ‖G z‖ < 1) :
    AnalyticOnNhd ℂ (fun z => cayleyInv (G z)) (Metric.ball (E₀ : ℂ) r) := by
  have hnum : AnalyticOnNhd ℂ (fun z => Complex.I * (1 + G z)) (Metric.ball (E₀ : ℂ) r) :=
    analyticOnNhd_const.mul (analyticOnNhd_const.add hGan)
  have hden : AnalyticOnNhd ℂ (fun z => (1 : ℂ) - G z) (Metric.ball (E₀ : ℂ) r) :=
    analyticOnNhd_const.sub hGan
  have hne : ∀ z ∈ Metric.ball (E₀ : ℂ) r, ((1 : ℂ) - G z) ≠ 0 := by
    intro z hz hc
    have h1 : G z = 1 := by linear_combination -hc
    have h2 := hGlt z hz
    rw [h1] at h2
    simp at h2
  refine (AnalyticOnNhd.div hnum hden hne).congr Metric.isOpen_ball ?_
  intro z hz
  simp [cayleyInv]

/-- `z ↦ z/2 - 1/cayleyInv (G z)` is analytic wherever `G` is analytic and `‖G‖ < 1`. -/
lemma extOn_analyticOnNhd {E₀ r : ℝ} {G : ℂ → ℂ}
    (hGan : AnalyticOnNhd ℂ G (Metric.ball (E₀ : ℂ) r))
    (hGlt : ∀ z ∈ Metric.ball (E₀ : ℂ) r, ‖G z‖ < 1) :
    AnalyticOnNhd ℂ (fun z => z / 2 - 1 / cayleyInv (G z)) (Metric.ball (E₀ : ℂ) r) := by
  have hU : AnalyticOnNhd ℂ (fun z => cayleyInv (G z)) (Metric.ball (E₀ : ℂ) r) :=
    extOn_analyticOnNhd_cayleyInv_comp hGan hGlt
  have hlin : AnalyticOnNhd ℂ (fun z : ℂ => z / 2) (Metric.ball (E₀ : ℂ) r) :=
    AnalyticOnNhd.div (f := fun z : ℂ => z) (g := fun _ : ℂ => (2 : ℂ))
      analyticOnNhd_id analyticOnNhd_const (fun z hz => by norm_num)
  have hinv : AnalyticOnNhd ℂ (fun z => (1 : ℂ) / cayleyInv (G z)) (Metric.ball (E₀ : ℂ) r) :=
    AnalyticOnNhd.div analyticOnNhd_const hU (fun z hz => extOn_cayleyInv_ne_zero (hGlt z hz))
  refine (hlin.sub hinv).congr Metric.isOpen_ball ?_
  intro z hz
  simp

/-- Off the real axis, `z ↦ z/2 - 1/cayleyInv (G z)` coincides with `glued α lam · y`. -/
lemma extOn_eq_glued_of_im_ne_zero {α lam E₀ r y : ℝ} {G : ℂ → ℂ}
    (hGeq : ∀ z ∈ Metric.ball (E₀ : ℂ) r, z.im ≠ 0 → G z = cayley (Psi α lam z y))
    {z : ℂ} (hz : z ∈ Metric.ball (E₀ : ℂ) r) (hzim : z.im ≠ 0) :
    z / 2 - 1 / cayleyInv (G z) = glued α lam z y := by
  have h1 : cayleyInv (G z) = Psi α lam z y := by
    rw [hGeq z hz hzim, extOn_cayleyInv_cayley_of_add_I_ne_zero (extOn_Psi_add_I_ne_zero α lam y hzim)]
  have h2 : (1 : ℂ) / Psi α lam z y = -(glued α lam z y - z / 2) := by
    rw [show Psi α lam z y = -1 / (glued α lam z y - z / 2) from rfl]
    exact extOn_one_div_neg_one_div _
  rw [h1, h2]
  ring

/-- On the real axis the reconstructed function is still `ℍ`-valued. -/
lemma extOn_im_pos_of_im_eq_zero {z u : ℂ} (hz : z.im = 0) (hu : 0 < u.im) :
    0 < (z / 2 - 1 / u).im := by
  have h1 : (z / 2).im = 0 := by simp [hz]
  have h2 : (1 / u).im = -u.im / ‖u‖ ^ 2 := by
    rw [one_div, Complex.inv_im, Complex.normSq_eq_norm_sq]
  have hne : u ≠ 0 := fun h0 => by rw [h0] at hu; simp at hu
  rw [Complex.sub_im, h1, h2]
  have h4 : (0 : ℝ) - -u.im / ‖u‖ ^ 2 = u.im / ‖u‖ ^ 2 := by ring
  rw [h4]
  exact div_pos hu (pow_pos (norm_pos_iff.mpr hne) 2)

theorem extOn_of_cayley (α lam : ℝ) (E₀ r y : ℝ) (hr : 0 < r) (hG : ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G (Metric.ball (E₀ : ℂ) r) ∧ (∀ z ∈ Metric.ball (E₀ : ℂ) r, ‖G z‖ < 1) ∧ (∀ z ∈ Metric.ball (E₀ : ℂ) r, z.im ≠ 0 → G z = Work.TMComp.Kotani.cayley (Work.TMComp.Kotani.Psi α lam z y))) : Work.TMComp.Kotani.ExtOn α lam E₀ r y := by
  obtain ⟨G, hGan, hGlt, hGeq⟩ := hG
  refine ⟨fun w => w / 2 - 1 / cayleyInv (G w), ?_, ?_, ?_, ?_⟩
  · exact extOn_analyticOnNhd hGan hGlt
  · intro z hz hzim
    show z / 2 - 1 / cayleyInv (G z) = mfun α lam z y
    rw [extOn_eq_glued_of_im_ne_zero hGeq hz (ne_of_gt hzim), glued_of_pos α lam hzim y]
  · intro z hz hzim
    show z / 2 - 1 / cayleyInv (G z) = 1 / star (mfun α lam (star z) (α - y))
    rw [extOn_eq_glued_of_im_ne_zero hGeq hz (ne_of_lt hzim), glued, if_neg (not_lt.mpr (le_of_lt hzim))]
  · intro z hz
    show 0 < (z / 2 - 1 / cayleyInv (G z)).im
    rcases lt_trichotomy z.im 0 with hneg | hzero | hpos
    · rw [extOn_eq_glued_of_im_ne_zero hGeq hz (ne_of_lt hneg), glued,
        if_neg (not_lt.mpr (le_of_lt hneg))]
      have hstar : 0 < (star z).im := by
        simpa [Complex.star_def, Complex.conj_im] using neg_pos.mpr hneg
      simpa only [sigSec] using sigSec_im_pos α lam hstar y
    · exact extOn_im_pos_of_im_eq_zero hzero (im_cayleyInv_pos (hGlt z hz))
    · rw [extOn_eq_glued_of_im_ne_zero hGeq hz (ne_of_gt hpos), glued_of_pos α lam hpos y]
      exact MfunProbs.mfun_im_pos α lam hpos y

end Work.TMComp.LocCantor
