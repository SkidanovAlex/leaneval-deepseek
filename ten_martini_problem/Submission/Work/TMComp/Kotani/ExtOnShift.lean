import Mathlib
import Submission.Work.TMComp.Kotani.GlueDefs

/-!
# Invariance of the local continuability of `mfun`

The set of `x` for which `mfun α lam · x` continues analytically across the real point `E₀`
(with the reflection formula below the axis and positive imaginary part) is invariant under the
translation group `ℤ + αℤ` and under the reflection `x ↦ α - x`.
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMComp.Kotani

open Work.TMContract

theorem mfun_period_one (α lam : ℝ) (E : ℂ) (y : ℝ) :
    mfun α lam E (y + 1) = mfun α lam E y := (mfun_props α lam).2.2.2.2.2.2 E y

theorem mfun_cov (α lam : ℝ) {E : ℂ} (hE : 0 < E.im) (y : ℝ) :
    mfun α lam E (y + α)
      = E - ((pot lam y : ℝ) : ℂ) - 1 / mfun α lam E y := (mfun_props α lam).2.2.2.1 E hE y

theorem mfun_im_pos' (α lam : ℝ) {E : ℂ} (hE : 0 < E.im) (y : ℝ) :
    0 < (mfun α lam E y).im := (mfun_props α lam).2.1 E hE y

theorem star_one_div (w : ℂ) : star (1 / w) = 1 / star w := by
  simpa [one_div] using star_inv w

theorem im_neg_inv_pos {w : ℂ} (hw : 0 < w.im) : 0 < (-(1 / w)).im := by
  rw [one_div, Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
  exact div_pos hw (Complex.normSq_pos.mpr (ne_of_apply_ne Complex.im (ne_of_gt hw)))

theorem inv_star_im_pos {w : ℂ} (hw : 0 < w.im) : 0 < (1 / star w).im := by
  rw [show (1 : ℂ) / star w = star (1 / w) from (star_one_div w).symm, Complex.star_def,
    Complex.conj_im]
  exact im_neg_inv_pos hw

/-- The identity behind the lower-half clause for the shifted index `x + α`. -/
theorem one_div_star_mfun_eq (α lam : ℝ) {E : ℂ} (hE : 0 < E.im) (x : ℝ) :
    1 / star (mfun α lam E (-x))
      = star E - ((pot lam x : ℝ) : ℂ) - star (mfun α lam E (α - x)) := by
  have h := mfun_cov α lam hE (-x)
  have hpot : ((pot lam (-x) : ℝ) : ℂ) = ((pot lam x : ℝ) : ℂ) := by rw [pot_even]
  rw [hpot, show -x + α = α - x by ring] at h
  have hstar : star (mfun α lam E (α - x))
      = star E - ((pot lam x : ℝ) : ℂ) - 1 / star (mfun α lam E (-x)) := by
    simpa using congrArg star h
  rw [hstar]
  ring

/-- `z ↦ star z` preserves balls centred at real points. -/
theorem star_mem_ball {E₀ r : ℝ} {z : ℂ} (hz : z ∈ Metric.ball (E₀ : ℂ) r) :
    star z ∈ Metric.ball (E₀ : ℂ) r := by
  have h : star z - (E₀ : ℂ) = star (z - (E₀ : ℂ)) := by simp
  rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
  rw [h, Complex.star_def, Complex.norm_conj]
  exact hz

theorem star_im_neg {z : ℂ} (hz : z.im < 0) : 0 < (star z).im := by
  simpa [Complex.star_def, Complex.conj_im] using hz

theorem star_im_pos {z : ℂ} (hz : 0 < z.im) : (star z).im < 0 := by
  simpa [Complex.star_def, Complex.conj_im] using hz

/-- Analyticity of `z ↦ 1 / star (f (star z))`. -/
theorem analyticOnNhd_inv_star_conj {E₀ r : ℝ} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.ball (E₀ : ℂ) r))
    (hpos : ∀ z ∈ Metric.ball (E₀ : ℂ) r, 0 < (f z).im) :
    AnalyticOnNhd ℂ (fun z => 1 / star (f (star z))) (Metric.ball (E₀ : ℂ) r) := by
  have hdiff : DifferentiableOn ℂ (fun z => star (f (star z))) (Metric.ball (E₀ : ℂ) r) := by
    intro z hz
    have hzd : DifferentiableAt ℂ f (star z) := (hf (star z) (star_mem_ball hz)).differentiableAt
    have h := hzd.conj_conj
    simpa [Complex.star_def, Function.comp_def] using h.differentiableWithinAt
  have han : AnalyticOnNhd ℂ (fun z => star (f (star z))) (Metric.ball (E₀ : ℂ) r) :=
    hdiff.analyticOnNhd Metric.isOpen_ball
  refine AnalyticOnNhd.congr Metric.isOpen_ball (han.inv ?_) ?_
  · intro z hz
    exact star_ne_zero.mpr (ne_of_apply_ne Complex.im (ne_of_gt (hpos (star z) (star_mem_ball hz))))
  · intro z hz
    simp [one_div]

/-- Translation invariance in `x` by `1`. -/
theorem extOn_add_one (α lam : ℝ) {E₀ r x : ℝ} :
    ExtOn α lam E₀ r (x + 1) ↔ ExtOn α lam E₀ r x := by
  constructor <;> intro h <;> obtain ⟨f, han, hup, hdown, hpos⟩ := h
  · refine ⟨f, han, fun z hz hzim => ?_, fun z hz hzim => ?_, hpos⟩
    · rw [hup z hz hzim, mfun_period_one α lam z x]
    · rw [hdown z hz hzim, show α - (x + 1) = (α - x) - 1 by ring,
        ← mfun_period_one α lam (star z) (α - x - 1), show α - x - 1 + 1 = α - x by ring]
  · refine ⟨f, han, fun z hz hzim => ?_, fun z hz hzim => ?_, hpos⟩
    · rw [hup z hz hzim, mfun_period_one α lam z x]
    · rw [hdown z hz hzim, show α - (x + 1) = (α - x) - 1 by ring,
        ← mfun_period_one α lam (star z) (α - x - 1), show α - x - 1 + 1 = α - x by ring]


/-- Invariance under the reflection `x ↦ α - x`. -/
theorem extOn_reflect (α lam : ℝ) {E₀ r x : ℝ} :
    ExtOn α lam E₀ r (α - x) ↔ ExtOn α lam E₀ r x := by
  have key : ∀ y : ℝ, ExtOn α lam E₀ r y → ExtOn α lam E₀ r (α - y) := by
    rintro y ⟨f, han, hup, hdown, hpos⟩
    refine ⟨fun z => 1 / star (f (star z)), analyticOnNhd_inv_star_conj han hpos, ?_, ?_, ?_⟩
    · intro z hz hzim
      dsimp only
      have hz' : star z ∈ Metric.ball (E₀ : ℂ) r := star_mem_ball hz
      have hzim' : (star z).im < 0 := star_im_pos hzim
      rw [hdown (star z) hz' hzim']
      simp only [star_one_div, star_star]
      rw [one_div_one_div]
    · intro z hz hzim
      dsimp only
      have hz' : star z ∈ Metric.ball (E₀ : ℂ) r := star_mem_ball hz
      have hzim' : 0 < (star z).im := star_im_neg hzim
      rw [hup (star z) hz' hzim', show α - (α - y) = y by ring]
    · intro z hz
      dsimp only
      exact inv_star_im_pos (hpos (star z) (star_mem_ball hz))
  constructor
  · intro h
    have h' := key (α - x) h
    rwa [show α - (α - x) = x by ring] at h'
  · exact key x

/-- If `mfun α lam · x` continues to the ball `B(E₀,r)`, so does `mfun α lam · (x + α)`. -/
theorem extOn_add_alpha_forward (α lam : ℝ) {E₀ r x : ℝ} (h : ExtOn α lam E₀ r x) :
    ExtOn α lam E₀ r (x + α) := by
  obtain ⟨f, han, hup, hdown, hpos⟩ := h
  have hne : ∀ z ∈ Metric.ball (E₀ : ℂ) r, f z ≠ 0 := fun z hz =>
    ne_of_apply_ne Complex.im (ne_of_gt (hpos z hz))
  have hkey : AnalyticOnNhd ℂ (fun z : ℂ => z - ((pot lam x : ℝ) : ℂ) - 1 / f z)
      (Metric.ball (E₀ : ℂ) r) :=
    (analyticOnNhd_id.sub analyticOnNhd_const).sub
      (AnalyticOnNhd.div analyticOnNhd_const han hne)
  refine ⟨fun z => z - ((pot lam x : ℝ) : ℂ) - 1 / f z, hkey, ?_, ?_, ?_⟩
  · intro z hz hzim
    dsimp only
    rw [hup z hz hzim, mfun_cov α lam hzim x]
  · intro z hz hzim
    dsimp only
    have hE : 0 < (star z).im := star_im_neg hzim
    rw [hdown z hz hzim, show α - (x + α) = -x by ring, one_div_one_div]
    rw [one_div_star_mfun_eq α lam hE x, star_star]
  · intro z hz
    dsimp only
    rcases lt_trichotomy z.im 0 with hlt | heq | hgt
    · have hE : 0 < (star z).im := star_im_neg hlt
      have hz' : z - ((pot lam x : ℝ) : ℂ) - 1 / f z
          = 1 / star (mfun α lam (star z) (-x)) := by
        rw [hdown z hz hlt, one_div_one_div]
        have hE' := one_div_star_mfun_eq α lam hE x
        rw [star_star] at hE'
        rw [hE']
      rw [hz']
      exact inv_star_im_pos (mfun_im_pos' α lam hE (-x))
    · have hfim : 0 < (f z).im := hpos z hz
      have h1 : (z - ((pot lam x : ℝ) : ℂ) - 1 / f z).im = (-(1 / f z)).im := by
        simp only [Complex.sub_im, Complex.ofReal_im, heq, sub_zero, zero_sub, Complex.neg_im]
      rw [h1]
      exact im_neg_inv_pos hfim
    · have h2 := mfun_cov α lam hgt x
      rw [hup z hz hgt, ← h2]
      exact mfun_im_pos' α lam hgt (x + α)

/-- If `mfun α lam · (x + α)` continues to the ball `B(E₀,r)`, so does `mfun α lam · x`. -/
theorem extOn_add_alpha_backward (α lam : ℝ) {E₀ r x : ℝ} (h : ExtOn α lam E₀ r (x + α)) :
    ExtOn α lam E₀ r x := by
  obtain ⟨f, han, hup, hdown, hpos⟩ := h
  have hdown' : ∀ z ∈ Metric.ball (E₀ : ℂ) r, z.im < 0 →
      f z = 1 / star (mfun α lam (star z) (-x)) := by
    intro z hz hzim
    rw [hdown z hz hzim, show α - (x + α) = -x by ring]
  have hden : ∀ z ∈ Metric.ball (E₀ : ℂ) r, z - ((pot lam x : ℝ) : ℂ) - f z ≠ 0 := by
    intro z hz
    rcases lt_trichotomy z.im 0 with hlt | heq | hgt
    · have hE : 0 < (star z).im := star_im_neg hlt
      have hz' : z - ((pot lam x : ℝ) : ℂ) - f z = star (mfun α lam (star z) (α - x)) := by
        rw [hdown' z hz hlt]
        have hE' := one_div_star_mfun_eq α lam hE x
        rw [star_star] at hE'
        rw [hE']
        ring
      rw [hz']
      exact star_ne_zero.mpr (ne_of_apply_ne Complex.im
        (ne_of_gt (mfun_im_pos' α lam hE (α - x))))
    · have hfim : 0 < (f z).im := hpos z hz
      intro hc
      have h1 : (z - ((pot lam x : ℝ) : ℂ) - f z).im = -(f z).im := by
        simp only [Complex.sub_im, Complex.ofReal_im, heq, sub_zero, zero_sub, Complex.neg_im]
      rw [hc, Complex.zero_im] at h1
      linarith
    · have hz' : z - ((pot lam x : ℝ) : ℂ) - f z = 1 / mfun α lam z x := by
        rw [hup z hz hgt, mfun_cov α lam hgt x]
        ring
      rw [hz', one_div]
      exact inv_ne_zero (ne_of_apply_ne Complex.im (ne_of_gt (mfun_im_pos' α lam hgt x)))
  have hkey : AnalyticOnNhd ℂ (fun z : ℂ => 1 / (z - ((pot lam x : ℝ) : ℂ) - f z))
      (Metric.ball (E₀ : ℂ) r) :=
    AnalyticOnNhd.div analyticOnNhd_const
      ((analyticOnNhd_id.sub analyticOnNhd_const).sub han) hden
  refine ⟨fun z => 1 / (z - ((pot lam x : ℝ) : ℂ) - f z), hkey, ?_, ?_, ?_⟩
  · intro z hz hzim
    dsimp only
    have hz' : z - ((pot lam x : ℝ) : ℂ) - f z = 1 / mfun α lam z x := by
      rw [hup z hz hzim, mfun_cov α lam hzim x]
      ring
    rw [hz', one_div_one_div]
  · intro z hz hzim
    dsimp only
    have hE : 0 < (star z).im := star_im_neg hzim
    have hz' : z - ((pot lam x : ℝ) : ℂ) - f z = star (mfun α lam (star z) (α - x)) := by
      rw [hdown' z hz hzim]
      have hE' := one_div_star_mfun_eq α lam hE x
      rw [star_star] at hE'
      rw [hE']
      ring
    rw [hz']
  · intro z hz
    dsimp only
    rcases lt_trichotomy z.im 0 with hlt | heq | hgt
    · have hE : 0 < (star z).im := star_im_neg hlt
      have hz' : z - ((pot lam x : ℝ) : ℂ) - f z = star (mfun α lam (star z) (α - x)) := by
        rw [hdown' z hz hlt]
        have hE' := one_div_star_mfun_eq α lam hE x
        rw [star_star] at hE'
        rw [hE']
        ring
      rw [hz']
      exact inv_star_im_pos (mfun_im_pos' α lam hE (α - x))
    · have hfim : 0 < (f z).im := hpos z hz
      have hD : (z - ((pot lam x : ℝ) : ℂ) - f z).im = -(f z).im := by
        simp only [Complex.sub_im, Complex.ofReal_im, heq, sub_zero, zero_sub, Complex.neg_im]
      have hDne : z - ((pot lam x : ℝ) : ℂ) - f z ≠ 0 := by
        intro hc
        have h0 : (z - ((pot lam x : ℝ) : ℂ) - f z).im = 0 := by rw [hc, Complex.zero_im]
        rw [hD] at h0
        linarith
      have hneg : 0 < -(z - ((pot lam x : ℝ) : ℂ) - f z).im := by rw [hD]; linarith
      rw [show (1 : ℂ) / (z - ((pot lam x : ℝ) : ℂ) - f z)
          = (z - ((pot lam x : ℝ) : ℂ) - f z)⁻¹ by rw [one_div]]
      rw [Complex.inv_im]
      exact div_pos (by linarith) (Complex.normSq_pos.mpr hDne)
    · have hz' : z - ((pot lam x : ℝ) : ℂ) - f z = 1 / mfun α lam z x := by
        rw [hup z hz hgt, mfun_cov α lam hgt x]
        ring
      rw [hz', one_div_one_div]
      exact mfun_im_pos' α lam hgt x

/-- Invariance under `x ↦ x + α`. -/
theorem extOn_add_alpha (α lam : ℝ) {E₀ r x : ℝ} :
    ExtOn α lam E₀ r (x + α) ↔ ExtOn α lam E₀ r x :=
  ⟨fun h => extOn_add_alpha_backward α lam h, fun h => extOn_add_alpha_forward α lam h⟩

/-- Invariance under `x ↦ x + m * α`, `m : ℤ`. -/
theorem extOn_add_zsmul_alpha (α lam : ℝ) {E₀ r x : ℝ} (m : ℤ) :
    ExtOn α lam E₀ r (x + (m : ℝ) * α) ↔ ExtOn α lam E₀ r x := by
  induction m using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have h1 : x + (((k : ℤ) + 1 : ℤ) : ℝ) * α = (x + ((k : ℤ) : ℝ) * α) + α := by
      push_cast; ring
    rw [h1, extOn_add_alpha]
    exact ih
  | pred k ih =>
    have h1 : x + ((-(k : ℤ) - 1 : ℤ) : ℝ) * α = (x + ((-(k : ℤ) : ℤ) : ℝ) * α) - α := by
      push_cast; ring
    rw [h1]
    have h2 : ExtOn α lam E₀ r ((x + ((-(k : ℤ) : ℤ) : ℝ) * α) - α)
        ↔ ExtOn α lam E₀ r (x + ((-(k : ℤ) : ℤ) : ℝ) * α) := by
      have h3 := extOn_add_alpha (α := α) (lam := lam) (E₀ := E₀) (r := r)
        (x := (x + ((-(k : ℤ) : ℤ) : ℝ) * α) - α)
      simpa using h3.symm
    rw [h2]
    exact ih

/-- Invariance under the translation group `ℤ + αℤ`. -/
theorem extOn_add_int_add_zsmul (α lam : ℝ) {E₀ r x : ℝ} (n m : ℤ) :
    ExtOn α lam E₀ r (x + (n : ℝ) + (m : ℝ) * α) ↔ ExtOn α lam E₀ r x := by
  induction n using Int.induction_on with
  | zero => simpa using extOn_add_zsmul_alpha α lam (E₀ := E₀) (r := r) (x := x) m
  | succ k ih =>
    have h1 : x + (((k : ℤ) + 1 : ℤ) : ℝ) + (m : ℝ) * α
        = (x + ((k : ℤ) : ℝ) + (m : ℝ) * α) + 1 := by push_cast; ring
    rw [h1, extOn_add_one]
    exact ih
  | pred k ih =>
    have h1 : x + ((-(k : ℤ) - 1 : ℤ) : ℝ) + (m : ℝ) * α
        = (x + ((-(k : ℤ) : ℤ) : ℝ) + (m : ℝ) * α) - 1 := by push_cast; ring
    rw [h1]
    have h2 : ExtOn α lam E₀ r ((x + ((-(k : ℤ) : ℤ) : ℝ) + (m : ℝ) * α) - 1)
        ↔ ExtOn α lam E₀ r (x + ((-(k : ℤ) : ℤ) : ℝ) + (m : ℝ) * α) := by
      have h3 := extOn_add_one (α := α) (lam := lam) (E₀ := E₀) (r := r)
        (x := (x + ((-(k : ℤ) : ℤ) : ℝ) + (m : ℝ) * α) - 1)
      simpa using h3.symm
    rw [h2]
    exact ih

end Work.TMComp.Kotani
