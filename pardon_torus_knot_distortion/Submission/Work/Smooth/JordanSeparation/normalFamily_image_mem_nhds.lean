import Mathlib
import Submission.Work.Smooth.JordanSeparation.Defs

/-!
# The image of a normal family contains a neighbourhood of a regular point

For a `C¹` curve `β : ℝ → ℂ` with `deriv β t₀ ≠ 0` and a continuous field `w : ℝ → ℂ` whose
offset map `(t,u) ↦ β t + u * w t` is injective in the `u`-variable on the strip `|u| < δ`,
the image of the strip is a neighbourhood of `β t₀`.

The proof reduces (by a translation and a non-zero complex scaling) to the normalised situation
`β t₀ = 0`, `0 < (deriv β t₀).re` and `(w t₀).re ≠ 0` (the latter because `u`-injectivity forces
`w t₀ ≠ 0`).  In these coordinates the target is sliced by its real part: for `x` near `0` and
`t` near `t₀` there is a unique `u` with `Re (β t + u * w t) = x`, namely
`u = (x - (β t).re) / (w t).re`; writing `K_x t = Im (β t + u * w t)`, the image contains every
point `x + (K_x t) * i`.  The `u`-injectivity forces `K_0` to take values of both signs on the
two sides of `t₀` (otherwise two points with the same image but distinct `u` would exist); this
survives for all `x` near `0` by continuity, and an intermediate-value argument yields the ball.
-/

open Set Metric Filter
open scoped Topology

set_option maxHeartbeats 4000000

namespace Work.Smooth.JordanSeparation

noncomputable section

/-- `HasDerivAt` for the real part of a `C¹` complex curve. -/
private lemma hasDerivAt_re_of_contDiff {β : ℝ → ℂ} (hβ : ContDiff ℝ 1 β) (t : ℝ) :
    HasDerivAt (fun s => (β s).re) ((deriv β t).re) t := by
  have hfd : HasFDerivAt β (fderiv ℝ β t) t :=
    (hβ.differentiable (by norm_num)).differentiableAt.hasFDerivAt
  have h2 : HasFDerivAt (fun s : ℝ => (β s).re)
      (Complex.reCLM.comp (fderiv ℝ β t)) t :=
    Complex.reCLM.hasFDerivAt.comp t hfd
  have h3 := h2.hasDerivAt
  rw [ContinuousLinearMap.comp_apply] at h3
  have h4 : (fderiv ℝ β t) (1 : ℝ) = deriv β t := hfd.hasDerivAt.deriv.symm
  rw [h4, Complex.reCLM_apply] at h3
  exact h3

/-- Real part of `(1 + i·s)·C`. -/
private lemma re_scale_I (s : ℝ) (C : ℂ) :
    ((1 + Complex.I * (s : ℂ)) * C).re = C.re - s * C.im := by
  rw [Complex.mul_re, Complex.add_re, Complex.one_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.add_im, Complex.one_im, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- There is a non-zero complex scaling making the real part of `p` positive while the real part
of `q` stays non-zero. -/
private lemma exists_scaling (p q : ℂ) (hp : p ≠ 0) (hq : q ≠ 0) :
    ∃ a : ℂ, a ≠ 0 ∧ 0 < (a * p).re ∧ (a * q).re ≠ 0 := by
  set C : ℂ := p⁻¹ * q with hCdef
  have hCne : C ≠ 0 := by rw [hCdef]; exact mul_ne_zero (inv_ne_zero hp) hq
  by_cases hci : C.im = 0
  · refine ⟨p⁻¹, inv_ne_zero hp, ?_, ?_⟩
    · rw [inv_mul_cancel₀ hp]; norm_num
    · have : C.re ≠ 0 := by
        intro h; exact hCne (Complex.ext (by simpa using h) (by simpa using hci))
      rw [show p⁻¹ * q = C from hCdef.symm]; exact this
  · refine ⟨(1 + Complex.I * (((C.re / C.im + 1 : ℝ)) : ℂ)) * p⁻¹, ?_, ?_, ?_⟩
    · apply mul_ne_zero _ (inv_ne_zero hp)
      intro h
      have := congrArg Complex.re h
      simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at this
      norm_num at this
    · have hcalc : (1 + Complex.I * (((C.re / C.im + 1 : ℝ)) : ℂ)) * p⁻¹ * p
          = 1 + Complex.I * (((C.re / C.im + 1 : ℝ)) : ℂ) := by
        rw [mul_assoc, inv_mul_cancel₀ hp, mul_one]
      rw [hcalc]
      have : (1 + Complex.I * ↑(C.re / C.im + 1)).re = 1 := by
        simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      rw [this]; norm_num
    · have hcalc : (1 + Complex.I * (((C.re / C.im + 1 : ℝ)) : ℂ)) * p⁻¹ * q
          = (1 + Complex.I * (((C.re / C.im + 1 : ℝ)) : ℂ)) * C := by
        rw [mul_assoc, show p⁻¹ * q = C from hCdef.symm]
      rw [hcalc, re_scale_I]
      have h2 : C.re - (C.re / C.im + 1) * C.im = -C.im := by
        rw [add_mul, one_mul, div_mul_cancel₀ _ hci]; ring
      rw [h2]
      exact neg_ne_zero.mpr hci

/-- Normalised core of the argument: `β t₀ = 0`, `0 < (deriv β t₀).re`, `(w t₀).re ≠ 0`. -/
private theorem core (β : ℝ → ℂ) (w : ℝ → ℂ) (δ t₀ : ℝ)
    (hβ : ContDiff ℝ 1 β) (hw : Continuous w) (hδ : 0 < δ)
    (ht0 : β t₀ = 0) (hder : 0 < (deriv β t₀).re) (hwr : (w t₀).re ≠ 0)
    (hinj : ∀ t t' u u' : ℝ, |u| < δ → |u'| < δ →
      β t + u * w t = β t' + u' * w t' → u = u') :
    ∃ ε : ℝ, 0 < ε ∧ Metric.ball (β t₀) ε ⊆
      (fun p : ℝ × ℝ => β p.1 + p.2 * w p.1) '' ((Set.univ : Set ℝ) ×ˢ Set.Ioo (-δ) δ) := by
  have hcb : Continuous β := hβ.continuous
  have hcdre : Continuous (fun t => (deriv β t).re) :=
    Complex.continuous_re.comp (hβ.continuous_deriv le_rfl)
  have hcwre : Continuous (fun t => (w t).re) := Complex.continuous_re.comp hw
  have hcwim : Continuous (fun t => (w t).im) := Complex.continuous_im.comp hw
  have hcbre : Continuous (fun t => (β t).re) := Complex.continuous_re.comp hcb
  have hcbim : Continuous (fun t => (β t).im) := Complex.continuous_im.comp hcb
  have hwrpos : 0 < |(w t₀).re| := abs_pos.mpr hwr
  have hphi0 : (β t₀).re = 0 := by rw [ht0]; rfl
  have hpsi0 : (β t₀).im = 0 := by rw [ht0]; rfl
  have hmem1 : {t : ℝ | 0 < (deriv β t).re} ∈ 𝓝 t₀ := by
    have h := hcdre.continuousAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds hder)
    simpa only [Set.preimage, Set.mem_setOf_eq, Set.mem_Ioi] using h
  have hmem2 : {t : ℝ | |(w t).re - (w t₀).re| < |(w t₀).re| / 2} ∈ 𝓝 t₀ := by
    have h := hcwre.continuousAt.preimage_mem_nhds
      (isOpen_Ioo.mem_nhds (show (w t₀).re ∈ Set.Ioo ((w t₀).re - |(w t₀).re| / 2)
          ((w t₀).re + |(w t₀).re| / 2) by constructor <;> linarith [hwrpos]))
    filter_upwards [h] with t ht
    simp only [Set.mem_preimage, Set.mem_Ioo] at ht
    rw [abs_lt]; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hmem3 : {t : ℝ | |(β t).re| < δ * |(w t₀).re| / 4} ∈ 𝓝 t₀ := by
    have hc : 0 < δ * |(w t₀).re| / 4 := by positivity
    have h := hcbre.continuousAt.preimage_mem_nhds
      (isOpen_Ioo.mem_nhds (show (β t₀).re ∈ Set.Ioo (-(δ * |(w t₀).re| / 4))
          (δ * |(w t₀).re| / 4) by rw [hphi0]; constructor <;> linarith))
    filter_upwards [h] with t ht
    simp only [Set.mem_preimage, Set.mem_Ioo] at ht
    rw [abs_lt]; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  obtain ⟨ε1, hε1pos, hε1⟩ := Metric.mem_nhds_iff.mp hmem1
  obtain ⟨ε2, hε2pos, hε2⟩ := Metric.mem_nhds_iff.mp hmem2
  obtain ⟨ε3, hε3pos, hε3⟩ := Metric.mem_nhds_iff.mp hmem3
  set η : ℝ := min (min ε1 ε2) ε3 / 2 with hηdef
  have hηpos : 0 < η := by
    rw [hηdef]; exact div_pos (lt_min (lt_min hε1pos hε2pos) hε3pos) two_pos
  have hη1 : η < ε1 := by
    rw [hηdef]
    have h := min_le_left (min ε1 ε2) ε3
    have h2 := min_le_left ε1 ε2
    linarith
  have hη2 : η < ε2 := by
    rw [hηdef]
    have h := min_le_left (min ε1 ε2) ε3
    have h2 := min_le_right ε1 ε2
    linarith
  have hη3 : η < ε3 := by
    rw [hηdef]
    have h := min_le_right (min ε1 ε2) ε3
    linarith
  have hcond1 : ∀ t, |t - t₀| ≤ η → 0 < (deriv β t).re := by
    intro t ht
    apply hε1; rw [Metric.mem_ball, Real.dist_eq]; exact lt_of_le_of_lt ht hη1
  have hcond2 : ∀ t, |t - t₀| ≤ η → |(w t).re - (w t₀).re| < |(w t₀).re| / 2 := by
    intro t ht
    apply hε2; rw [Metric.mem_ball, Real.dist_eq]; exact lt_of_le_of_lt ht hη2
  have hcond3 : ∀ t, |t - t₀| ≤ η → |(β t).re| < δ * |(w t₀).re| / 4 := by
    intro t ht
    apply hε3; rw [Metric.mem_ball, Real.dist_eq]; exact lt_of_le_of_lt ht hη3
  have hwre_lb : ∀ t, |t - t₀| ≤ η → |(w t₀).re| / 2 < |(w t).re| := by
    intro t ht
    have hab := abs_sub_abs_le_abs_sub (w t₀).re (w t).re
    rw [abs_sub_comm (w t₀).re (w t).re] at hab
    have h4 := hcond2 t ht
    linarith
  have hwre_ne : ∀ t, |t - t₀| ≤ η → (w t).re ≠ 0 := by
    intro t ht h0
    have h := hwre_lb t ht
    rw [h0, abs_zero] at h; linarith [hwrpos]
  have hmem_Icc : ∀ t, |t - t₀| ≤ η → t ∈ Set.Icc (t₀ - η) (t₀ + η) := by
    intro t ht; rw [Set.mem_Icc, abs_le] at *; constructor <;> linarith [ht.1, ht.2]
  have hmem_Icc0 : t₀ ∈ Set.Icc (t₀ - η) (t₀ + η) := by
    rw [Set.mem_Icc]; constructor <;> linarith [hηpos]
  have hmono : StrictMonoOn (fun t => (β t).re) (Set.Icc (t₀ - η) (t₀ + η)) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _) hcbre.continuousOn ?_
    intro x hx
    rw [interior_Icc] at hx
    have hx' : |x - t₀| ≤ η := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
    rw [(hasDerivAt_re_of_contDiff hβ x).deriv]
    exact hcond1 x hx'
  have hphi_lt : ∀ t, |t - t₀| ≤ η → t < t₀ → (β t).re < 0 := by
    intro t ht hlt
    have h := hmono (hmem_Icc t ht) hmem_Icc0 hlt
    simpa only [hphi0] using h
  have hphi_gt : ∀ t, |t - t₀| ≤ η → t₀ < t → 0 < (β t).re := by
    intro t ht hlt
    have h := hmono hmem_Icc0 (hmem_Icc t ht) hlt
    simpa only [hphi0] using h
  set R : ℝ → ℝ := fun t => (w t).im / (w t).re with hR
  set K0 : ℝ → ℝ := fun t => (β t).im - (β t).re * R t with hK0
  have hK0t₀ : K0 t₀ = 0 := by simp [hK0, hphi0, hpsi0]
  have hF_x : ∀ (x t : ℝ), (w t).re ≠ 0 →
      β t + ((((x - (β t).re) / (w t).re : ℝ)) : ℂ) * w t
        = (x : ℂ) + ((K0 t + x * R t : ℝ) : ℂ) * Complex.I := by
    intro x t hwt
    apply Complex.ext
    · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        sub_zero, Complex.I_re]
      field_simp
      ring
    · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        zero_add, Complex.I_im, Complex.I_re, hR, hK0]
      field_simp
      ring
  have hF_0 : ∀ t, (w t).re ≠ 0 →
      β t + ((((0 - (β t).re) / (w t).re : ℝ)) : ℂ) * w t = ((K0 t : ℝ) : ℂ) * Complex.I := by
    intro t hwt
    have h := hF_x 0 t hwt
    simpa using h
  have hu_bound : ∀ t x, |t - t₀| ≤ η → |x| < δ * |(w t₀).re| / 4 →
      |(x - (β t).re) / (w t).re| < δ := by
    intro t x ht hx
    have hwt := hwre_lb t ht
    have hwtpos : 0 < |(w t).re| := by linarith [hwrpos]
    have h3 := hcond3 t ht
    have h1 : |x - (β t).re| ≤ |x| + |(β t).re| := by
      rw [sub_eq_add_neg]
      exact (abs_add_le x (-(β t).re)).trans_eq (by rw [abs_neg])
    rw [abs_div, div_lt_iff₀ hwtpos]
    have hlt : |x - (β t).re| < δ * |(w t₀).re| / 2 := by linarith [h1, hx, h3]
    have hδ2 : δ * |(w t₀).re| / 2 < δ * |(w t).re| := by nlinarith [hwt, hwrpos, hδ]
    linarith
  have hden_pos : ∀ t₁ t₂, |t₁ - t₀| ≤ η → |t₂ - t₀| ≤ η → 0 < (w t₁).re * (w t₂).re := by
    intro t₁ t₂ ht1 ht2
    have hc2a := hcond2 t₁ ht1
    have hc2b := hcond2 t₂ ht2
    rcases lt_or_gt_of_ne hwr with hc | hc
    · rw [abs_of_neg hc] at hc2a hc2b
      have h1 : (w t₁).re < 0 := by rw [abs_lt] at hc2a; linarith [hc2a.2, hc]
      have h2 : (w t₂).re < 0 := by rw [abs_lt] at hc2b; linarith [hc2b.2, hc]
      exact mul_pos_of_neg_of_neg h1 h2
    · rw [abs_of_pos hc] at hc2a hc2b
      have h1 : 0 < (w t₁).re := by rw [abs_lt] at hc2a; linarith [hc2a.1, hc]
      have h2 : 0 < (w t₂).re := by rw [abs_lt] at hc2b; linarith [hc2b.1, hc]
      exact mul_pos h1 h2
  have hfold0 : ∀ t, |t - t₀| ≤ η → t ≠ t₀ → K0 t ≠ 0 := by
    intro t ht hne h0
    have hwt := hwre_ne t ht
    have hu : |(0 - (β t).re) / (w t).re| < δ := hu_bound t 0 ht (by rw [abs_zero]; positivity)
    have hzero : β t + ((((0 - (β t).re) / (w t).re : ℝ)) : ℂ) * w t
        = β t₀ + (0 : ℝ) * w t₀ := by
      rw [hF_0 t hwt, h0]; simp [ht0]
    have hres := hinj t t₀ ((0 - (β t).re) / (w t).re) 0 hu (by rw [abs_zero]; exact hδ) hzero
    have hphi_eq : (β t).re = 0 := by
      rw [zero_sub, neg_div, neg_eq_zero, div_eq_zero_iff] at hres
      rcases hres with h | h
      · exact h
      · exact absurd h hwt
    rcases lt_trichotomy t t₀ with hlt | heq | hgt
    · linarith [hphi_lt t ht hlt, hphi_eq]
    · exact hne heq
    · linarith [hphi_gt t ht hgt, hphi_eq]
  have hfold : ∀ t₁ t₂, |t₁ - t₀| ≤ η → t₁ < t₀ → t₀ < t₂ → |t₂ - t₀| ≤ η →
      K0 t₁ = K0 t₂ → False := by
    intro t₁ t₂ ht1 h1 h2 ht2 heq
    have hwt1 := hwre_ne t₁ ht1
    have hwt2 := hwre_ne t₂ ht2
    have hu1 : |(0 - (β t₁).re) / (w t₁).re| < δ := hu_bound t₁ 0 ht1 (by rw [abs_zero]; positivity)
    have hu2 : |(0 - (β t₂).re) / (w t₂).re| < δ := hu_bound t₂ 0 ht2 (by rw [abs_zero]; positivity)
    have heq' : β t₁ + ((((0 - (β t₁).re) / (w t₁).re : ℝ)) : ℂ) * w t₁
        = β t₂ + ((((0 - (β t₂).re) / (w t₂).re : ℝ)) : ℂ) * w t₂ := by
      rw [hF_0 t₁ hwt1, hF_0 t₂ hwt2, heq]
    have huu := hinj t₁ t₂ _ _ hu1 hu2 heq'
    have hprod : ((0 - (β t₁).re) / (w t₁).re) * ((0 - (β t₂).re) / (w t₂).re) < 0 := by
      have hnum : (β t₁).re * (β t₂).re < 0 :=
        mul_neg_of_neg_of_pos (hphi_lt t₁ ht1 h1) (hphi_gt t₂ ht2 h2)
      have hden := hden_pos t₁ t₂ ht1 ht2
      have he : ((0 - (β t₁).re) / (w t₁).re) * ((0 - (β t₂).re) / (w t₂).re)
          = ((β t₁).re * (β t₂).re) / ((w t₁).re * (w t₂).re) := by
        field_simp; ring
      rw [he]
      exact div_neg_of_neg_of_pos hnum hden
    rw [huu] at hprod
    nlinarith [sq_nonneg (((0 - (β t₁).re) / (w t₁).re))]
  have hcontRbig : ContinuousOn R (Set.Icc (t₀ - η) (t₀ + η)) := by
    refine ContinuousOn.div hcwim.continuousOn hcwre.continuousOn ?_
    intro t ht
    exact hwre_ne t (by rw [Set.mem_Icc] at ht; rw [abs_le]; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  have hcont_K0 : ContinuousOn K0 (Set.Icc (t₀ - η) (t₀ + η)) := by
    have h := ContinuousOn.sub hcbim.continuousOn (ContinuousOn.mul hcbre.continuousOn hcontRbig)
    rw [hK0]; exact h
  have hta : |(t₀ - η / 2) - t₀| ≤ η := by rw [abs_le]; constructor <;> linarith
  have htb : |(t₀ + η / 2) - t₀| ≤ η := by rw [abs_le]; constructor <;> linarith
  have hcross : K0 (t₀ - η / 2) * K0 (t₀ + η / 2) < 0 := by
    have hne_a : K0 (t₀ - η / 2) ≠ 0 := hfold0 _ hta (by linarith)
    have hne_b : K0 (t₀ + η / 2) ≠ 0 := hfold0 _ htb (by linarith)
    have hsubL : Set.Icc (t₀ - η / 2) t₀ ⊆ Set.Icc (t₀ - η) (t₀ + η) := by
      intro z hz; rw [Set.mem_Icc] at hz ⊢; constructor <;> linarith [hz.1, hz.2]
    have hsubR : Set.Icc t₀ (t₀ + η / 2) ⊆ Set.Icc (t₀ - η) (t₀ + η) := by
      intro z hz; rw [Set.mem_Icc] at hz ⊢; constructor <;> linarith [hz.1, hz.2]
    have hcontL : ∀ Y : ℝ, K0 (t₀ - η / 2) < Y → Y < 0 →
        ∃ s, t₀ - η < s ∧ s < t₀ ∧ K0 s = Y := by
      intro Y hY hYn
      have hm : Y ∈ Set.Icc (K0 (t₀ - η / 2)) (K0 t₀) := by
        rw [hK0t₀]; exact ⟨le_of_lt hY, le_of_lt hYn⟩
      have h3 : Y ∈ K0 '' Set.Icc (t₀ - η / 2) t₀ :=
        intermediate_value_Icc (by linarith) (hcont_K0.mono hsubL) hm
      rw [Set.mem_image] at h3
      obtain ⟨s, hs, hse⟩ := h3
      rw [Set.mem_Icc] at hs
      have hne' : s ≠ t₀ := fun h => by rw [h, hK0t₀] at hse; linarith [hse, hYn]
      exact ⟨s, by linarith [hs.1], lt_of_le_of_ne hs.2 hne', hse⟩
    have hcontLpos : ∀ Y : ℝ, 0 < Y → Y < K0 (t₀ - η / 2) →
        ∃ s, t₀ - η < s ∧ s < t₀ ∧ K0 s = Y := by
      intro Y hY hYn
      have hm : Y ∈ Set.Icc (K0 t₀) (K0 (t₀ - η / 2)) := by
        rw [hK0t₀]; exact ⟨le_of_lt hY, le_of_lt hYn⟩
      have h3 : Y ∈ K0 '' Set.Icc (t₀ - η / 2) t₀ :=
        intermediate_value_Icc' (by linarith) (hcont_K0.mono hsubL) hm
      rw [Set.mem_image] at h3
      obtain ⟨s, hs, hse⟩ := h3
      rw [Set.mem_Icc] at hs
      have hne' : s ≠ t₀ := fun h => by rw [h, hK0t₀] at hse; linarith [hse, hY]
      exact ⟨s, by linarith [hs.1], lt_of_le_of_ne hs.2 hne', hse⟩
    have hcontR : ∀ Y : ℝ, 0 < Y → Y < K0 (t₀ + η / 2) →
        ∃ s, t₀ < s ∧ s < t₀ + η ∧ K0 s = Y := by
      intro Y hY hYn
      have hm : Y ∈ Set.Icc (K0 t₀) (K0 (t₀ + η / 2)) := by
        rw [hK0t₀]; exact ⟨le_of_lt hY, le_of_lt hYn⟩
      have h3 : Y ∈ K0 '' Set.Icc t₀ (t₀ + η / 2) :=
        intermediate_value_Icc (by linarith) (hcont_K0.mono hsubR) hm
      rw [Set.mem_image] at h3
      obtain ⟨s, hs, hse⟩ := h3
      rw [Set.mem_Icc] at hs
      have hne' : t₀ ≠ s := fun h => by rw [← h, hK0t₀] at hse; linarith [hse, hY]
      exact ⟨s, lt_of_le_of_ne hs.1 hne', by linarith [hs.2], hse⟩
    have hcontRneg : ∀ Y : ℝ, K0 (t₀ + η / 2) < Y → Y < 0 →
        ∃ s, t₀ < s ∧ s < t₀ + η ∧ K0 s = Y := by
      intro Y hY hYn
      have hm : Y ∈ Set.Icc (K0 (t₀ + η / 2)) (K0 t₀) := by
        rw [hK0t₀]; exact ⟨le_of_lt hY, le_of_lt hYn⟩
      have h3 : Y ∈ K0 '' Set.Icc t₀ (t₀ + η / 2) :=
        intermediate_value_Icc' (by linarith) (hcont_K0.mono hsubR) hm
      rw [Set.mem_image] at h3
      obtain ⟨s, hs, hse⟩ := h3
      rw [Set.mem_Icc] at hs
      have hne' : t₀ ≠ s := fun h => by rw [← h, hK0t₀] at hse; linarith [hse, hYn]
      exact ⟨s, lt_of_le_of_ne hs.1 hne', by linarith [hs.2], hse⟩
    by_contra hcon
    rw [not_lt] at hcon
    rcases lt_or_gt_of_ne hne_a with ha | ha
    · rcases lt_or_gt_of_ne hne_b with hb | hb
      · obtain ⟨s, hs1, hs2, hse⟩ := hcontL (max (K0 (t₀ - η / 2)) (K0 (t₀ + η / 2)) / 2)
          (by have := le_max_left (K0 (t₀ - η / 2)) (K0 (t₀ + η / 2)); nlinarith)
          (by have := max_lt ha hb; linarith)
        obtain ⟨s', hs1', hs2', hse'⟩ := hcontRneg (max (K0 (t₀ - η / 2)) (K0 (t₀ + η / 2)) / 2)
          (by have := le_max_right (K0 (t₀ - η / 2)) (K0 (t₀ + η / 2)); nlinarith)
          (by have := max_lt ha hb; linarith)
        exact hfold s s' (by rw [abs_le]; constructor <;> linarith) hs2 (by linarith)
          (by rw [abs_le]; constructor <;> linarith) (by rw [hse, hse'])
      · nlinarith [ha, hb]
    · rcases lt_or_gt_of_ne hne_b with hb | hb
      · nlinarith [ha, hb]
      · obtain ⟨s, hs1, hs2, hse⟩ := hcontLpos (min (K0 (t₀ - η / 2)) (K0 (t₀ + η / 2)) / 2)
          (by have := lt_min ha hb; linarith)
          (by have := min_le_left (K0 (t₀ - η / 2)) (K0 (t₀ + η / 2)); nlinarith)
        obtain ⟨s', hs1', hs2', hse'⟩ := hcontR (min (K0 (t₀ - η / 2)) (K0 (t₀ + η / 2)) / 2)
          (by have := lt_min ha hb; linarith)
          (by have := min_le_right (K0 (t₀ - η / 2)) (K0 (t₀ + η / 2)); nlinarith)
        exact hfold s s' (by rw [abs_le]; constructor <;> linarith) hs2 (by linarith)
          (by rw [abs_le]; constructor <;> linarith) (by rw [hse, hse'])
  -- final neighbourhood
  have hK1ne : K0 (t₀ - η / 2) ≠ 0 := hfold0 _ hta (by linarith)
  have hK2ne : K0 (t₀ + η / 2) ≠ 0 := hfold0 _ htb (by linarith)
  set r : ℝ := min |K0 (t₀ - η / 2)| |K0 (t₀ + η / 2)| / 2 with hrdef
  have hrpos : 0 < r := by
    rw [hrdef]; exact div_pos (lt_min (abs_pos.mpr hK1ne) (abs_pos.mpr hK2ne)) two_pos
  have hK1lb : 2 * r ≤ |K0 (t₀ - η / 2)| := by
    rw [hrdef]; have := min_le_left |K0 (t₀ - η / 2)| |K0 (t₀ + η / 2)|; linarith
  have hK2lb : 2 * r ≤ |K0 (t₀ + η / 2)| := by
    rw [hrdef]; have := min_le_right |K0 (t₀ - η / 2)| |K0 (t₀ + η / 2)|; linarith
  set M : ℝ := max |R (t₀ - η / 2)| |R (t₀ + η / 2)| + 1 with hMdef
  have hMpos : 0 < M := by rw [hMdef]; positivity
  set Estrad : ℝ := r / M with hEdef
  have hEpos : 0 < Estrad := by rw [hEdef]; exact div_pos hrpos hMpos
  have hRa : |R (t₀ - η / 2)| < M := by
    rw [hMdef]; have := le_max_left |R (t₀ - η / 2)| |R (t₀ + η / 2)|; linarith
  have hRb : |R (t₀ + η / 2)| < M := by
    rw [hMdef]; have := le_max_right |R (t₀ - η / 2)| |R (t₀ + η / 2)|; linarith
  have hstrad : ∀ x : ℝ, |x| < Estrad →
      ((K0 (t₀ - η / 2) + x * R (t₀ - η / 2) ≤ -r ∧ r ≤ K0 (t₀ + η / 2) + x * R (t₀ + η / 2)) ∨
       (r ≤ K0 (t₀ - η / 2) + x * R (t₀ - η / 2) ∧ K0 (t₀ + η / 2) + x * R (t₀ + η / 2) ≤ -r)) := by
    intro x hx
    have hEM : Estrad * M = r := by rw [hEdef]; field_simp
    have hxa : |x * R (t₀ - η / 2)| < r := by
      rw [abs_mul]
      have h1 : |x| * |R (t₀ - η / 2)| < Estrad * M :=
        lt_of_le_of_lt (mul_le_mul_of_nonneg_left (le_of_lt hRa) (abs_nonneg x))
          (mul_lt_mul_of_pos_right hx hMpos)
      rwa [hEM] at h1
    have hxb : |x * R (t₀ + η / 2)| < r := by
      rw [abs_mul]
      have h1 : |x| * |R (t₀ + η / 2)| < Estrad * M :=
        lt_of_le_of_lt (mul_le_mul_of_nonneg_left (le_of_lt hRb) (abs_nonneg x))
          (mul_lt_mul_of_pos_right hx hMpos)
      rwa [hEM] at h1
    have ha' := abs_lt.mp hxa
    have hb' := abs_lt.mp hxb
    rcases lt_or_gt_of_ne hK1ne with h1 | h1
    · have h2 : 0 < K0 (t₀ + η / 2) := by
        by_contra h; push_neg at h; nlinarith [h1, h, hcross]
      left
      exact ⟨by rw [abs_of_neg h1] at hK1lb; linarith [hK1lb, ha'.2],
             by rw [abs_of_pos h2] at hK2lb; linarith [hK2lb, hb'.1]⟩
    · have h2 : K0 (t₀ + η / 2) < 0 := by
        by_contra h; push_neg at h; nlinarith [h1, h, hcross]
      right
      exact ⟨by rw [abs_of_pos h1] at hK1lb; linarith [hK1lb, ha'.1],
             by rw [abs_of_neg h2] at hK2lb; linarith [hK2lb, hb'.2]⟩
  set εx : ℝ := min Estrad (δ * |(w t₀).re| / 4) with hεxdef
  have hεxpos : 0 < εx := by
    rw [hεxdef]; exact lt_min hEpos (by positivity)
  refine ⟨min εx r, lt_min hεxpos hrpos, ?_⟩
  intro z hz
  rw [Metric.mem_ball] at hz
  have hzr : ‖z‖ < min εx r := by simpa [ht0, dist_eq_norm] using hz
  have hxlt : |z.re| < εx := lt_of_le_of_lt (Complex.abs_re_le_norm z) (lt_of_lt_of_le hzr (min_le_left _ _))
  have hyle : |z.im| ≤ r := le_of_lt (lt_of_le_of_lt (Complex.abs_im_le_norm z) (lt_of_lt_of_le hzr (min_le_right _ _)))
  have hge := abs_le.mp hyle
  have hsub : Set.Icc (t₀ - η / 2) (t₀ + η / 2) ⊆ Set.Icc (t₀ - η) (t₀ + η) := by
    intro s hs; rw [Set.mem_Icc] at hs ⊢; constructor <;> linarith [hs.1, hs.2]
  have hcontx : ContinuousOn (fun t => K0 t + z.re * R t) (Set.Icc (t₀ - η / 2) (t₀ + η / 2)) :=
    (hcont_K0.mono hsub).add (ContinuousOn.const_mul (hcontRbig.mono hsub) z.re)
  have hzltE : |z.re| < Estrad := lt_of_lt_of_le hxlt (min_le_left _ _)
  have hzltD : |z.re| < δ * |(w t₀).re| / 4 := lt_of_lt_of_le hxlt (min_le_right _ _)
  have key : ∃ t, t ∈ Set.Icc (t₀ - η / 2) (t₀ + η / 2) ∧ K0 t + z.re * R t = z.im := by
    rcases hstrad z.re hzltE with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hm : z.im ∈ Set.Icc (K0 (t₀ - η / 2) + z.re * R (t₀ - η / 2))
          (K0 (t₀ + η / 2) + z.re * R (t₀ + η / 2)) :=
        ⟨by linarith [h1, hge.1], by linarith [h2, hge.2]⟩
      obtain ⟨s, hs, hse⟩ := intermediate_value_Icc (by linarith) hcontx hm
      exact ⟨s, hs, hse⟩
    · have hm : z.im ∈ Set.Icc (K0 (t₀ + η / 2) + z.re * R (t₀ + η / 2))
          (K0 (t₀ - η / 2) + z.re * R (t₀ - η / 2)) :=
        ⟨by linarith [h2, hge.1], by linarith [h1, hge.2]⟩
      obtain ⟨s, hs, hse⟩ := intermediate_value_Icc' (by linarith) hcontx hm
      exact ⟨s, hs, hse⟩
  obtain ⟨t, ht, hte⟩ := key
  have htmem : |t - t₀| ≤ η := by rw [Set.mem_Icc] at ht; rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have hwt := hwre_ne t htmem
  have hux : |(z.re - (β t).re) / (w t).re| < δ := hu_bound t z.re htmem hzltD
  have huab := abs_lt.mp hux
  refine ⟨(t, (z.re - (β t).re) / (w t).re), ?_, ?_⟩
  · rw [Set.mem_prod, Set.mem_Ioo]
    exact ⟨Set.mem_univ _, ⟨huab.1, huab.2⟩⟩
  · change β t + ((((z.re - (β t).re) / (w t).re : ℝ)) : ℂ) * w t = z
    rw [hF_x z.re t hwt, hte]
    apply Complex.ext <;> simp

/-- **Core estimate.**  For a curve `β : ℝ → ℂ` and a continuous field `w` whose associated
family `(t,u) ↦ β t + u * w t` is injective in `u` on the strip `|u| < δ`, the image of the
strip is a neighbourhood of `β t₀` at any point `t₀` where `β` is regular. -/
theorem normalFamily_image_mem_nhds (β : ℝ → ℂ) (w : ℝ → ℂ) (δ : ℝ) (t₀ : ℝ)
    (hβ : ContDiff ℝ 1 β) (hw : Continuous w) (hδ : 0 < δ)
    (himm : deriv β t₀ ≠ 0)
    (hinj : ∀ t t' u u' : ℝ, |u| < δ → |u'| < δ →
      β t + u * w t = β t' + u' * w t' → u = u') :
    ∃ ε : ℝ, 0 < ε ∧ Metric.ball (β t₀) ε ⊆
      (fun p : ℝ × ℝ => β p.1 + p.2 * w p.1) '' ((Set.univ : Set ℝ) ×ˢ Set.Ioo (-δ) δ) := by
  -- the field does not vanish at the base parameter
  have hw0 : w t₀ ≠ 0 := by
    intro h
    have hlt : |δ / 2| < δ := by rw [abs_of_pos (by linarith)]; linarith
    have h0 : β t₀ + (0 : ℝ) * w t₀ = β t₀ + ((δ / 2 : ℝ) : ℂ) * w t₀ := by simp [h]
    have hcontra := hinj t₀ t₀ 0 (δ / 2) (by rw [abs_zero]; exact hδ) hlt h0
    linarith
  obtain ⟨a, hane, hap, haq⟩ := exists_scaling (deriv β t₀) (w t₀) himm hw0
  set β₁ : ℝ → ℂ := fun t => a * (β t - β t₀) with hβ₁
  set w₁ : ℝ → ℂ := fun t => a * w t with hw₁
  have hcan : 0 < ‖a‖ := norm_pos_iff.mpr hane
  have hβ₁cd : ContDiff ℝ 1 β₁ := by rw [hβ₁]; fun_prop
  have hw₁c : Continuous w₁ := by rw [hw₁]; fun_prop
  have hβ₁0 : β₁ t₀ = 0 := by simp only [hβ₁]; ring
  have hderiv1 : deriv β₁ t₀ = a * deriv β t₀ := by
    rw [hβ₁, deriv_const_mul_field]
    congr 1
    rw [deriv_sub_const]
  have hder1 : 0 < (deriv β₁ t₀).re := by rw [hderiv1]; exact hap
  have hwr1 : (w₁ t₀).re ≠ 0 := by rw [hw₁]; exact haq
  have hinj1 : ∀ t t' u u' : ℝ, |u| < δ → |u'| < δ →
      β₁ t + u * w₁ t = β₁ t' + u' * w₁ t' → u = u' := by
    intro t t' u u' hu hu' h
    apply hinj t t' u u' hu hu'
    have e1 : β₁ t + u * w₁ t = a * (β t + u * w t - β t₀) := by simp only [hβ₁, hw₁]; ring
    have e2 : β₁ t' + u' * w₁ t' = a * (β t' + u' * w t' - β t₀) := by simp only [hβ₁, hw₁]; ring
    have h' : a * (β t + u * w t - β t₀) = a * (β t' + u' * w t' - β t₀) := by
      rw [← e1, ← e2]; exact h
    have hsub := mul_left_cancel₀ hane h'
    rw [sub_eq_add_neg, sub_eq_add_neg] at hsub
    exact add_right_cancel hsub
  obtain ⟨εc, hεc, hball⟩ := core β₁ w₁ δ t₀ hβ₁cd hw₁c hδ hβ₁0 hder1 hwr1 hinj1
  refine ⟨εc / ‖a‖, div_pos hεc hcan, ?_⟩
  intro z hz
  rw [Metric.mem_ball, dist_eq_norm] at hz
  have hmem : a * (z - β t₀) ∈ Metric.ball (β₁ t₀) εc := by
    rw [hβ₁0, Metric.mem_ball, dist_zero_right, norm_mul]
    calc ‖a‖ * ‖z - β t₀‖ < ‖a‖ * (εc / ‖a‖) := mul_lt_mul_of_pos_left hz hcan
      _ = εc := by field_simp
  obtain ⟨p, hp, hpe⟩ := hball hmem
  refine ⟨p, hp, ?_⟩
  have hF1 : β₁ p.1 + p.2 * w₁ p.1 = a * (β p.1 + p.2 * w p.1 - β t₀) := by
    simp only [hβ₁, hw₁]; ring
  change β₁ p.1 + p.2 * w₁ p.1 = a * (z - β t₀) at hpe
  rw [hF1] at hpe
  have hsub := mul_left_cancel₀ hane hpe
  rw [sub_eq_add_neg, sub_eq_add_neg] at hsub
  exact add_right_cancel hsub

end

end Work.Smooth.JordanSeparation
