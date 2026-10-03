import Submission.Lib.Unif2.Commons.Topology.Crossing.crossing_lemma_square

namespace Commons.Topology.Jordan

open Set Complex

/-! ## Affine rescaling of the rectangle onto the unit square

`crossingRectScale a b c d` rescales the `re`- and `im`-coordinates separately to send the
rectangle `{z : ℂ | a ≤ z.re ≤ b ∧ c ≤ z.im ≤ d}` to the unit square `[0,1]²`
(assumed non-degenerate, i.e. `a < b` and `c < d`). -/

/-- Affine rescaling identifying the rectangle `[a,b] × [c,d]` with the unit square `[0,1]²`. -/
noncomputable def crossingRectScale (a b c d : ℝ) (z : ℂ) : ℂ :=
  (((z.re - a) / (b - a) : ℝ) : ℂ) + (((z.im - c) / (d - c) : ℝ) : ℂ) * Complex.I

lemma crossingRectScale_re (a b c d : ℝ) (z : ℂ) :
    (crossingRectScale a b c d z).re = (z.re - a) / (b - a) := by
  show ((((z.re - a) / (b - a) : ℝ) : ℂ)
      + (((z.im - c) / (d - c) : ℝ) : ℂ) * Complex.I).re = (z.re - a) / (b - a)
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]

lemma crossingRectScale_im (a b c d : ℝ) (z : ℂ) :
    (crossingRectScale a b c d z).im = (z.im - c) / (d - c) := by
  show ((((z.re - a) / (b - a) : ℝ) : ℂ)
      + (((z.im - c) / (d - c) : ℝ) : ℂ) * Complex.I).im = (z.im - c) / (d - c)
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add]
  ring

lemma continuous_crossingRectScale (a b c d : ℝ) :
    Continuous (crossingRectScale a b c d) := by
  have h1 : Continuous fun z : ℂ => ((z.re - a) / (b - a) : ℝ) :=
    (Complex.continuous_re.sub continuous_const).div_const _
  have h2 : Continuous fun z : ℂ => ((z.im - c) / (d - c) : ℝ) :=
    (Complex.continuous_im.sub continuous_const).div_const _
  exact (Complex.continuous_ofReal.comp h1).add
    ((Complex.continuous_ofReal.comp h2).mul continuous_const)

lemma crossingRectScale_injective {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    Function.Injective (crossingRectScale a b c d) := by
  intro z w hzw
  have hba : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  have hdc : d - c ≠ 0 := ne_of_gt (sub_pos.mpr hcd)
  have hre : z.re = w.re := by
    have h := congrArg Complex.re hzw
    rw [crossingRectScale_re, crossingRectScale_re] at h
    have h2 := congrArg (fun x : ℝ => x * (b - a)) h
    rw [div_mul_cancel₀ (z.re - a) hba, div_mul_cancel₀ (w.re - a) hba] at h2
    linarith
  have him : z.im = w.im := by
    have h := congrArg Complex.im hzw
    rw [crossingRectScale_im, crossingRectScale_im] at h
    have h2 := congrArg (fun x : ℝ => x * (d - c)) h
    rw [div_mul_cancel₀ (z.im - c) hdc, div_mul_cancel₀ (w.im - c) hdc] at h2
    linarith
  exact Complex.ext hre him

lemma crossingRectScale_mem {a b c d : ℝ} (hab : a < b) (hcd : c < d) {z : ℂ}
    (hr : z.re ∈ Set.Icc a b) (hi : z.im ∈ Set.Icc c d) :
    (crossingRectScale a b c d z).re ∈ Set.Icc (0:ℝ) 1 ∧
      (crossingRectScale a b c d z).im ∈ Set.Icc (0:ℝ) 1 := by
  have hb : 0 < b - a := sub_pos.mpr hab
  have hd : 0 < d - c := sub_pos.mpr hcd
  rw [crossingRectScale_re, crossingRectScale_im]
  refine ⟨⟨div_nonneg (by linarith [hr.1]) hb.le, ?_⟩,
          ⟨div_nonneg (by linarith [hi.1]) hd.le, ?_⟩⟩
  · rw [div_le_one hb]; linarith [hr.2]
  · rw [div_le_one hd]; linarith [hi.2]

lemma crossingRectScale_re_eq_zero {a b c d : ℝ} {z : ℂ} (hz : z.re = a) :
    (crossingRectScale a b c d z).re = 0 := by
  rw [crossingRectScale_re, hz, sub_self, zero_div]

lemma crossingRectScale_re_eq_one {a b c d : ℝ} (hab : a < b) {z : ℂ} (hz : z.re = b) :
    (crossingRectScale a b c d z).re = 1 := by
  rw [crossingRectScale_re, hz, div_self (ne_of_gt (sub_pos.mpr hab))]

lemma crossingRectScale_im_eq_zero {a b c d : ℝ} {z : ℂ} (hz : z.im = c) :
    (crossingRectScale a b c d z).im = 0 := by
  rw [crossingRectScale_im, hz, sub_self, zero_div]

lemma crossingRectScale_im_eq_one {a b c d : ℝ} (hcd : c < d) {z : ℂ} (hz : z.im = d) :
    (crossingRectScale a b c d z).im = 1 := by
  rw [crossingRectScale_im, hz, div_self (ne_of_gt (sub_pos.mpr hcd))]

/-- **Crossing lemma** (Maehara's Lemma 2, the plane form of the two-dimensional Brouwer
fixed point theorem).  Two paths in the rectangle `E(a,b;c,d) = {z : ℂ | a ≤ z.re ≤ b ∧
c ≤ z.im ≤ d}` — one joining the left side to the right side, the other the bottom side to the
top side — must meet.  Only the values of the paths on `[-1,1]` are constrained. -/
theorem crossing_lemma_rect {a b c d : ℝ} (h v : C(ℝ, ℂ))
    (hh : ∀ t : ℝ, t ∈ Set.Icc (-1:ℝ) 1 → (h t).re ∈ Set.Icc a b ∧ (h t).im ∈ Set.Icc c d)
    (hv : ∀ t : ℝ, t ∈ Set.Icc (-1:ℝ) 1 → (v t).re ∈ Set.Icc a b ∧ (v t).im ∈ Set.Icc c d)
    (h1 : (h (-1)).re = a) (h2 : (h 1).re = b)
    (v1 : (v (-1)).im = c) (v2 : (v 1).im = d) :
    ∃ s ∈ Set.Icc (-1:ℝ) 1, ∃ t ∈ Set.Icc (-1:ℝ) 1, h s = v t := by
  have hab : a ≤ b := by
    have := (hh (-1) (by norm_num)).1.2
    rwa [h1] at this
  have hcd : c ≤ d := by
    have := (hv (-1) (by norm_num)).2.2
    rwa [v1] at this
  rcases eq_or_lt_of_le hab with hab' | hab'
  · -- degenerate case `a = b`: the `re`-coordinate is pinned, so the intermediate value
    -- theorem for the `im`-coordinate of `v` produces the intersection.
    have hcontV : ContinuousOn (fun t : ℝ => (v t).im) (Set.Icc (-1:ℝ) 1) :=
      (Complex.continuous_im.comp v.continuous).continuousOn
    have hsubV := isPreconnected_Icc.intermediate_value
      (show (-1:ℝ) ∈ Set.Icc (-1:ℝ) 1 by norm_num)
      (show (1:ℝ) ∈ Set.Icc (-1:ℝ) 1 by norm_num) hcontV
    have hymem : (h (-1)).im ∈ Set.Icc ((v (-1)).im) ((v 1)).im := by
      rw [v1, v2]; exact (hh (-1) (by norm_num)).2
    obtain ⟨t, ht, htval⟩ := hsubV hymem
    refine ⟨-1, by norm_num, t, ht, ?_⟩
    apply Complex.ext
    · have hmem : (v t).re ∈ Set.Icc a b := (hv t ht).1
      rw [hab'] at hmem
      rw [h1, hab']
      exact (le_antisymm hmem.2 hmem.1).symm
    · exact htval.symm
  rcases eq_or_lt_of_le hcd with hcd' | hcd'
  · -- degenerate case `c = d`, symmetric to the previous one.
    have hcontH : ContinuousOn (fun t : ℝ => (h t).re) (Set.Icc (-1:ℝ) 1) :=
      (Complex.continuous_re.comp h.continuous).continuousOn
    have hsubH := isPreconnected_Icc.intermediate_value
      (show (-1:ℝ) ∈ Set.Icc (-1:ℝ) 1 by norm_num)
      (show (1:ℝ) ∈ Set.Icc (-1:ℝ) 1 by norm_num) hcontH
    have hymem : (v (-1)).re ∈ Set.Icc ((h (-1)).re) ((h 1)).re := by
      rw [h1, h2]; exact (hv (-1) (by norm_num)).1
    obtain ⟨s, hs, hsval⟩ := hsubH hymem
    refine ⟨s, hs, -1, by norm_num, ?_⟩
    apply Complex.ext
    · exact hsval
    · have hmem : (h s).im ∈ Set.Icc c d := (hh s hs).2
      rw [← hcd'] at hmem
      rw [v1]
      exact le_antisymm hmem.2 hmem.1
  · -- non-degenerate case: reparametrise `[-1,1]` by `unitInterval`, rescale the rectangle
    -- to the unit square and apply `crossing_lemma_square`.
    let H : C(unitInterval, ℂ) :=
      ⟨fun s => crossingRectScale a b c d (h (2 * (s:ℝ) - 1)), by
        refine (continuous_crossingRectScale a b c d).comp ?_
        exact h.continuous.comp
          ((continuous_const.mul continuous_subtype_val).sub continuous_const)⟩
    let V : C(unitInterval, ℂ) :=
      ⟨fun t => crossingRectScale a b c d (v (2 * (t:ℝ) - 1)), by
        refine (continuous_crossingRectScale a b c d).comp ?_
        exact v.continuous.comp
          ((continuous_const.mul continuous_subtype_val).sub continuous_const)⟩
    have hmem_unit : ∀ s : unitInterval, (2 * (s:ℝ) - 1) ∈ Set.Icc (-1:ℝ) 1 := by
      intro s
      have hs : (s:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨s.2.1, s.2.2⟩
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hH : ∀ s : unitInterval,
        (H s).re ∈ Set.Icc (0:ℝ) 1 ∧ (H s).im ∈ Set.Icc (0:ℝ) 1 := by
      intro s
      have hs := hmem_unit s
      exact crossingRectScale_mem hab' hcd' (hh _ hs).1 (hh _ hs).2
    have hV : ∀ t : unitInterval,
        (V t).re ∈ Set.Icc (0:ℝ) 1 ∧ (V t).im ∈ Set.Icc (0:ℝ) 1 := by
      intro t
      have ht := hmem_unit t
      exact crossingRectScale_mem hab' hcd' (hv _ ht).1 (hv _ ht).2
    have H0 : (H 0).re = 0 := by
      change (crossingRectScale a b c d (h (2 * ((0:unitInterval):ℝ) - 1))).re = 0
      rw [show 2 * ((0:unitInterval):ℝ) - 1 = -1 by norm_num,
        crossingRectScale_re_eq_zero h1]
    have H1 : (H 1).re = 1 := by
      change (crossingRectScale a b c d (h (2 * ((1:unitInterval):ℝ) - 1))).re = 1
      rw [show 2 * ((1:unitInterval):ℝ) - 1 = 1 by norm_num,
        crossingRectScale_re_eq_one hab' h2]
    have V0 : (V 0).im = 0 := by
      change (crossingRectScale a b c d (v (2 * ((0:unitInterval):ℝ) - 1))).im = 0
      rw [show 2 * ((0:unitInterval):ℝ) - 1 = -1 by norm_num,
        crossingRectScale_im_eq_zero v1]
    have V1 : (V 1).im = 1 := by
      change (crossingRectScale a b c d (v (2 * ((1:unitInterval):ℝ) - 1))).im = 1
      rw [show 2 * ((1:unitInterval):ℝ) - 1 = 1 by norm_num,
        crossingRectScale_im_eq_one hcd' v2]
    obtain ⟨s, t, hst⟩ :=
      Commons.Topology.Crossing.crossing_lemma_square H V hH hV H0 H1 V0 V1
    exact ⟨2 * (s:ℝ) - 1, hmem_unit s, 2 * (t:ℝ) - 1, hmem_unit t,
      crossingRectScale_injective hab' hcd' hst⟩

end Commons.Topology.Jordan
