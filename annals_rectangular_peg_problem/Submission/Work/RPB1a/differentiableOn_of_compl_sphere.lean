import Mathlib

namespace Work.RPB1a

open Complex Set Metric intervalIntegral
open scoped ContDiff Real Topology Interval

/-! ### Painlevé removability of the real axis (Morera)

These are the private helpers implementing the "straight-line case" needed below: a function
continuous on an open set `Ω ⊆ ℂ` and complex-differentiable off the real axis is
complex-differentiable on `Ω`.  The proof is Morera's theorem
(`Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn`): each rectangle is split
along the axis into two rectangles each having an edge *on* the axis, and Cauchy–Goursat
(`Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn`) applies to each
half because the *open* interior of a rectangle with an edge on the axis avoids the axis. -/

/-- The boundary integral of `f` along the rectangle with opposite corners `z` and `w`. -/
private noncomputable def rectBoundary (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  ((∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
      I • (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) -
      I • (∫ y : ℝ in z.im..w.im, f (z.re + y * I)))

private lemma rectBoundary_add_eq (f : ℂ → ℂ) (z w : ℂ) :
    z.wedgeIntegral w f + w.wedgeIntegral z f = rectBoundary f z w :=
  Complex.wedgeIntegral_add_wedgeIntegral_eq z w f

/-- A rectangle whose open interior avoids the real axis has vanishing boundary integral for a
function continuous on a domain `Ω` containing the closed rectangle and holomorphic off the
axis. -/
private lemma rectBoundary_zero_of_off_axis {Ω : Set ℂ} {f : ℂ → ℂ}
    (hcont : ContinuousOn f Ω) (hdiff : DifferentiableOn ℂ f (Ω ∩ {z : ℂ | z.im ≠ 0}))
    {z w : ℂ} (hsub : Rectangle z w ⊆ Ω)
    (haxis : (0 : ℝ) ∉ Set.Ioo (min z.im w.im) (max z.im w.im)) :
    rectBoundary f z w = 0 := by
  rw [rectBoundary]
  refine Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn f z w
    (hcont.mono hsub) (hdiff.mono fun p hp => ?_)
  rw [Complex.mem_reProdIm] at hp
  refine ⟨hsub ?_, ?_⟩
  · rw [Complex.Rectangle, Complex.mem_reProdIm]
    refine ⟨?_, ?_⟩
    · rw [Ioo_min_max] at hp
      exact uIoo_subset_uIcc_self hp.1
    · rw [Ioo_min_max] at hp
      exact uIoo_subset_uIcc_self hp.2
  · intro h0
    exact haxis (by simpa only [Ioo_min_max] using h0 ▸ hp.2)

/-- A rectangle with a horizontal edge on the real axis has vanishing boundary integral. -/
private lemma rectBoundary_zero_of_edge_on_axis {Ω : Set ℂ} {f : ℂ → ℂ}
    (hcont : ContinuousOn f Ω) (hdiff : DifferentiableOn ℂ f (Ω ∩ {z : ℂ | z.im ≠ 0}))
    {z w : ℂ} (hsub : Rectangle z w ⊆ Ω) (haxis : z.im = 0 ∨ w.im = 0) :
    rectBoundary f z w = 0 := by
  refine rectBoundary_zero_of_off_axis hcont hdiff hsub fun hm => ?_
  rcases haxis with h | h <;> rw [h] at hm
  · rcases le_total (0 : ℝ) w.im with hw | hw
    · rw [min_eq_left hw] at hm
      exact lt_irrefl (0 : ℝ) hm.1
    · rw [max_eq_left hw] at hm
      exact lt_irrefl (0 : ℝ) hm.2
  · rcases le_total z.im 0 with hz | hz
    · rw [max_eq_right hz] at hm
      exact lt_irrefl (0 : ℝ) hm.2
    · rw [min_eq_right hz] at hm
      exact lt_irrefl (0 : ℝ) hm.1

/-- The integral of `f` along the vertical edge of the rectangle at real part `a` splits at the
real axis, whenever the axis meets the edge. -/
private lemma vertical_edge_split {Ω : Set ℂ} {f : ℂ → ℂ} (hcont : ContinuousOn f Ω)
    {z w : ℂ} (hsub : Rectangle z w ⊆ Ω) (h0mem : (0 : ℝ) ∈ [[z.im, w.im]]) {a : ℝ}
    (ha : a ∈ [[z.re, w.re]]) :
    (∫ y : ℝ in z.im..w.im, f (a + y * I)) =
      (∫ y : ℝ in z.im..(0 : ℝ), f (a + y * I)) +
        ∫ y : ℝ in (0 : ℝ)..w.im, f (a + y * I) := by
  have contV : ContinuousOn (fun t : ℝ => f (a + t * I)) [[z.im, w.im]] :=
    hcont.comp (by fun_prop) fun t ht => hsub (by
      rw [Complex.Rectangle, Complex.mem_reProdIm]
      exact ⟨by simpa using ha, by simpa using ht⟩)
  refine (integral_add_adjacent_intervals ?_ ?_).symm
  · exact (contV.mono (uIcc_subset_uIcc left_mem_uIcc h0mem)).intervalIntegrable
  · exact (contV.mono (uIcc_subset_uIcc h0mem right_mem_uIcc)).intervalIntegrable

/-- A rectangle straddling the real axis has vanishing boundary integral: split it at the axis
into the two half-rectangles, each handled by `rectBoundary_zero_of_edge_on_axis`, and recombine,
the shared axis edge cancelling. -/
private lemma rectBoundary_zero_of_straddling {Ω : Set ℂ} {f : ℂ → ℂ}
    (hcont : ContinuousOn f Ω) (hdiff : DifferentiableOn ℂ f (Ω ∩ {z : ℂ | z.im ≠ 0}))
    {z w : ℂ} (hsub : Rectangle z w ⊆ Ω)
    (hstr : (0 : ℝ) ∈ Set.Ioo (min z.im w.im) (max z.im w.im)) :
    rectBoundary f z w = 0 := by
  have h0mem : (0 : ℝ) ∈ [[z.im, w.im]] := by
    rw [← Icc_min_max]
    exact Ioo_subset_Icc_self hstr
  have splitVw := vertical_edge_split hcont hsub h0mem right_mem_uIcc
  have splitVz := vertical_edge_split hcont hsub h0mem left_mem_uIcc
  have hsubR1 : Rectangle z (↑w.re : ℂ) ⊆ Ω := by
    refine fun p hp => hsub ?_
    rw [Complex.Rectangle, Complex.mem_reProdIm] at hp ⊢
    simp only [Complex.ofReal_re, Complex.ofReal_im] at hp
    exact ⟨hp.1, uIcc_subset_uIcc left_mem_uIcc h0mem hp.2⟩
  have hsubR2 : Rectangle (↑z.re : ℂ) w ⊆ Ω := by
    refine fun p hp => hsub ?_
    rw [Complex.Rectangle, Complex.mem_reProdIm] at hp ⊢
    simp only [Complex.ofReal_re, Complex.ofReal_im] at hp
    exact ⟨hp.1, uIcc_subset_uIcc h0mem right_mem_uIcc hp.2⟩
  have R1 := rectBoundary_zero_of_edge_on_axis hcont hdiff hsubR1
    (Or.inr (Complex.ofReal_im w.re))
  have R2 := rectBoundary_zero_of_edge_on_axis hcont hdiff hsubR2
    (Or.inl (Complex.ofReal_im z.re))
  rw [rectBoundary] at R1 R2
  simp only [Complex.ofReal_re, Complex.ofReal_im] at R1 R2
  rw [rectBoundary, splitVw, splitVz, smul_add, smul_add]
  simp only [smul_eq_mul] at R1 R2 ⊢
  linear_combination R1 + R2

/-- **Painlevé removability of the real axis.** -/
private lemma differentiableOn_of_continuousOn_of_differentiableOn_im_ne_zero {Ω : Set ℂ}
    {f : ℂ → ℂ} (hΩ : IsOpen Ω) (hc : ContinuousOn f Ω)
    (hd : DifferentiableOn ℂ f (Ω ∩ {z : ℂ | z.im ≠ 0})) :
    DifferentiableOn ℂ f Ω := by
  refine (Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn hΩ).mp ⟨?_, hc⟩
  intro z w hsub
  rw [← add_eq_zero_iff_eq_neg, rectBoundary_add_eq]
  by_cases hstr : (0 : ℝ) ∈ Set.Ioo (min z.im w.im) (max z.im w.im)
  · exact rectBoundary_zero_of_straddling hc hd hsub hstr
  · exact rectBoundary_zero_of_off_axis hc hd hsub hstr

/-! ### Painlevé removability of a circle

A fractional-linear chart `w ↦ c + a (w - I)/(w + I)` carries the real axis onto the circle
`sphere c ‖a‖` and omits the single point `c + a`; applying the straight-line case to `F` composed
with this chart (and transporting back along its inverse) removes the circle off the omitted
point.  Two charts, with `a = ±r`, cover the circle, and the prescribed value at the two omitted
points is recovered from the other chart. -/

/-- The fractional-linear chart carrying the real axis onto `sphere c ‖a‖`, omitting `c + a`. -/
private noncomputable def circleMap (c a w : ℂ) : ℂ := c + a * ((w - I) / (w + I))

/-- Its inverse, away from the omitted point `c + a`. -/
private noncomputable def circleMapInv (c a z : ℂ) : ℂ := I * ((a + (z - c)) / (a - (z - c)))

private lemma differentiableOn_circleMap (c a : ℂ) :
    DifferentiableOn ℂ (circleMap c a) ({-I}ᶜ : Set ℂ) := by
  intro w hw
  have hw' : w + I ≠ 0 := by
    intro h
    refine hw ?_
    rw [Set.mem_singleton_iff]
    linear_combination h
  exact (show DifferentiableAt ℂ (fun u : ℂ => c + a * ((u - I) / (u + I))) w by
    fun_prop).differentiableWithinAt

private lemma differentiableOn_circleMapInv (c a : ℂ) :
    DifferentiableOn ℂ (circleMapInv c a) ({c + a}ᶜ : Set ℂ) := by
  intro z hz
  have hz' : a - (z - c) ≠ 0 := by
    intro h
    refine hz ?_
    rw [Set.mem_singleton_iff]
    linear_combination -h
  exact (show DifferentiableAt ℂ (fun u : ℂ => I * ((a + (u - c)) / (a - (u - c)))) z by
    fun_prop).differentiableWithinAt

private lemma circleMap_circleMapInv {c a z : ℂ} (ha : a ≠ 0) (hz : z ≠ c + a) :
    circleMap c a (circleMapInv c a z) = z := by
  have hden : a - (z - c) ≠ 0 := by
    intro h
    exact hz (by linear_combination -h)
  simp only [circleMap, circleMapInv]
  field_simp [ha, hden]
  ring

private lemma circleMapInv_ne_neg_I {c a z : ℂ} (ha : a ≠ 0) (hz : z ≠ c + a) :
    circleMapInv c a z ≠ -I := by
  have hden : a - (z - c) ≠ 0 := by
    intro h
    exact hz (by linear_combination -h)
  intro h
  simp only [circleMapInv] at h
  have h4 : (a + (z - c)) / (a - (z - c)) = -1 := by
    apply mul_left_cancel₀ I_ne_zero
    rw [h, mul_neg, mul_one]
  rw [div_eq_iff hden] at h4
  have haz : a = 0 := by linear_combination h4 / 2
  exact ha haz

private lemma circleMap_mem_sphere_iff {c a w : ℂ} (ha : a ≠ 0) (hw : w ≠ -I) :
    circleMap c a w ∈ sphere c ‖a‖ ↔ w.im = 0 := by
  rw [mem_sphere, circleMap, dist_eq, add_sub_cancel_left, norm_mul, norm_div]
  have hden : ‖w + I‖ ≠ 0 := norm_ne_zero_iff.mpr (by
    intro h
    exact hw (by linear_combination h))
  have ha0 : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  have hnorm : ‖w - I‖ = ‖w + I‖ ↔ w.im = 0 := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← Complex.normSq_eq_norm_sq,
      ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, sub_re, I_re, sub_zero, sub_im, I_im, add_re, add_zero,
      add_im]
    constructor
    · intro h
      nlinarith
    · intro h
      rw [h]
      ring
  constructor
  · intro h
    have hquot : ‖w - I‖ / ‖w + I‖ = 1 := mul_left_cancel₀ ha0 (by simpa using h)
    exact hnorm.mp (div_eq_one_iff_eq hden |>.mp hquot)
  · intro h
    have hquot : ‖w - I‖ / ‖w + I‖ = 1 := div_eq_one_iff_eq hden |>.mpr (hnorm.mpr h)
    rw [hquot, mul_one]

/-- Removability across a circle off one point: the chart omits `c + a`. -/
private theorem differentiableOn_of_diff_sphere_omit {Ω : Set ℂ} {F : ℂ → ℂ} {c a : ℂ}
    (ha : a ≠ 0) (hΩ : IsOpen Ω) (hcont : ContinuousOn F Ω)
    (hdiff : DifferentiableOn ℂ F (Ω \ sphere c ‖a‖)) :
    DifferentiableOn ℂ F (Ω \ {c + a}) := by
  have hφU : DifferentiableOn ℂ (circleMap c a) ({-I}ᶜ ∩ circleMap c a ⁻¹' Ω : Set ℂ) :=
    (differentiableOn_circleMap c a).mono inter_subset_left
  have hUopen : IsOpen ({-I}ᶜ ∩ circleMap c a ⁻¹' Ω : Set ℂ) :=
    (differentiableOn_circleMap c a).continuousOn.isOpen_inter_preimage
      isClosed_singleton.isOpen_compl hΩ
  have hGdiff : DifferentiableOn ℂ (F ∘ circleMap c a)
      (({-I}ᶜ ∩ circleMap c a ⁻¹' Ω : Set ℂ) ∩ {z : ℂ | z.im ≠ 0}) := by
    refine hdiff.comp (hφU.mono inter_subset_left) fun w hw => ⟨hw.1.2, ?_⟩
    have hwI : w ≠ -I := by
      intro h
      exact hw.1.1 (by simpa using h)
    rw [circleMap_mem_sphere_iff ha hwI]
    exact hw.2
  have hG : DifferentiableOn ℂ (F ∘ circleMap c a) ({-I}ᶜ ∩ circleMap c a ⁻¹' Ω : Set ℂ) :=
    differentiableOn_of_continuousOn_of_differentiableOn_im_ne_zero hUopen
      (hcont.comp hφU.continuousOn fun w hw => hw.2) hGdiff
  have hψ : DifferentiableOn ℂ (circleMapInv c a) (Ω \ {c + a}) :=
    (differentiableOn_circleMapInv c a).mono fun z hz => hz.2
  refine (hG.comp hψ ?_).congr fun z hz => ?_
  · rintro z hz
    refine ⟨?_, ?_⟩
    · exact circleMapInv_ne_neg_I ha (by simpa using hz.2)
    · change circleMap c a (circleMapInv c a z) ∈ Ω
      rw [circleMap_circleMapInv ha (by simpa using hz.2)]
      exact hz.1
  · change F z = F (circleMap c a (circleMapInv c a z))
    rw [circleMap_circleMapInv ha (by simpa using hz.2)]

/-- **Painlevé removability across a circle.** A function continuous on an open set `Ω ⊆ ℂ` and
holomorphic off a positive-radius circle is holomorphic throughout `Ω`. -/
private theorem differentiableOn_of_continuousOn_of_differentiableOn_diff_sphere {Ω : Set ℂ}
    {F : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r) (hΩ : IsOpen Ω) (hcont : ContinuousOn F Ω)
    (hdiff : DifferentiableOn ℂ F (Ω \ sphere c r)) :
    DifferentiableOn ℂ F Ω := by
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  have hnorm : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have hnorm' : ‖(-(r : ℂ))‖ = r := by rw [norm_neg, hnorm]
  have hpos := differentiableOn_of_diff_sphere_omit (c := c) (a := (r : ℂ)) hr0 hΩ hcont
    (by rw [hnorm]; exact hdiff)
  have hneg := differentiableOn_of_diff_sphere_omit (c := c) (a := -(r : ℂ)) (neg_ne_zero.mpr hr0)
    hΩ hcont (by rw [hnorm']; exact hdiff)
  have hopenPos : IsOpen (Ω \ {c + (r : ℂ)}) := hΩ.sdiff isClosed_singleton
  have hopenNeg : IsOpen (Ω \ {c + -(r : ℂ)}) := hΩ.sdiff isClosed_singleton
  intro z hz
  by_cases hzr : z = c + (r : ℂ)
  · have hzneg : z ∈ Ω \ {c + -(r : ℂ)} := by
      refine ⟨hz, ?_⟩
      intro h
      simp only [Set.mem_singleton_iff] at h
      rw [hzr] at h
      apply hr0
      have hzero : (2 : ℂ) * (r : ℂ) = 0 := by linear_combination h
      exact (mul_eq_zero.mp hzero).resolve_left (by norm_num)
    exact (hneg z hzneg).differentiableAt (hopenNeg.mem_nhds hzneg) |>.differentiableWithinAt
  · have hzpos : z ∈ Ω \ {c + (r : ℂ)} := ⟨hz, by simpa using hzr⟩
    exact (hpos z hzpos).differentiableAt (hopenPos.mem_nhds hzpos) |>.differentiableWithinAt

/-- **Removable singularity across the unit circle.** If `f` is continuous on an open set `Ω ⊆ ℂ`
and complex-differentiable on `Ω` minus the unit circle, then `f` is complex-differentiable on `Ω`.

Suggested route: reduce to the straight-line case (a continuous function on an open set that is
differentiable off a straight line is differentiable everywhere — this auxiliary fact can be proved
inline in this file by Morera plus the splitting of a rectangle along the line; a sibling in the
project may also supply it as `Submission.Work.RPB1a.differentiableOn_of_compl_line`, import it if
it exists).

For `z₀ ∈ sphere 0 1` use the chart `φ u = z₀ * Complex.exp u`, which is entire with
`deriv φ u = z₀ * Complex.exp u ≠ 0`, satisfies `φ 0 = z₀` and `‖φ u‖ = Real.exp u.re`, so
`φ u ∈ sphere 0 1 ↔ u.re = 0`.  Let `Ω' := φ ⁻¹' Ω`, an open neighbourhood of `0`; then
`g := f ∘ φ` is continuous on `Ω'` and differentiable on `Ω' \ {u | u.re = 0}` (because `φ` maps
that set into `Ω \ sphere 0 1`).  Apply the line case to get `DifferentiableOn ℂ (f ∘ φ) Ω'`, hence
`DifferentiableAt ℂ (f ∘ φ) 0`.  Finally use the local inverse of `φ` at `0`
(`AnalyticAt.hasStrictDerivAt` + `HasStrictFDerivAt.localInverse`, which gives
`HasStrictDerivAt r _ z₀` and `∀ᶠ x in 𝓝 z₀, φ (r x) = x`) to write `f =ᶠ[𝓝 z₀] (f ∘ φ) ∘ r` and
conclude `DifferentiableAt ℂ f z₀`. -/
theorem differentiableOn_of_compl_sphere {Ω : Set ℂ} (hΩ : IsOpen Ω) {f : ℂ → ℂ}
    (hc : ContinuousOn f Ω) (hd : DifferentiableOn ℂ f (Ω \ sphere 0 1)) :
    DifferentiableOn ℂ f Ω :=
  differentiableOn_of_continuousOn_of_differentiableOn_diff_sphere one_pos hΩ hc hd

end Work.RPB1a
