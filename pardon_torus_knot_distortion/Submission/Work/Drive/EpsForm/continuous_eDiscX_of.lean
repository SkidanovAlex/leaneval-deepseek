import Mathlib
import Submission.Work.Drive.EpsForm.WaypointDesign2

namespace Work.Drive.EpsForm

noncomputable section

open Set
open LeanEval.KnotTheory.PardonDistortion

/-!
# Continuity of the corrected disc map

Auxiliary material for `continuous_eDiscX_of`.  The disc map `eDiscX` is the restriction to
the closed unit disc of the function `eDiscXFun z = eFunX (arg z) ‖z‖` on the whole plane.

The plane is covered by the two closed half planes `{0 ≤ im}` and `{im ≤ 0}`.  On the upper
half plane `arg z = arccos (re z / ‖z‖)`; on the lower half plane `arg z` is either
`- arccos (re z / ‖z‖)` (when `im z < 0`), or it can be replaced by that expression using
`eFunX (-π) = eFunX π` on the negative real axis.  Hence on each half plane `eDiscXFun`
agrees with a function that is locally a composition of continuous maps, and outside the
origin those compositions are genuinely continuous.  At the origin continuity follows from
the uniform smallness of `eFunX t s` as `s → 0`.
-/

/-- The corrected disc map `eDiscX`, read as a function on the whole plane. -/
def eDiscXFun (z : ℂ) : R3 := eFunX (Complex.arg z) ‖z‖

theorem eDiscXFun_apply (z : ℂ) : eDiscXFun z = eFunX (Complex.arg z) ‖z‖ := rfl

theorem eFunX2_mk (a b : ℝ) : eFunX2 (a, b) = eFunX a b := rfl

theorem eDiscXFun_zero : eDiscXFun 0 = 0 := by
  rw [eDiscXFun_apply, Complex.arg_zero, norm_zero, eFunX_zero]

/-- `eDiscX` is the restriction of `eDiscXFun` to the closed unit disc. -/
theorem eDiscX_eq_domRestrict :
    eDiscX = (Metric.closedBall (0 : ℂ) 1).domRestrict eDiscXFun := rfl

/-- On the closed upper half plane the argument is the companion pair of `arccos`. -/
def argPairUp (z : ℂ) : ℝ × ℝ := (Real.arccos (z.re / ‖z‖), ‖z‖)

/-- On the closed lower half plane the argument is the companion pair of `-arccos`. -/
def argPairDn (z : ℂ) : ℝ × ℝ := (-Real.arccos (z.re / ‖z‖), ‖z‖)

theorem argPairUp_apply (z : ℂ) : argPairUp z = (Real.arccos (z.re / ‖z‖), ‖z‖) := rfl

theorem argPairDn_apply (z : ℂ) : argPairDn z = (-Real.arccos (z.re / ‖z‖), ‖z‖) := rfl

/-- For a real `z`, the norm is the absolute value of the real part. -/
theorem norm_eq_abs_re_of_im_eq_zero {z : ℂ} (him : z.im = 0) : ‖z‖ = |z.re| := by
  simp only [Complex.norm_eq_sqrt_sq_add_sq, him, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    add_zero, Real.sqrt_sq_eq_abs]

theorem re_div_norm_eq_one {z : ℂ} (him : z.im = 0) (hre : 0 < z.re) : z.re / ‖z‖ = 1 := by
  rw [norm_eq_abs_re_of_im_eq_zero him, abs_of_pos hre, div_self hre.ne']

theorem re_div_norm_eq_neg_one {z : ℂ} (him : z.im = 0) (hre : z.re < 0) :
    z.re / ‖z‖ = -1 := by
  rw [norm_eq_abs_re_of_im_eq_zero him, abs_of_neg hre, div_neg, div_self hre.ne]

theorem eFunX2_argPairUp_zero :
    eFunX2 (Real.arccos ((0 : ℂ).re / ‖(0 : ℂ)‖), ‖(0 : ℂ)‖) = 0 := by
  rw [Complex.zero_re, norm_zero, zero_div, eFunX2_mk, eFunX_zero]

theorem eFunX2_argPairDn_zero :
    eFunX2 (-Real.arccos ((0 : ℂ).re / ‖(0 : ℂ)‖), ‖(0 : ℂ)‖) = 0 := by
  rw [Complex.zero_re, norm_zero, zero_div, eFunX2_mk, eFunX_zero]

/-- On the closed upper half plane `arg z = arccos (re z / ‖z‖)`. -/
theorem eDiscXFun_eq_upper {z : ℂ} (hz : z ≠ 0) (him : 0 ≤ z.im) :
    eDiscXFun z = eFunX2 (Real.arccos (z.re / ‖z‖), ‖z‖) := by
  rw [eDiscXFun_apply, Complex.arg_of_im_nonneg_of_ne_zero him hz, eFunX2_mk]

/-- On the closed lower half plane `arg z` can be replaced by `- arccos (re z / ‖z‖)`; the two
agree genuinely where `im z < 0`, and on the negative real axis the two ends `±π` are
identified by `eFunX (-π) = eFunX π`. -/
theorem eDiscXFun_eq_lower
    (hpi : ∀ s ∈ Set.Icc (0 : ℝ) 1, eFunX (-Real.pi) s = eFunX Real.pi s)
    {z : ℂ} (hz : z ≠ 0) (him : z.im ≤ 0) (hK : ‖z‖ ≤ 1) :
    eDiscXFun z = eFunX2 (-Real.arccos (z.re / ‖z‖), ‖z‖) := by
  rw [eDiscXFun_apply]
  rcases lt_or_eq_of_le him with him' | him'
  · rw [Complex.arg_of_im_neg him', eFunX2_mk]
  · have hre_ne : z.re ≠ 0 := by
      intro h
      exact hz (Complex.ext h (by simpa using him'))
    rcases lt_or_gt_of_ne hre_ne with hre | hre
    · rw [Complex.arg_eq_pi_iff.mpr ⟨hre, him'⟩]
      have hneg : -Real.arccos (z.re / ‖z‖) = -Real.pi := by
        rw [re_div_norm_eq_neg_one him' hre, Real.arccos_neg_one]
      rw [hneg, eFunX2_mk]
      exact (hpi ‖z‖ ⟨norm_nonneg z, hK⟩).symm
    · have harg0 : Complex.arg z = 0 := by
        rw [Complex.arg_of_re_nonneg hre.le, him', zero_div, Real.arcsin_zero]
      have hneg : -Real.arccos (z.re / ‖z‖) = 0 := by
        rw [re_div_norm_eq_one him' hre, Real.arccos_one, neg_zero]
      rw [harg0, hneg, eFunX2_mk]

/-- **Continuity of the corrected disc map from the two ingredients about `eFunX`.**
If `eFunX2` is continuous on `[-π,π] × [0,1]`, the profile leaves the axis uniformly in the
azimuth (the two lemmas `continuousOn_eFunX2` and `eFunX_tendsto_zero` above), and the two
ends `t = ±π` agree on `[0,1]` (`eFunX_neg_pi_eq` in the imported file), then the disc map
`eDiscX z = eFunX (arg z) ‖z‖` is continuous on the closed unit disc.

Route: at `z` in the slit plane (`0 < re z ∨ im z ≠ 0`) use `Complex.continuousAt_arg`
and `ContinuousWithinAt.comp` with the pair map `z ↦ (arg z, ‖z‖)`, which always lands in
`[-π,π] × [0,1]`.  On the negative real axis (`arg = π`) use the explicit formulas
`Complex.arg_of_re_neg_of_im_nonneg` and `Complex.arg_of_re_neg_of_im_neg` on the two
closed half-planes `{0 ≤ im}` and `{im ≤ 0}` and glue with
`ContinuousOn.union_of_isClosed`; the two halves give the same value because
`eFunX (-π) s = eFunX π s`.  At `z = 0` use the uniform statement (`eDiscX 0 = 0`,
i.e. `eFunX_zero`). -/
theorem continuous_eDiscX_of
    (hE : ContinuousOn eFunX2 (Set.Icc (-Real.pi) Real.pi ×ˢ Set.Icc (0 : ℝ) 1))
    (huni : ∀ ε > 0, ∃ δ > 0, ∀ t ∈ Set.Icc (-Real.pi) Real.pi, ∀ s ∈ Set.Icc (0 : ℝ) 1,
      s < δ → ‖eFunX t s‖ < ε)
    (hpi : ∀ s ∈ Set.Icc (0 : ℝ) 1, eFunX (-Real.pi) s = eFunX Real.pi s) :
    Continuous eDiscX := by
  have hUclosed : IsClosed {z : ℂ | 0 ≤ z.im} :=
    isClosed_le continuous_const Complex.continuous_im
  have hLclosed : IsClosed {z : ℂ | z.im ≤ 0} :=
    isClosed_le Complex.continuous_im continuous_const
  -- Continuity at the origin, from the uniform bound.
  have h0at : ContinuousAt eDiscXFun 0 := by
    rw [Metric.continuousAt_iff']
    intro ε hε
    obtain ⟨δ, hδpos, hδ⟩ := huni ε hε
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (lt_min hδpos one_pos)] with y hy
    have hyδ : ‖y‖ < δ :=
      lt_of_lt_of_le (by simpa [dist_zero_right] using hy) (min_le_left _ _)
    have hy1 : ‖y‖ ≤ 1 :=
      le_of_lt (lt_of_lt_of_le (by simpa [dist_zero_right] using hy) (min_le_right _ _))
    have harg : Complex.arg y ∈ Set.Icc (-Real.pi) Real.pi :=
      ⟨(Complex.neg_pi_lt_arg y).le, Complex.arg_le_pi y⟩
    have hs : ‖y‖ ∈ Set.Icc (0 : ℝ) 1 := ⟨norm_nonneg y, hy1⟩
    rw [eDiscXFun_zero, dist_zero_right, eDiscXFun_apply]
    exact hδ (Complex.arg y) harg ‖y‖ hs hyδ
  -- The upper half of the disc.
  have hKU : ContinuousOn eDiscXFun
      (Metric.closedBall (0 : ℂ) 1 ∩ {z : ℂ | 0 ≤ z.im}) := by
    intro x hx
    rcases eq_or_ne x 0 with rfl | hx0
    · exact h0at.continuousWithinAt.mono Set.inter_subset_left
    · have hxnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
      have hx1 : ‖x‖ ≤ 1 := by
        have h := hx.1
        rwa [Metric.mem_closedBall, dist_zero_right] at h
      have hpc : ContinuousAt argPairUp x := by
        change ContinuousAt (fun z : ℂ => (Real.arccos (z.re / ‖z‖), ‖z‖)) x
        exact (Real.continuous_arccos.continuousAt.comp
          (Complex.continuous_re.continuousAt.div₀ continuous_norm.continuousAt hxnorm)).prodMk
          continuous_norm.continuousAt
      have hpm : argPairUp x ∈ Set.Icc (-Real.pi) Real.pi ×ˢ Set.Icc (0 : ℝ) 1 := by
        change (Real.arccos (x.re / ‖x‖), ‖x‖) ∈
          Set.Icc (-Real.pi) Real.pi ×ˢ Set.Icc (0 : ℝ) 1
        exact ⟨⟨by linarith [Real.arccos_nonneg (x.re / ‖x‖), Real.pi_pos],
          Real.arccos_le_pi _⟩, norm_nonneg x, hx1⟩
      have hmap : MapsTo argPairUp
          (Metric.closedBall (0 : ℂ) 1 ∩ {z : ℂ | 0 ≤ z.im})
          (Set.Icc (-Real.pi) Real.pi ×ˢ Set.Icc (0 : ℝ) 1) := by
        intro z hz
        change (Real.arccos (z.re / ‖z‖), ‖z‖) ∈
          Set.Icc (-Real.pi) Real.pi ×ˢ Set.Icc (0 : ℝ) 1
        have hz1 : ‖z‖ ≤ 1 := by
          have h := hz.1
          rwa [Metric.mem_closedBall, dist_zero_right] at h
        exact ⟨⟨by linarith [Real.arccos_nonneg (z.re / ‖z‖), Real.pi_pos],
          Real.arccos_le_pi _⟩, norm_nonneg z, hz1⟩
      have hcomp : ContinuousWithinAt (eFunX2 ∘ argPairUp)
          (Metric.closedBall (0 : ℂ) 1 ∩ {z : ℂ | 0 ≤ z.im}) x :=
        ContinuousWithinAt.comp (hE.continuousWithinAt hpm) hpc.continuousWithinAt hmap
      refine hcomp.congr (fun y hy => ?_) ?_
      · rcases eq_or_ne y 0 with rfl | hy0
        · rw [Function.comp_apply, eDiscXFun_zero]
          show (0 : R3) = eFunX2 (Real.arccos ((0 : ℂ).re / ‖(0 : ℂ)‖), ‖(0 : ℂ)‖)
          exact eFunX2_argPairUp_zero.symm
        · simpa only [Function.comp_apply, argPairUp_apply] using
            eDiscXFun_eq_upper hy0 hy.2
      · simpa only [Function.comp_apply, argPairUp_apply] using
          eDiscXFun_eq_upper hx0 hx.2
  -- The lower half of the disc.
  have hKL : ContinuousOn eDiscXFun
      (Metric.closedBall (0 : ℂ) 1 ∩ {z : ℂ | z.im ≤ 0}) := by
    intro x hx
    rcases eq_or_ne x 0 with rfl | hx0
    · exact h0at.continuousWithinAt.mono Set.inter_subset_left
    · have hxnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
      have hx1 : ‖x‖ ≤ 1 := by
        have h := hx.1
        rwa [Metric.mem_closedBall, dist_zero_right] at h
      have hpc : ContinuousAt argPairDn x := by
        change ContinuousAt (fun z : ℂ => (-Real.arccos (z.re / ‖z‖), ‖z‖)) x
        exact ((Real.continuous_arccos.continuousAt.comp
          (Complex.continuous_re.continuousAt.div₀ continuous_norm.continuousAt hxnorm)).neg).prodMk
          continuous_norm.continuousAt
      have hpm : argPairDn x ∈ Set.Icc (-Real.pi) Real.pi ×ˢ Set.Icc (0 : ℝ) 1 := by
        change (-Real.arccos (x.re / ‖x‖), ‖x‖) ∈
          Set.Icc (-Real.pi) Real.pi ×ˢ Set.Icc (0 : ℝ) 1
        exact ⟨⟨by linarith [Real.arccos_le_pi (x.re / ‖x‖)],
          by linarith [Real.arccos_nonneg (x.re / ‖x‖), Real.pi_pos]⟩, norm_nonneg x, hx1⟩
      have hmap : MapsTo argPairDn
          (Metric.closedBall (0 : ℂ) 1 ∩ {z : ℂ | z.im ≤ 0})
          (Set.Icc (-Real.pi) Real.pi ×ˢ Set.Icc (0 : ℝ) 1) := by
        intro z hz
        change (-Real.arccos (z.re / ‖z‖), ‖z‖) ∈
          Set.Icc (-Real.pi) Real.pi ×ˢ Set.Icc (0 : ℝ) 1
        have hz1 : ‖z‖ ≤ 1 := by
          have h := hz.1
          rwa [Metric.mem_closedBall, dist_zero_right] at h
        exact ⟨⟨by linarith [Real.arccos_le_pi (z.re / ‖z‖)],
          by linarith [Real.arccos_nonneg (z.re / ‖z‖), Real.pi_pos]⟩, norm_nonneg z, hz1⟩
      have hcomp : ContinuousWithinAt (eFunX2 ∘ argPairDn)
          (Metric.closedBall (0 : ℂ) 1 ∩ {z : ℂ | z.im ≤ 0}) x :=
        ContinuousWithinAt.comp (hE.continuousWithinAt hpm) hpc.continuousWithinAt hmap
      refine hcomp.congr (fun y hy => ?_) ?_
      · rcases eq_or_ne y 0 with rfl | hy0
        · rw [Function.comp_apply, eDiscXFun_zero]
          show (0 : R3) = eFunX2 (-Real.arccos ((0 : ℂ).re / ‖(0 : ℂ)‖), ‖(0 : ℂ)‖)
          exact eFunX2_argPairDn_zero.symm
        · have hy1 : ‖y‖ ≤ 1 := by
            have h := hy.1
            rwa [Metric.mem_closedBall, dist_zero_right] at h
          simpa only [Function.comp_apply, argPairDn_apply] using
            eDiscXFun_eq_lower hpi hy0 hy.2 hy1
      · simpa only [Function.comp_apply, argPairDn_apply] using
          eDiscXFun_eq_lower hpi hx0 hx.2 hx1
  -- The two halves cover the disc.
  have hunion : (Metric.closedBall (0 : ℂ) 1 ∩ {z : ℂ | 0 ≤ z.im}) ∪
      (Metric.closedBall (0 : ℂ) 1 ∩ {z : ℂ | z.im ≤ 0}) = Metric.closedBall (0 : ℂ) 1 := by
    ext z
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h
      rcases le_or_gt 0 z.im with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr ⟨h, h'.le⟩
  have hK : ContinuousOn eDiscXFun (Metric.closedBall (0 : ℂ) 1) := by
    rw [← hunion]
    exact hKU.union_of_isClosed hKL (Metric.isClosed_closedBall.inter hUclosed)
      (Metric.isClosed_closedBall.inter hLclosed)
  rw [eDiscX_eq_domRestrict]
  exact continuousOn_iff_continuous_domRestrict.mp hK

end

end Work.Drive.EpsForm
