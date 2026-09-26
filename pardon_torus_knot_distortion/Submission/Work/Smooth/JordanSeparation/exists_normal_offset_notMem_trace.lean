import Mathlib
import Submission.Work.Smooth.JordanSeparation.Defs

/-!
# The normal offsets of a simple immersed curve miss the curve

The **offset** of an immersed closed plane curve `c` in the direction of its unit normal field
`normalField c t = I·γ'(t)/‖γ'(t)‖` is, for small `s ≠ 0`, disjoint from the curve itself: this
file proves that for a *simple* immersed `C¹` curve there is `δ > 0` such that for every
`0 < s < δ` the two points `γ(0) ± s·normalField c 0` both lie off the trace of `c`
(`exists_normal_offset_notMem_trace`).  The two points are the first `t = 0` normal offsets of
the tubular-neighbourhood construction of `Submission/Work/Smooth/JordanSeparation/Defs`, and
they are the two points at which the winding number of `c` is compared in
`wind_normal_offset_sub`.

The mathematical content is the classical statement that an immersed curve crosses a *short*
segment of its normal direction transversally at a regular point.  Two separate facts are used:

* **locally**, the function `t ↦ detV (γ t - γ 0) (normalField c 0)` is `C¹` with
  `f'(0) = detV (γ'(0)) (normalField c 0) = ‖γ'(0)‖ > 0` (`detV_deriv_normalField`), hence it is
  strictly monotone near `0` and vanishes there only at `t = 0`; the determinant vanishes
  whenever `γ t - γ 0` is a multiple of `normalField c 0`, so `γ t` can only be a normal offset
  of `γ 0` for `t ∈ Ioo 0 ε ∪ Ioo (-ε) 0` when `t = 0`;
* **globally**, simplicity makes `γ` injective on `[0, 2π)`, so on the compact complement
  `[ε, 2π - ε]` of the local neighbourhood of `0` the continuous function `‖γ t - γ 0‖` has a
  positive minimum `m`; the offsets of length `< m` therefore cannot touch the trace there.

## Main results

* `hasDerivAt_detV_sub` — the derivative of `t ↦ detV (γ t - γ 0) v`;
* `continuous_detV_deriv` — continuity of `t ↦ detV (γ' t) v`;
* `exists_detV_normalField_ne_zero_near` — the local fact;
* `exists_normal_offset_notMem_trace` — the lemma requested by the Jordan separation chapter.
-/

open Work.Smooth.Jordan

namespace Work.Smooth.JordanSeparation

noncomputable section

/-- The derivative of `t ↦ detV (γ t - γ 0) v` along a `C¹` curve `γ` is
`t ↦ detV (γ' t) v`.  The chain rule is applied in `ℂ` (conjugation and multiplication by the
constant `v`) and the imaginary part is taken at the end. -/
lemma hasDerivAt_detV_sub (c : Work.Smooth.Jordan.SmoothPlaneCurve) (v : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => detV (c.γ s - c.γ 0) v) (detV (deriv c.γ t) v) t := by
  have hd : HasDerivAt c.γ (deriv c.γ t) t := (c.differentiable t).hasDerivAt
  have hsub : HasDerivAt (fun s : ℝ => c.γ s - c.γ 0) (deriv c.γ t) t := hd.sub_const _
  have hconj : HasDerivAt (fun s : ℝ => starRingEnd ℂ (c.γ s - c.γ 0))
      (starRingEnd ℂ (deriv c.γ t)) t :=
    ((Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt t hsub)
  have hmul : HasDerivAt (fun s : ℝ => starRingEnd ℂ (c.γ s - c.γ 0) * v)
      (starRingEnd ℂ (deriv c.γ t) * v) t := hconj.mul_const v
  exact (Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hmul)

/-- The function `t ↦ detV (γ' t) v` is continuous, because `γ'` is. -/
lemma continuous_detV_deriv (c : Work.Smooth.Jordan.SmoothPlaneCurve) (v : ℂ) :
    Continuous fun t : ℝ => detV (deriv c.γ t) v := by
  have h1 : Continuous fun t : ℝ => starRingEnd ℂ (deriv c.γ t) * v :=
    (((Complex.conjCLE : ℂ →L[ℝ] ℂ).continuous.comp c.continuous_deriv)).mul continuous_const
  have h2 : Continuous fun t : ℝ => (starRingEnd ℂ (deriv c.γ t) * v).im :=
    Complex.continuous_im.comp h1
  simpa only [detV_def] using h2

/-- **The local transversality fact.**  For an immersed `C¹` closed curve `c` there is `ε > 0`
such that the determinant of `γ t - γ 0` against the normal direction `normalField c 0` does not
vanish for `0 < |t| ≤ ε`.  Equivalently: near the parameter `0` the curve meets the normal line
at `γ 0` only at `γ 0` itself. -/
lemma exists_detV_normalField_ne_zero_near (c : Work.Smooth.Jordan.SmoothPlaneCurve)
    (h : Work.Smooth.Jordan.SmoothPlaneCurve.IsImmersion c) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| ≤ ε → t ≠ 0 →
      detV (c.γ t - c.γ 0) (normalField c 0) ≠ 0 := by
  -- `t ↦ detV (γ' t) (normalField c 0)` is continuous and positive at `0`
  obtain ⟨ε₁, hε₁, hpos⟩ : ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ t : ℝ, |t| < ε₁ →
      0 < detV (deriv c.γ t) (normalField c 0) := by
    have hg0 : 0 < detV (deriv c.γ 0) (normalField c 0) := by
      rw [detV_deriv_normalField c h 0]
      exact norm_pos_iff.mpr (h 0)
    have hcont := continuous_detV_deriv c (normalField c 0)
    have hopen : IsOpen {t : ℝ | 0 < detV (deriv c.γ t) (normalField c 0)} :=
      isOpen_lt continuous_const hcont
    obtain ⟨e, he, hball⟩ := Metric.isOpen_iff.mp hopen 0 hg0
    exact ⟨e, he, fun t ht => hball (by rwa [Metric.mem_ball, Real.dist_eq, sub_zero])⟩
  refine ⟨min (ε₁/2) 1, lt_min (by linarith) one_pos, ?_⟩
  have hε_le : min (ε₁/2) 1 ≤ ε₁ := by
    calc min (ε₁/2) 1 ≤ ε₁/2 := min_le_left _ _
      _ ≤ ε₁ := by linarith
  have hcont : Continuous (fun s : ℝ => detV (c.γ s - c.γ 0) (normalField c 0)) :=
    continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_detV_sub c _ t).continuousAt)
  -- the function is strictly monotone on a neighbourhood of `0`, where its derivative is positive
  have hmono : StrictMonoOn (fun s : ℝ => detV (c.γ s - c.γ 0) (normalField c 0))
      (Set.Icc (-(min (ε₁/2) 1)) (min (ε₁/2) 1)) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _) hcont.continuousOn (fun x hx => ?_)
    rw [interior_Icc, Set.mem_Ioo] at hx
    rw [(hasDerivAt_detV_sub c (normalField c 0) x).deriv]
    exact hpos x (abs_lt.mpr ⟨by linarith [hε_le, hx.1], by linarith [hε_le, hx.2]⟩)
  intro t ht htne
  have htmem : t ∈ Set.Icc (-(min (ε₁/2) 1)) (min (ε₁/2) 1) := by
    rw [Set.mem_Icc]
    exact abs_le.mp ht
  have h0mem : (0 : ℝ) ∈ Set.Icc (-(min (ε₁/2) 1)) (min (ε₁/2) 1) := by
    rw [Set.mem_Icc]
    exact ⟨by linarith [lt_min (by linarith : (0:ℝ) < ε₁/2) one_pos],
           le_of_lt (lt_min (by linarith : (0:ℝ) < ε₁/2) one_pos)⟩
  have hf0 : detV (c.γ 0 - c.γ 0) (normalField c 0) = 0 := by simp
  rcases lt_or_gt_of_ne htne with hlt | hgt
  · have h' := hmono htmem h0mem hlt
    simp only [hf0] at h'
    exact ne_of_lt h'
  · have h' := hmono h0mem htmem hgt
    simp only [hf0] at h'
    exact ne_of_gt h'

/-- **The normal offsets of `γ 0` miss the curve.**  For a simple immersed `C¹` closed plane
curve there is `δ > 0` such that both points `γ 0 + s·normalField c 0` and
`γ 0 - s·normalField c 0` lie off the trace of `c` for every `0 < s < δ`. -/
theorem exists_normal_offset_notMem_trace (c : Work.Smooth.Jordan.SmoothPlaneCurve)
    (h : Work.Smooth.Jordan.SmoothPlaneCurve.IsImmersion c) (hsimple : c.toPlaneCurve.IsSimple) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < s → s < δ →
      c.γ 0 + s * Work.Smooth.JordanSeparation.normalField c 0 ∉ c.trace ∧
      c.γ 0 - s * Work.Smooth.JordanSeparation.normalField c 0 ∉ c.trace := by
  set v : ℂ := normalField c 0 with hv
  have hvnorm : ‖v‖ = 1 := norm_normalField c h 0
  have hvne : v ≠ 0 := by
    intro h0
    rw [h0] at hvnorm
    simp at hvnorm
  -- the local radius, cut down so that it is also `< π`
  obtain ⟨ε₁, hε₁pos, hloc₁⟩ := exists_detV_normalField_ne_zero_near c h
  set ε : ℝ := min ε₁ 1 with hεdef
  have hεpos : 0 < ε := lt_min hε₁pos one_pos
  have hεle₁ : ε ≤ ε₁ := min_le_left _ _
  have hεle1 : ε ≤ 1 := min_le_right _ _
  have hεpi : ε < Real.pi := by linarith [hεle1, Real.pi_gt_three]
  have hloc : ∀ t : ℝ, |t| ≤ ε → t ≠ 0 → detV (c.γ t - c.γ 0) v ≠ 0 := by
    intro t ht htne
    exact hloc₁ t (le_trans ht hεle₁) htne
  -- the global radius: the distance from `γ 0` to the curve away from the local neighbourhood
  have hεlt : ε < 2 * Real.pi - ε := by linarith [hεpi, Real.pi_pos]
  obtain ⟨x, hxK, hxmin⟩ := isCompact_Icc.exists_isMinOn
      (s := Set.Icc ε (2 * Real.pi - ε)) (f := fun t => ‖c.γ t - c.γ 0‖)
      ⟨ε, le_rfl, hεlt.le⟩ ((continuous_norm.comp (c.cont.sub continuous_const)).continuousOn)
  set m : ℝ := ‖c.γ x - c.γ 0‖ with hmdef
  have hmpos : 0 < m := by
    have hne : c.γ x - c.γ 0 ≠ 0 := by
      refine sub_ne_zero.mpr (fun hγ => ?_)
      have hxIco : x ∈ Set.Ico (0 : ℝ) (2 * Real.pi) :=
        ⟨le_of_lt (lt_of_lt_of_le hεpos hxK.1), by linarith [hxK.2, hεpos]⟩
      have h0Ico : (0 : ℝ) ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := ⟨le_rfl, by positivity⟩
      have hx0 : x = 0 := hsimple hxIco h0Ico hγ
      linarith [hεpos, hxK.1, hx0]
    simpa [hmdef] using norm_pos_iff.mpr hne
  -- a point of the trace at distance `s < δ` from `γ 0` would have to be one of the two offsets
  have key : ∀ (r s : ℝ), 0 < s → s < ε → s < m → (r = s ∨ r = -s) →
      c.γ 0 + r * v ∉ c.trace := by
    intro r s hs hsε hsm hr hmem
    rw [PlaneCurve.trace_eq_image_Ico] at hmem
    obtain ⟨t, ht, htγ⟩ := hmem
    have hrabs : |r| = s := by
      rcases hr with h' | h' <;> rw [h'] <;> simp [abs_of_pos hs]
    have hsub : c.γ 0 + r * v - c.γ 0 = (r : ℂ) * v := by ring
    rcases lt_or_ge t ε with htlt | htge
    · -- `t ∈ [0, ε)`: the local transversality fact applies
      have htabs : |t| ≤ ε := by
        rw [abs_le]
        exact ⟨by linarith [ht.1, hεpos], htlt.le⟩
      rcases eq_or_ne t 0 with ht0 | htne
      · -- `t = 0`: then `r·v = 0`, impossible
        subst ht0
        have h1 : r * v = 0 := add_left_cancel (by rw [add_zero]; exact htγ.symm)
        rcases mul_eq_zero.mp h1 with h2 | h2
        · have : r = 0 := Complex.ofReal_eq_zero.mp h2
          rw [this] at hrabs
          simp at hrabs
          linarith [hs, hrabs]
        · exact hvne h2
      · have hdet := hloc t htabs htne
        apply hdet
        rw [show c.γ t - c.γ 0 = c.γ 0 + r * v - c.γ 0 from by rw [htγ], hsub, detV_smul_left,
          detV_self, mul_zero]
    · rcases le_or_gt t (2 * Real.pi - ε) with htle | htgt
      · -- `t ∈ [ε, 2π - ε]`: the distance from `γ 0` is at least `m > s`
        have hmin : ‖c.γ x - c.γ 0‖ ≤ ‖c.γ t - c.γ 0‖ :=
          (isMinOn_iff.mp hxmin) t ⟨htge, htle⟩
        have hnorm : ‖c.γ t - c.γ 0‖ = s := by
          rw [show c.γ t - c.γ 0 = c.γ 0 + r * v - c.γ 0 from by rw [htγ], hsub, norm_mul,
            Complex.norm_real, Real.norm_eq_abs, hrabs, hvnorm, mul_one]
        linarith [hmin, hsm, hnorm]
      · -- `t ∈ (2π - ε, 2π)`: periodicity reduces this to the local case
        have ht2 : t < 2 * Real.pi := by linarith [ht.2]
        have htabs : |t - 2 * Real.pi| ≤ ε := by
          rw [abs_le]
          exact ⟨by linarith, by linarith⟩
        have htne : t - 2 * Real.pi ≠ 0 := by linarith
        have hdet := hloc (t - 2 * Real.pi) htabs htne
        apply hdet
        have hper : c.γ (t - 2 * Real.pi) = c.γ t := by
          have hh := c.periodic_apply (t - 2 * Real.pi)
          rw [sub_add_cancel] at hh
          exact hh.symm
        rw [show c.γ (t - 2 * Real.pi) - c.γ 0 = c.γ 0 + r * v - c.γ 0 from by rw [hper, htγ],
          hsub, detV_smul_left, detV_self, mul_zero]
  refine ⟨min ε m, lt_min hεpos hmpos, ?_⟩
  intro s hs hsδ
  have hsε : s < ε := lt_of_lt_of_le hsδ (min_le_left _ _)
  have hsm : s < m := lt_of_lt_of_le hsδ (min_le_right _ _)
  constructor
  · exact key s s hs hsε hsm (Or.inl rfl)
  · have h' := key (-s) s hs hsε hsm (Or.inr rfl)
    have h2 : c.γ 0 + (↑(-s) : ℂ) * v = c.γ 0 - s * v := by
      rw [Complex.ofReal_neg, neg_mul]
      ring
    rwa [h2] at h'

end

end Work.Smooth.JordanSeparation
