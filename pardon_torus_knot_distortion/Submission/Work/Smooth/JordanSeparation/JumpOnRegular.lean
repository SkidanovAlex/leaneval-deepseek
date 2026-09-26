import Mathlib
import Submission.Work.Smooth.JordanSeparation.WeakDefs
import Submission.Work.Smooth.JordanSeparation.JumpIntegralWeak
import Submission.Work.Smooth.JordanSeparation.wind_normal_offset_sub
import Submission.Work.Smooth.JordanSeparation.exists_normal_offset_notMem_trace

/-!
# The index jumps by one at a *regular* parameter of a simple `C¹` curve

The chain of `Jump.lean` with the hypothesis `c.IsImmersion` replaced by `deriv c.γ 0 ≠ 0`
throughout: the normal offsets of `c.γ 0` miss the trace, the difference of the two winding
integrals equals `(1/π)·ê·∫ s·γ'/((γ-γ0)² + s²ê²)`, that integral tends to `π·conj ê`, hence the
winding difference tends to `1` and, being an integer difference, equals `1` for small `s > 0`, so
the indices differ by `1`.

* `exists_normal_offset_notMem_trace_of_deriv_ne_zero`;
* `wind_normal_offset_sub_of_deriv_ne_zero`;
* `tendsto_wind_normal_offset_sub_of_deriv_ne_zero`;
* `wind_normal_offset_sub_eq_one_of_deriv_ne_zero`;
* `ind_jump_of_deriv_ne_zero`.
-/

open Set intervalIntegral MeasureTheory
open Work.Smooth.Jordan

namespace Work.Smooth.JordanSeparation

noncomputable section

/-- **The local transversality fact.**  For an immersed `C¹` closed curve `c` there is `ε > 0`
such that the determinant of `γ t - γ 0` against the normal direction `normalField c 0` does not
vanish for `0 < |t| ≤ ε`.  Equivalently: near the parameter `0` the curve meets the normal line
at `γ 0` only at `γ 0` itself. -/
lemma exists_detV_normalField_ne_zero_near_of_deriv_ne_zero (c : Work.Smooth.Jordan.SmoothPlaneCurve)
    (hreg : deriv c.γ 0 ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| ≤ ε → t ≠ 0 →
      detV (c.γ t - c.γ 0) (normalField c 0) ≠ 0 := by
  -- `t ↦ detV (γ' t) (normalField c 0)` is continuous and positive at `0`
  obtain ⟨ε₁, hε₁, hpos⟩ : ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ t : ℝ, |t| < ε₁ →
      0 < detV (deriv c.γ t) (normalField c 0) := by
    have hg0 : 0 < detV (deriv c.γ 0) (normalField c 0) := by
      rw [detV_deriv_normalField_of_deriv_ne_zero c hreg]
      exact norm_pos_iff.mpr hreg
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
theorem exists_normal_offset_notMem_trace_of_deriv_ne_zero (c : Work.Smooth.Jordan.SmoothPlaneCurve)
    (hreg : deriv c.γ 0 ≠ 0) (hsimple : c.toPlaneCurve.IsSimple) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < s → s < δ →
      c.γ 0 + s * Work.Smooth.JordanSeparation.normalField c 0 ∉ c.trace ∧
      c.γ 0 - s * Work.Smooth.JordanSeparation.normalField c 0 ∉ c.trace := by
  set v : ℂ := normalField c 0 with hv
  have hvnorm : ‖v‖ = 1 := norm_normalField_of_deriv_ne_zero c hreg
  have hvne : v ≠ 0 := by
    intro h0
    rw [h0] at hvnorm
    simp at hvnorm
  -- the local radius, cut down so that it is also `< π`
  obtain ⟨ε₁, hε₁pos, hloc₁⟩ := exists_detV_normalField_ne_zero_near_of_deriv_ne_zero c hreg
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

/-- The purely algebraic core of `wind_normal_offset_sub`: for two complex points
`z ± s·N`, the difference of the corresponding `1`-form integrands is a single fraction whose
denominator is `(z - z0)² + s²T²` whenever `N = I·T`. -/
private theorem div_sub_div_normal' (z z0 T N g : ℂ) (s : ℂ) (hN : N = Complex.I * T)
    (hzp : z - (z0 + s * N) ≠ 0) (hzm : z - (z0 - s * N) ≠ 0)
    (hpi : (Real.pi : ℂ) ≠ 0) (hD : (z - z0) ^ 2 + s ^ 2 * T ^ 2 ≠ 0) :
    g / (z - (z0 + s * N)) - g / (z - (z0 - s * N))
      = (2 * (Real.pi : ℂ) * Complex.I) *
          ((1 / (Real.pi : ℂ)) * T * (s * g / ((z - z0) ^ 2 + s ^ 2 * T ^ 2))) := by
  subst hN
  have hden : (z - (z0 + s * (Complex.I * T))) * (z - (z0 - s * (Complex.I * T)))
      = (z - z0) ^ 2 + s ^ 2 * T ^ 2 := by
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [div_sub_div (b := z - (z0 + s * (Complex.I * T)))
        (d := z - (z0 - s * (Complex.I * T))) g g hzp hzm, hden]
  field_simp
  ring

theorem wind_normal_offset_sub_of_deriv_ne_zero (c : Work.Smooth.Jordan.SmoothPlaneCurve)
    (_hreg : deriv c.γ 0 ≠ 0) {s : ℝ} (hs : 0 < s)
    (hspos : c.γ 0 + s * Work.Smooth.JordanSeparation.normalField c 0 ∉ c.trace)
    (hsneg : c.γ 0 - s * Work.Smooth.JordanSeparation.normalField c 0 ∉ c.trace) :
    Work.Smooth.Jordan.wind c (c.γ 0 + s * Work.Smooth.JordanSeparation.normalField c 0)
        - Work.Smooth.Jordan.wind c (c.γ 0 - s * Work.Smooth.JordanSeparation.normalField c 0)
      = (1 / (Real.pi : ℂ)) * Work.Smooth.JordanSeparation.unitTangent c 0 *
        (∫ τ in (0 : ℝ)..(2 * Real.pi),
          (s * deriv c.γ τ) /
            ((c.γ τ - c.γ 0) ^ 2
              + (s : ℂ) ^ 2 * (Work.Smooth.JordanSeparation.unitTangent c 0) ^ 2)) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h2piI : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := Work.Smooth.Jordan.two_pi_I_ne_zero
  have hintp : IntervalIntegrable (windingIntegrand c (c.γ 0 + s * normalField c 0)) volume 0
      (2 * Real.pi) :=
    (Work.Smooth.Jordan.continuous_windingIntegrand c hspos).intervalIntegrable _ _
  have hintm : IntervalIntegrable (windingIntegrand c (c.γ 0 - s * normalField c 0)) volume 0
      (2 * Real.pi) :=
    (Work.Smooth.Jordan.continuous_windingIntegrand c hsneg).intervalIntegrable _ _
  have hpoint : ∀ τ : ℝ,
      windingIntegrand c (c.γ 0 + s * normalField c 0) τ
        - windingIntegrand c (c.γ 0 - s * normalField c 0) τ
      = (2 * (Real.pi : ℂ) * Complex.I) *
          ((1 / (Real.pi : ℂ)) * unitTangent c 0 *
            (s * deriv c.γ τ /
              ((c.γ τ - c.γ 0) ^ 2 + (s : ℂ) ^ 2 * (unitTangent c 0) ^ 2))) := by
    intro τ
    have hzp : c.γ τ - (c.γ 0 + (s : ℂ) * normalField c 0) ≠ 0 := by
      intro hh
      apply hspos
      rw [← sub_eq_zero.mp hh]
      exact c.mem_trace τ
    have hzm : c.γ τ - (c.γ 0 - (s : ℂ) * normalField c 0) ≠ 0 := by
      intro hh
      apply hsneg
      rw [← sub_eq_zero.mp hh]
      exact c.mem_trace τ
    have hden : (c.γ τ - (c.γ 0 + (s : ℂ) * normalField c 0))
        * (c.γ τ - (c.γ 0 - (s : ℂ) * normalField c 0))
        = (c.γ τ - c.γ 0) ^ 2 + (s : ℂ) ^ 2 * (unitTangent c 0) ^ 2 := by
      rw [normalField_def]
      ring_nf
      rw [Complex.I_sq]
      ring
    have hD : (c.γ τ - c.γ 0) ^ 2 + (s : ℂ) ^ 2 * (unitTangent c 0) ^ 2 ≠ 0 := by
      rw [← hden]
      exact mul_ne_zero hzp hzm
    rw [windingIntegrand_apply, windingIntegrand_apply]
    exact div_sub_div_normal' (c.γ τ) (c.γ 0) (unitTangent c 0) (normalField c 0)
      (deriv c.γ τ) (s : ℂ) (normalField_def c 0) hzp hzm hpi hD
  rw [wind_def, wind_def, windingPrimitive, windingPrimitive, ← mul_sub]
  rw [← intervalIntegral.integral_sub hintp hintm]
  rw [intervalIntegral.integral_congr (fun τ _ => hpoint τ)]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [← mul_assoc, inv_mul_cancel₀ h2piI, one_mul]

/-- **The difference of the two winding integrals at the normal offsets tends to `1`** (at a
regular parameter). -/
theorem tendsto_wind_normal_offset_sub_of_deriv_ne_zero (c : SmoothPlaneCurve)
    (hreg : deriv c.γ 0 ≠ 0) (hs : c.toPlaneCurve.IsSimple) :
    Filter.Tendsto (fun s : ℝ =>
        wind c (c.γ 0 + s * normalField c 0) - wind c (c.γ 0 - s * normalField c 0))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1) := by
  obtain ⟨δ₁, hδ₁, hnt⟩ := exists_normal_offset_notMem_trace_of_deriv_ne_zero c hreg hs
  have hJ := tendsto_winding_jump_integral_of_deriv_ne_zero c hreg hs
  have h₁ : Filter.Tendsto (fun s : ℝ => (1 / (Real.pi : ℂ)) * unitTangent c 0 *
      (∫ τ in (0 : ℝ)..(2 * Real.pi),
        (s * deriv c.γ τ) /
          ((c.γ τ - c.γ 0) ^ 2 + (s : ℂ) ^ 2 * (unitTangent c 0) ^ 2)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds ((1 / (Real.pi : ℂ)) * unitTangent c 0 *
        ((Real.pi : ℂ) * (starRingEnd ℂ) (unitTangent c 0)))) :=
    hJ.const_mul _
  have hval : (1 / (Real.pi : ℂ)) * unitTangent c 0 *
      ((Real.pi : ℂ) * (starRingEnd ℂ) (unitTangent c 0)) = 1 := by
    have hunit := norm_unitTangent_of_deriv_ne_zero c hreg
    have hconj : unitTangent c 0 * (starRingEnd ℂ) (unitTangent c 0) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hunit]
      norm_num
    calc (1 / (Real.pi : ℂ)) * unitTangent c 0 *
          ((Real.pi : ℂ) * (starRingEnd ℂ) (unitTangent c 0))
        = ((1 / (Real.pi : ℂ)) * (Real.pi : ℂ)) *
            (unitTangent c 0 * (starRingEnd ℂ) (unitTangent c 0)) := by ring
      _ = 1 := by rw [hconj]; field_simp
  rw [hval] at h₁
  have hmem : ∀ᶠ s : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), s ∈ Set.Ioo (0 : ℝ) δ₁ := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [isOpen_Iio.mem_nhds (show (0 : ℝ) < δ₁ by linarith)] with s hlt hpos
    exact ⟨hpos, hlt⟩
  refine h₁.congr' ?_
  filter_upwards [hmem] with s hs1
  have hspos : c.γ 0 + s * normalField c 0 ∉ c.trace := (hnt s hs1.1 hs1.2).1
  have hsneg : c.γ 0 - s * normalField c 0 ∉ c.trace := (hnt s hs1.1 hs1.2).2
  exact (wind_normal_offset_sub_of_deriv_ne_zero c hreg hs1.1 hspos hsneg).symm

/-- **The difference of the two winding integrals at the normal offsets is `1` for small
`s > 0`** (at a regular parameter). -/
theorem wind_normal_offset_sub_eq_one_of_deriv_ne_zero (c : SmoothPlaneCurve)
    (hreg : deriv c.γ 0 ≠ 0) (hs : c.toPlaneCurve.IsSimple) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < s → s < δ →
      wind c (c.γ 0 + s * normalField c 0) - wind c (c.γ 0 - s * normalField c 0) = 1 := by
  obtain ⟨δ₁, hδ₁, hnt⟩ := exists_normal_offset_notMem_trace_of_deriv_ne_zero c hreg hs
  have htend := tendsto_wind_normal_offset_sub_of_deriv_ne_zero c hreg hs
  have hev : ∀ᶠ s : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      dist (wind c (c.γ 0 + s * normalField c 0)
        - wind c (c.γ 0 - s * normalField c 0)) (1 : ℂ) < (1 / 2 : ℝ) :=
    (Metric.tendsto_nhds.mp htend) (1 / 2) (by norm_num)
  rw [eventually_nhdsWithin_iff] at hev
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hεspec⟩ := hev
  refine ⟨min ε δ₁, lt_min hε hδ₁, fun s hs0 hslt => ?_⟩
  have hε' : dist s (0 : ℝ) < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hs0]
    exact lt_of_lt_of_le hslt (min_le_left _ _)
  have hP : dist (wind c (c.γ 0 + s * normalField c 0)
      - wind c (c.γ 0 - s * normalField c 0)) (1 : ℂ) < (1 / 2 : ℝ) := hεspec hε' hs0
  have hsδ₁ : s < δ₁ := lt_of_lt_of_le hslt (min_le_right _ _)
  have hnt' := hnt s hs0 hsδ₁
  have hint : ∃ k : ℤ, wind c (c.γ 0 + s * normalField c 0)
      - wind c (c.γ 0 - s * normalField c 0) = (k : ℂ) := by
    obtain ⟨k, hk⟩ := wind_mem_int c hnt'.1
    obtain ⟨l, hl⟩ := wind_mem_int c hnt'.2
    exact ⟨k - l, by rw [hk, hl]; push_cast; ring⟩
  obtain ⟨m, hm⟩ := hint
  have hm1 : ‖(((m - 1 : ℤ)) : ℂ)‖ < (1 / 2 : ℝ) := by
    have hcast : (((m - 1 : ℤ)) : ℂ) = (m : ℂ) - 1 := by
      rw [Int.cast_sub, Int.cast_one]
    rw [hcast, ← hm, dist_eq_norm] at *
    exact hP
  have hm1Z : |(m - 1 : ℤ)| < 1 := by
    have h2 : (((|(m - 1 : ℤ)| : ℤ)) : ℝ) < 1 := by
      rw [Int.cast_abs, ← Complex.norm_intCast]
      linarith [hm1]
    exact_mod_cast h2
  have hm0 : m - 1 = 0 := Int.abs_lt_one_iff.mp hm1Z
  rw [hm]
  have : m = 1 := by omega
  rw [this]; norm_num

/-- **The index jumps by one at a regular parameter of a simple `C¹` curve.** -/
theorem ind_jump_of_deriv_ne_zero (c : SmoothPlaneCurve) (hreg : deriv c.γ 0 ≠ 0)
    (hs : c.toPlaneCurve.IsSimple) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < s → s < δ →
      c.γ 0 + s * normalField c 0 ∉ c.trace ∧
        c.γ 0 - s * normalField c 0 ∉ c.trace ∧
        ind c (c.γ 0 + s * normalField c 0) = ind c (c.γ 0 - s * normalField c 0) + 1 := by
  obtain ⟨δ₁, hδ₁, hnt⟩ := exists_normal_offset_notMem_trace_of_deriv_ne_zero c hreg hs
  obtain ⟨δ₂, hδ₂, hwind⟩ := wind_normal_offset_sub_eq_one_of_deriv_ne_zero c hreg hs
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun s hs0 hslt => ?_⟩
  have hs₁ : s < δ₁ := lt_of_lt_of_le hslt (min_le_left _ _)
  have hs₂ : s < δ₂ := lt_of_lt_of_le hslt (min_le_right _ _)
  obtain ⟨hpos, hneg⟩ := hnt s hs0 hs₁
  refine ⟨hpos, hneg, ?_⟩
  have hw := hwind s hs0 hs₂
  obtain ⟨k, hk⟩ := wind_mem_int c hpos
  obtain ⟨l, hl⟩ := wind_mem_int c hneg
  have hcast : ((ind c (c.γ 0 + s * normalField c 0)
      - ind c (c.γ 0 - s * normalField c 0) : ℤ) : ℂ) = 1 := by
    rw [Int.cast_sub, ind_spec c ⟨k, hk⟩, ind_spec c ⟨l, hl⟩]
    exact hw
  have hm : ind c (c.γ 0 + s * normalField c 0) - ind c (c.γ 0 - s * normalField c 0)
      = (1 : ℤ) := Int.cast_injective (by rw [hcast]; norm_num)
  omega

end

end Work.Smooth.JordanSeparation
