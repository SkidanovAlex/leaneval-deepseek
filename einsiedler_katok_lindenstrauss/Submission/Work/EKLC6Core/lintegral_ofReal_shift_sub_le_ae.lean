import Mathlib
import Submission.Work.EKLC6Core.lintegral_ofReal_sub_comp_le

/-!
# `EKLC6Core.lintegral_ofReal_shift_sub_le_ae`

Almost-everywhere version of `Work.EKLC6Core.lintegral_ofReal_shift_sub_le`.

If `T` preserves the probability measure `μ`, `Φ` is a.e. measurable and
`Φ x ≤ J + Φ (T x)` for a.e. `x` with `0 ≤ J`, then the a.e. nonnegative defect
`J + Φ (T x) - Φ x` has Lebesgue integral (of its `ENNReal.ofReal`) at most `ofReal J`.

The proof is the truncation/Fatou argument of `lintegral_ofReal_shift_sub_le`: clipping `Φ`
to the window `[-n, n]` preserves the one-sided hypothesis, the clipped defect has integral
exactly `J` by invariance of `μ` under `T`, and Fatou's lemma transfers the bound to the
limit.  Only the step producing almost-everywhere nonnegativity of the clipped defect uses
the hypothesis, so it can be relaxed to hold only almost everywhere.
-/

namespace Work.EKLC6Core

open MeasureTheory

/-- Truncation of `Φ` to the window `[-n, n]`. -/
private def truncW {X : Type*} (Φ : X → ℝ) (n : ℕ) (x : X) : ℝ :=
  max (min (Φ x) (n : ℝ)) (-(n : ℝ))

/-- Truncating `a` above by `n` preserves an inequality `a ≤ J + b`
(needed for the "min" part of the window truncation). -/
private lemma min_le_add_minW {a b J n : ℝ} (hJ : 0 ≤ J) (h : a ≤ J + b) :
    min a n ≤ J + min b n := by
  rcases lt_or_ge a n with ha | ha
  · rw [min_eq_left (le_of_lt ha)]
    rcases lt_or_ge b n with hb | hb
    · rw [min_eq_left (le_of_lt hb)]; linarith
    · rw [min_eq_right hb]; linarith
  · rw [min_eq_right ha]
    rcases lt_or_ge b n with hb | hb
    · rw [min_eq_left (le_of_lt hb)]; linarith
    · rw [min_eq_right hb]; linarith

/-- Truncating `a` below by `-n` preserves an inequality `a ≤ J + b`
(needed for the "max" part of the window truncation). -/
private lemma max_le_add_maxW {a b J n : ℝ} (hJ : 0 ≤ J) (h : a ≤ J + b) :
    max a (-n) ≤ J + max b (-n) := by
  rcases lt_or_ge a (-n) with ha | ha
  · rw [max_eq_right (le_of_lt ha)]
    rcases lt_or_ge b (-n) with hb | hb
    · rw [max_eq_right (le_of_lt hb)]; linarith
    · rw [max_eq_left hb]; linarith
  · rw [max_eq_left ha]
    rcases lt_or_ge b (-n) with hb | hb
    · rw [max_eq_right (le_of_lt hb)]; linarith
    · rw [max_eq_left hb]; linarith

/-- For a fixed real `y`, the window truncation `max (min y n) (-n)` equals `y`
for all sufficiently large `n`. -/
private lemma eventually_truncW_eq {X : Type*} (Φ : X → ℝ) (x : X) :
    ∀ᶠ n : ℕ in Filter.atTop, truncW Φ n x = Φ x := by
  filter_upwards [tendsto_natCast_atTop_atTop.eventually (Filter.Ici_mem_atTop (Φ x)),
    tendsto_natCast_atTop_atTop.eventually (Filter.Ici_mem_atTop (-(Φ x)))] with n hn1 hn2
  have hn2' : -(n : ℝ) ≤ Φ x := by linarith
  rw [truncW, min_eq_left hn1, max_eq_left hn2']

/-- **Key coboundary estimate, almost-everywhere form.**  If `T` preserves the probability
measure `μ` and `Φ x ≤ J + Φ (T x)` for almost every `x`, with `0 ≤ J`, then the (a.e.
nonnegative) defect function `J + Φ (T x) - Φ x` has Lebesgue integral at most `J`.

The proof truncates `Φ` to the window `[-n, n]` (which preserves the hypothesis), for which
the integral of the defect equals `J` exactly by invariance of `μ`; Fatou's lemma then gives
the bound for `Φ` itself. -/
theorem lintegral_ofReal_shift_sub_le_ae {X : Type*} [MeasurableSpace X]
    {μ : MeasureTheory.Measure X} [MeasureTheory.IsProbabilityMeasure μ] {T : X → X}
    (hmp : MeasureTheory.MeasurePreserving T μ μ) {Φ : X → ℝ} (hΦ : AEMeasurable Φ μ)
    {J : ℝ} (hJ : 0 ≤ J) (hle : ∀ᵐ x ∂μ, Φ x ≤ J + Φ (T x)) :
    ∫⁻ x, ENNReal.ofReal (J + Φ (T x) - Φ x) ∂μ ≤ ENNReal.ofReal J := by
  have htr_ae : ∀ n, AEMeasurable (truncW Φ n) μ := by
    intro n
    exact (hΦ.min aemeasurable_const).max aemeasurable_const
  -- the truncation preserves the one-sided hypothesis, almost everywhere
  have hle_tr : ∀ n, ∀ᵐ x ∂μ, truncW Φ n x ≤ J + truncW Φ n (T x) := by
    intro n
    filter_upwards [hle] with x hx
    exact max_le_add_maxW (n := (n : ℝ)) hJ (min_le_add_minW (n := (n : ℝ)) hJ hx)
  have hg_bound : ∀ n x, |truncW Φ n x| ≤ (n : ℝ) := by
    intro n x
    rw [abs_le]
    constructor
    · exact le_max_right _ _
    · apply max_le
      · exact min_le_right _ _
      · have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith
  have hg_int : ∀ n, Integrable (truncW Φ n) μ := by
    intro n
    refine Integrable.of_bound ?_ (n : ℝ) ?_
    · exact (aestronglyMeasurable_iff_aemeasurable).2 (htr_ae n)
    · filter_upwards with x
      rw [Real.norm_eq_abs]
      exact hg_bound n x
  have hcomp : ∀ n, ∫ x, truncW Φ n (T x) ∂μ = ∫ x, truncW Φ n x ∂μ := by
    intro n
    rw [← MeasureTheory.integral_map (φ := T) (f := truncW Φ n) hmp.aemeasurable
      (by rw [hmp.map_eq]; exact (hg_int n).aestronglyMeasurable)]
    rw [hmp.map_eq]
  have hval : ∀ n, ∫⁻ x, ENNReal.ofReal (J + truncW Φ n (T x) - truncW Φ n x) ∂μ
      = ENNReal.ofReal J := by
    intro n
    have hgT_int : Integrable (fun x => truncW Φ n (T x)) μ :=
      (hmp.integrable_comp (hg_int n).aestronglyMeasurable).2 (hg_int n)
    have hInt : Integrable (fun x => J + truncW Φ n (T x) - truncW Φ n x) μ :=
      ((integrable_const J).add hgT_int).sub (hg_int n)
    have hnn : 0 ≤ᵐ[μ] (fun x => J + truncW Φ n (T x) - truncW Φ n x) := by
      filter_upwards [hle_tr n] with x hx
      show (0 : ℝ) ≤ J + truncW Φ n (T x) - truncW Φ n x
      linarith
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hnn]
    congr 1
    have key2 : ∫ x, (J + truncW Φ n (T x)) - truncW Φ n x ∂μ
        = ∫ x, J + truncW Φ n (T x) ∂μ - ∫ x, truncW Φ n x ∂μ :=
      integral_sub ((integrable_const J).add hgT_int) (hg_int n)
    have key1 : ∫ x, J + truncW Φ n (T x) ∂μ
        = ∫ x, J ∂μ + ∫ x, truncW Φ n (T x) ∂μ :=
      integral_add (integrable_const J) hgT_int
    rw [key2, key1, hcomp n]
    simp [MeasureTheory.integral_const]
  have hF_ae : ∀ n, AEMeasurable
      (fun x => ENNReal.ofReal (J + truncW Φ n (T x) - truncW Φ n x)) μ := by
    intro n
    have h1 : AEMeasurable (fun x => truncW Φ n (T x)) μ :=
      (htr_ae n).comp_quasiMeasurePreserving hmp.quasiMeasurePreserving
    have h3 : AEMeasurable (fun x => J + truncW Φ n (T x) - truncW Φ n x) μ :=
      ((aemeasurable_const.add h1).sub (htr_ae n))
    exact ENNReal.measurable_ofReal.comp_aemeasurable h3
  have hlim : ∀ x, Filter.liminf
        (fun n => ENNReal.ofReal (J + truncW Φ n (T x) - truncW Φ n x)) Filter.atTop
      = ENNReal.ofReal (J + Φ (T x) - Φ x) := by
    intro x
    have hev : ∀ᶠ n in Filter.atTop,
        ENNReal.ofReal (J + truncW Φ n (T x) - truncW Φ n x)
          = ENNReal.ofReal (J + Φ (T x) - Φ x) := by
      filter_upwards [eventually_truncW_eq Φ x, eventually_truncW_eq Φ (T x)] with n h1 h2
      rw [h1, h2]
    rw [Filter.liminf_congr hev, Filter.liminf_const]
  have hFatou := MeasureTheory.lintegral_liminf_le' (μ := μ) (u := Filter.atTop)
      (f := fun n x => ENNReal.ofReal (J + truncW Φ n (T x) - truncW Φ n x)) hF_ae
  have hrhs : Filter.liminf
        (fun n => ∫⁻ x, ENNReal.ofReal (J + truncW Φ n (T x) - truncW Φ n x) ∂μ)
        Filter.atTop = ENNReal.ofReal J := by
    simp_rw [hval]
    exact Filter.liminf_const _
  have hlhs : ∫⁻ x, Filter.liminf
        (fun n => ENNReal.ofReal (J + truncW Φ n (T x) - truncW Φ n x)) Filter.atTop ∂μ
      = ∫⁻ x, ENNReal.ofReal (J + Φ (T x) - Φ x) ∂μ := by
    apply MeasureTheory.lintegral_congr_ae
    filter_upwards with x
    exact hlim x
  calc ∫⁻ x, ENNReal.ofReal (J + Φ (T x) - Φ x) ∂μ
      = ∫⁻ x, Filter.liminf
          (fun n => ENNReal.ofReal (J + truncW Φ n (T x) - truncW Φ n x)) Filter.atTop ∂μ :=
        hlhs.symm
    _ ≤ Filter.liminf
          (fun n => ∫⁻ x, ENNReal.ofReal (J + truncW Φ n (T x) - truncW Φ n x) ∂μ)
          Filter.atTop := hFatou
    _ = ENNReal.ofReal J := hrhs

end Work.EKLC6Core
