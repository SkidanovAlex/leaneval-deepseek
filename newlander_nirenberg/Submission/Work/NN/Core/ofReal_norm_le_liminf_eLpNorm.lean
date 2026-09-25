import Mathlib
import Submission.Work.NN.Core.CnPert

/-!
# `‖u c‖` is bounded by the `liminf` of the `L^p`-seminorms of `u` on a ball

If `u : ℂⁿ → ℂ` is continuous, `c : ℂⁿ`, `r > 0` and `E j → ∞` with `E j ≥ 1`, then
`‖u c‖ ≤ liminf_j ‖u‖_{L^{E j}(ball c r)}`.  This is the "the `L^p` seminorm increases to the
`ess sup` as `p → ∞`" fact, applied at the single point `c`; it is used to recover a *pointwise*
bound from a uniform `L^p` bound with diverging exponent.

The proof has three ingredients, all isolated below:

* `ofReal_mul_rpow_measure_le_eLpNorm` — a measure-theoretic lower bound: if `b ≤ ‖f‖` a.e. then
  `b · (μ univ)^{1/p} ≤ ‖f‖_{L^p}` (the reverse of Mathlib's `eLpNorm_le_of_ae_bound`).
* `exists_ball_norm_le_of_continuousAt` — continuity at `c` produces a ball on which `b ≤ ‖u‖`
  for every `b < ‖u c‖`.
* `eventually_ofReal_le_ofReal_mul_rpow_inv` — `b · (μ s)^{1/E j} → b` along jumps of a measure
  with `0 < μ s` (handling `μ s = ∞` separately); consequently a fixed `b < b₀` is bounded by
  `b₀ · (μ s)^{1/E j}` eventually.

Finally `ofReal ‖u c‖ = ⨆_{b < ‖u c‖} ofReal b` (`le_of_forall_lt`) upgrades the eventual
bounds for every `b < ‖u c‖` to the stated inequality.
-/

noncomputable section

open scoped ENNReal
open MeasureTheory Filter

namespace Work.NN.Core

/-- **Reverse of `eLpNorm_le_of_ae_bound`.**  If `f : α → ℂ` is a.e. strongly measurable and
`b ≤ ‖f x‖` a.e., with `b ≥ 0`, then `ofReal b * (μ univ) ^ (1 / p) ≤ eLpNorm f (ofReal p) μ`
for every real `p ≥ 1`.

Indeed `(eLpNorm f (ofReal p) μ) ^ p = ∫⁻ ‖f‖ₑ ^ p`, which dominates
`∫⁻ (ofReal b) ^ p = (ofReal b)^p · μ univ`; taking `p`-th roots and splitting
`(ofReal b)^p · μ univ` into `((ofReal b)^p) · μ univ` gives the claim. -/
theorem ofReal_mul_rpow_measure_le_eLpNorm {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℂ} (hf : AEStronglyMeasurable f μ) {b : ℝ} (_hb : 0 ≤ b)
    (hbd : ∀ᵐ x ∂μ, b ≤ ‖f x‖) {p : ℝ} (hp : 1 ≤ p) :
    ENNReal.ofReal b * (μ Set.univ) ^ (1 / p) ≤
      MeasureTheory.eLpNorm f (ENNReal.ofReal p) μ := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hpne0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp0
  have hpnetop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hpne0 hpnetop hf,
    ENNReal.toReal_ofReal hp0.le]
  have hbpow : ∫⁻ x, (ENNReal.ofReal b) ^ p ∂μ ≤ ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
    apply lintegral_mono_ae
    filter_upwards [hbd] with x hx
    refine ENNReal.rpow_le_rpow ?_ hp0.le
    have hnorm : ‖f x‖ₑ = ENNReal.ofReal ‖f x‖ := by
      rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal]; norm_cast
    rw [hnorm]; exact ENNReal.ofReal_le_ofReal hx
  rw [lintegral_const] at hbpow
  have h1 : ((ENNReal.ofReal b) ^ p) ^ (1 / p) = ENNReal.ofReal b := by
    rw [← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one]
  have h2 : (ENNReal.ofReal b) * (μ Set.univ) ^ (1 / p)
      = ((ENNReal.ofReal b) ^ p * μ Set.univ) ^ (1 / p) := by
    have := ENNReal.mul_rpow_of_nonneg ((ENNReal.ofReal b) ^ p) (μ Set.univ)
      (z := 1 / p) (by positivity)
    rw [this, h1]
  calc ENNReal.ofReal b * (μ Set.univ) ^ (1 / p)
      = ((ENNReal.ofReal b) ^ p * μ Set.univ) ^ (1 / p) := h2
    _ ≤ (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ^ (1 / p) := ENNReal.rpow_le_rpow hbpow (by positivity)

/-- **Continuity gives a local lower bound.**  If `f` is continuous at `c` then for every
`b < ‖f c‖` there is a ball around `c` on which `b ≤ ‖f‖`. -/
lemma exists_ball_norm_le_of_continuousAt {E : Type*} [PseudoMetricSpace E] {f : E → ℂ} {c : E}
    (hc : ContinuousAt f c) {b : ℝ} (hb : b < ‖f c‖) :
    ∃ s > 0, ∀ x ∈ Metric.ball c s, b ≤ ‖f x‖ := by
  have hε : 0 < ‖f c‖ - b := sub_pos.mpr hb
  obtain ⟨δ, hδpos, hδ⟩ := (Metric.continuousAt_iff.mp hc) (‖f c‖ - b) hε
  refine ⟨δ, hδpos, fun x hx => ?_⟩
  have hlt : dist (f x) (f c) < ‖f c‖ - b := hδ hx
  rw [dist_eq_norm] at hlt
  have h2 : ‖f c‖ - ‖f x‖ ≤ ‖f x - f c‖ := by
    simpa [norm_sub_rev] using norm_sub_norm_le (f c) (f x)
  linarith

/-- **The measure factor tends to `1`.**  For a measurable set `s` with `0 < μ s`, a real
sequence `E j → ∞` with `E j ≥ 1`, and real numbers `b < b₀` with `0 < b₀`, we have
`ofReal b ≤ ofReal b₀ * (μ s) ^ (1 / E j)` eventually. -/
lemma eventually_ofReal_le_ofReal_mul_rpow_inv {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {s : Set α} (hμpos : 0 < μ s) {E : ℕ → ℝ} (hEtop : Tendsto E atTop atTop)
    (hE : ∀ j, 1 ≤ E j) {b b0 : ℝ} (hbb0 : b < b0) (hb0pos : 0 < b0) :
    ∀ᶠ j in atTop, ENNReal.ofReal b ≤ ENNReal.ofReal b0 * (μ s) ^ (1 / E j) := by
  by_cases htop : μ s = ⊤
  · filter_upwards with j
    rw [htop, ENNReal.top_rpow_of_pos
      (one_div_pos.mpr (lt_of_lt_of_le zero_lt_one (hE j)))]
    rw [ENNReal.mul_top]
    · exact le_top
    · exact (ENNReal.ofReal_pos.mpr hb0pos).ne'
  · set m := (μ s).toReal with hm
    have hmpos : 0 < m := ENNReal.toReal_pos hμpos.ne' htop
    have hinv : Tendsto (fun j => (E j)⁻¹) atTop (nhds 0) := hEtop.inv_tendsto_atTop
    have hrpow : Tendsto (fun j => m ^ (E j)⁻¹) atTop (nhds (m ^ (0:ℝ))) :=
      (Real.continuousAt_const_rpow hmpos.ne').tendsto.comp hinv
    rw [Real.rpow_zero] at hrpow
    have hev : ∀ᶠ j in atTop, b ≤ b0 * m ^ (E j)⁻¹ := by
      have hclose : ∀ᶠ j in atTop, dist (m ^ (E j)⁻¹) 1 < (b0 - b) / (2 * b0) :=
        Metric.tendsto_nhds.mp hrpow _ (by positivity)
      filter_upwards [hclose] with j hj
      rw [Real.dist_eq] at hj
      have h2 := abs_lt.mp hj
      have hb0' : b0 * (1 - (b0 - b) / (2 * b0)) ≥ b := by
        rw [mul_sub, mul_one]
        have : b0 * ((b0 - b) / (2 * b0)) = (b0 - b) / 2 := by field_simp
        rw [this]; linarith
      calc b ≤ b0 * (1 - (b0 - b) / (2 * b0)) := hb0'
        _ ≤ b0 * m ^ (E j)⁻¹ := by
            apply mul_le_mul_of_nonneg_left _ hb0pos.le
            linarith [h2.1]
    filter_upwards [hev] with j hj
    rw [show μ s = ENNReal.ofReal m from (ENNReal.ofReal_toReal htop).symm,
      ENNReal.ofReal_rpow_of_nonneg hmpos.le
        (one_div_nonneg.mpr (le_of_lt (lt_of_lt_of_le zero_lt_one (hE j)))),
      ← ENNReal.ofReal_mul hb0pos.le, one_div]
    exact ENNReal.ofReal_le_ofReal hj

set_option linter.unusedVariables false in
theorem ofReal_norm_le_liminf_eLpNorm {n : ℕ} (hn : 0 < n) {u : Cn n → ℂ} (hu : Continuous u)
    {c : Cn n} {r : ℝ} (hr : 0 < r) {E : ℕ → ℝ} (hE : ∀ j, 1 ≤ E j)
    (hEtop : Filter.Tendsto E Filter.atTop Filter.atTop) :
    ENNReal.ofReal ‖u c‖ ≤ Filter.liminf
      (fun j => MeasureTheory.eLpNorm u (ENNReal.ofReal (E j))
        (MeasureTheory.volume.restrict (Metric.ball c r))) Filter.atTop := by
  -- Every `b < ‖u c‖` is eventually below the `L^{E j}` seminorm on the ball.
  have key : ∀ b : ℝ, 0 ≤ b → b < ‖u c‖ →
      ∀ᶠ j in Filter.atTop, ENNReal.ofReal b ≤ MeasureTheory.eLpNorm u (ENNReal.ofReal (E j))
        (MeasureTheory.volume.restrict (Metric.ball c r)) := by
    intro b hb0 hbc
    set b0 : ℝ := (b + ‖u c‖) / 2 with hb0def
    have hbb0 : b < b0 := by rw [hb0def]; linarith
    have hb0a : b0 < ‖u c‖ := by rw [hb0def]; linarith
    have hb0pos : 0 < b0 := lt_of_le_of_lt hb0 hbb0
    obtain ⟨s, hspos, hs⟩ := exists_ball_norm_le_of_continuousAt hu.continuousAt hb0a
    set s' : ℝ := min s r with hs'def
    have hs'pos : 0 < s' := lt_min hspos hr
    have hs'le_r : s' ≤ r := min_le_right _ _
    have hbound : ∀ x ∈ Metric.ball c s', b0 ≤ ‖u x‖ := fun x hx =>
      hs x (Metric.ball_subset_ball (min_le_left _ _) hx)
    -- The lower bound on the small ball, from the general measure-theoretic lemma.
    have hsmall : ∀ j, ENNReal.ofReal b0
          * (MeasureTheory.volume (Metric.ball c s')) ^ (1 / E j)
        ≤ MeasureTheory.eLpNorm u (ENNReal.ofReal (E j))
            (MeasureTheory.volume.restrict (Metric.ball c s')) := by
      intro j
      have hbd : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Metric.ball c s')), b0 ≤ ‖u x‖ := by
        rw [ae_restrict_iff' Metric.isOpen_ball.measurableSet]
        exact Filter.Eventually.of_forall fun x hx => hbound x hx
      have hmeas : AEStronglyMeasurable u (MeasureTheory.volume.restrict (Metric.ball c s')) :=
        (hu.aestronglyMeasurable (μ := MeasureTheory.volume)).restrict
      have hh := ofReal_mul_rpow_measure_le_eLpNorm hmeas hb0pos.le hbd (hE j)
      rwa [Measure.restrict_apply_univ] at hh
    -- Enlarge the ball to the given one.
    have hbig : ∀ j, MeasureTheory.eLpNorm u (ENNReal.ofReal (E j))
            (MeasureTheory.volume.restrict (Metric.ball c s'))
        ≤ MeasureTheory.eLpNorm u (ENNReal.ofReal (E j))
            (MeasureTheory.volume.restrict (Metric.ball c r)) := by
      intro j
      exact MeasureTheory.eLpNorm_mono_measure _
        (Measure.restrict_mono (Metric.ball_subset_ball hs'le_r) le_rfl)
    have hchain : ∀ j, ENNReal.ofReal b0
          * (MeasureTheory.volume (Metric.ball c s')) ^ (1 / E j)
        ≤ MeasureTheory.eLpNorm u (ENNReal.ofReal (E j))
            (MeasureTheory.volume.restrict (Metric.ball c r)) :=
      fun j => (hsmall j).trans (hbig j)
    have hvolpos : 0 < MeasureTheory.volume (Metric.ball c s') :=
      Metric.measure_ball_pos (MeasureTheory.volume : MeasureTheory.Measure (Cn n)) c hs'pos
    have hlim := eventually_ofReal_le_ofReal_mul_rpow_inv MeasureTheory.volume hvolpos
      hEtop hE hbb0 hb0pos
    filter_upwards [hlim] with j hj
    exact hj.trans (hchain j)
  -- Hence `ofReal b ≤ liminf` for every `b < ‖u c‖`.
  have key2 : ∀ b : ℝ, 0 ≤ b → b < ‖u c‖ →
      ENNReal.ofReal b ≤ Filter.liminf
        (fun j => MeasureTheory.eLpNorm u (ENNReal.ofReal (E j))
          (MeasureTheory.volume.restrict (Metric.ball c r))) Filter.atTop :=
    fun b hb0 hbc => Filter.le_liminf_of_le (by isBoundedDefault) (key b hb0 hbc)
  -- `ofReal ‖u c‖` is the supremum of `ofReal b` over `b < ‖u c‖`.
  refine le_of_forall_lt fun c' hc' => ?_
  have hc'top : c' ≠ ⊤ := ne_top_of_lt hc'
  have hc'lt : c'.toReal < ‖u c‖ := (ENNReal.lt_ofReal_iff_toReal_lt hc'top).mp hc'
  set b : ℝ := (c'.toReal + ‖u c‖) / 2 with hbdef
  have hb0 : 0 ≤ b := by
    rw [hbdef]; linarith [ENNReal.toReal_nonneg (a := c'), norm_nonneg (u c)]
  have hbc : b < ‖u c‖ := by rw [hbdef]; linarith
  have hc'b : c' < ENNReal.ofReal b := by
    rw [ENNReal.lt_ofReal_iff_toReal_lt hc'top, hbdef]; linarith
  exact lt_of_lt_of_le hc'b (key2 b hb0 hbc)

end Work.NN.Core
