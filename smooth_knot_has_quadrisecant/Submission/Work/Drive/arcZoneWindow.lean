import Mathlib
import Submission.Work.Drive.chordSweepSmooth
import Submission.Work.Drive.chordSweepDefs
import Submission.Work.Drive.chordFrame
import Submission.Work.Drive.sweepBlurFacts
import Submission.Work.Drive.needleProfileDefs

/-!
# The window geometry of the chord sweep's arc zone

This module collects the elementary *window* facts on which the star-shapedness of the needle
(`Submission/Work/Drive/needleFlatteningData.lean`) rests.  All of them are statements about the
elementary data of a `Work.Drive.SweepData`: the lifts `taR`, `tbR` of the band arc, the width
`sweepW' = tbR - taR`, and the sawtooth `sweepParam`.

* `Work.Drive.sweepParam_lt_of_le_half` — **the cell lemma**: if `sweepParam x₁ ≤ 1/2` and
  `0 < x₂ - x₁ < period/2` then `sweepParam x₁ < sweepParam x₂`.  This is what makes the needle's
  arc zone monotone in its loop parameter: the whole loop-parameter window of a point of the arc
  zone lies in the *first half of a single cell*, so the sawtooth is strictly increasing across it
  (the hypothesis `t₂ - t₁ < period/2` of the arc-zone statement is exactly what rules out a jump of
  the sawtooth).

* `Work.Drive.exists_window_small` — the *lifting* window: near the collapsed end `0` both the
  displacement of `taR` and the width `sweepW'` are as small as wanted.  This is what lets all the
  loops of the sweep window be compared with one another (the retained arcs of the window all lie in
  a short parameter interval).

* `Work.Drive.inner_velocity_chord_pos` — **the short-arc tangent estimate**: over a short parameter
  interval `[a,b]` the tangent of an analytic knot never makes an obtuse angle with the chord
  `r b - r a`.  This is the pointwise positivity of the chord coordinate.

* `Work.Drive.chordEndB_sub_chordEndA` — the needle's chord vector as the bump-weighted average of
  the loops' chords.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology intervalIntegral

/-! ## 1. The cell lemma for `sweepParam` -/

/-- **`sweepParam` is strictly increasing across a box in the first half of a cell.**  If
`sweepParam x₁ ≤ 1/2` (so `x₁` lies in the first half of the cell `[k·period, (k+1)·period]` of which
it is the floor) and the box `[x₁, x₂]` is shorter than half a period, then `x₂` lies in the *same*
cell and to the right of `x₁`, so `sweepParam x₂ = sweepParam x₁ + (x₂ - x₁)/period > sweepParam x₁`.
The strict bound `x₂ - x₁ < period / 2` is optimal: at `x₂ - x₁ = period / 2` the conclusion can fail
(`x₁` at the beginning of a cell, `x₂` at its middle). -/
theorem sweepParam_lt_of_le_half {x₁ x₂ : ℝ} (h1 : sweepParam x₁ ≤ 1 / 2)
    (hlt : x₁ < x₂) (hd : x₂ - x₁ < period / 2) : sweepParam x₁ < sweepParam x₂ := by
  have hp : 0 < period := period_pos
  set k : ℤ := ⌊x₁ / period⌋ with hk
  have h1' : x₁ / period - (k : ℝ) ≤ 1 / 2 := by
    have h := h1
    rw [sweepParam] at h
    simpa [hk] using h
  have hx1 : x₁ / period ≤ (k : ℝ) + 1 / 2 := by linarith
  have hx2lt : x₂ / period < (k : ℝ) + 1 := by
    have h2 : x₂ / period < x₁ / period + 1 / 2 := by
      rw [div_lt_iff₀ hp]
      have hx : (x₁ / period + 1 / 2) * period = x₁ + period / 2 := by
        rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hp)]
        ring
      rw [hx]
      linarith
    linarith
  have hfloor : ⌊x₂ / period⌋ = k := by
    rw [Int.floor_eq_iff]
    constructor
    · have hkx₁ : (k : ℝ) ≤ x₁ / period := by
        have h := Int.floor_le (x₁ / period)
        simpa [hk] using h
      have hlt' : x₁ / period < x₂ / period := by
        rw [div_lt_div_iff_of_pos_right hp]
        exact hlt
      linarith
    · exact hx2lt
  have hsp1 : sweepParam x₁ = x₁ / period - (k : ℝ) := by
    rw [sweepParam]
  have hsp2 : sweepParam x₂ = x₂ / period - (k : ℝ) := by
    rw [sweepParam, hfloor]
  rw [hsp1, hsp2]
  have hlt' : x₁ / period < x₂ / period := by
    rw [div_lt_div_iff_of_pos_right hp]
    exact hlt
  linarith

/-! ## 2. The lifting window at the collapsed end -/

lemma arcWin_clampI_continuous : Continuous (clampI : ℝ → Set.Icc (0 : ℝ) 1) :=
  Continuous.subtype_mk (continuous_const.min (continuous_const.max continuous_id))
    (fun x => (clampI x).2)

lemma arcWin_taR_continuous {d : BandArcData} (D : SweepData d) : Continuous (taR D) :=
  D.cont_ta.comp arcWin_clampI_continuous

lemma arcWin_tbR_continuous {d : BandArcData} (D : SweepData d) : Continuous (tbR D) :=
  D.cont_tb.comp arcWin_clampI_continuous

lemma arcWin_sweepW'_continuous {d : BandArcData} (D : SweepData d) : Continuous (sweepW' D) :=
  (arcWin_tbR_continuous D).sub (arcWin_taR_continuous D)

lemma sweepW'_zero {d : BandArcData} (D : SweepData d) : sweepW' D 0 = 0 := by
  have h0 : clampI (0 : ℝ) = (0 : Set.Icc (0 : ℝ) 1) := Subtype.ext (by simp [clampI])
  have h : sweepW' D 0 = D.tb (0 : Set.Icc (0 : ℝ) 1) - D.ta (0 : Set.Icc (0 : ℝ) 1) := by
    simp only [sweepW', taR, tbR, h0]
  rw [h, D.left_eq]; ring

/-- **The lifting window at the collapsed end.**  For any `w > 0` the displacement of the left lift
`taR` and the width `sweepW'` are at most `w` on a right neighbourhood of `0`. -/
theorem exists_window_small {d : BandArcData} (D : SweepData d) {w : ℝ} (hw : 0 < w) :
    ∃ η : ℝ, 0 < η ∧ ∀ σ : ℝ, 0 ≤ σ → σ ≤ η →
      |taR D σ - taR D 0| ≤ w ∧ sweepW' D σ ≤ w := by
  obtain ⟨δ₁, hδ₁, hspec₁⟩ :=
    Metric.continuousAt_iff.mp (arcWin_taR_continuous D).continuousAt w hw
  obtain ⟨δ₂, hδ₂, hspec₂⟩ :=
    Metric.continuousAt_iff.mp (arcWin_sweepW'_continuous D).continuousAt w hw
  refine ⟨min δ₁ δ₂ / 2, by positivity, ?_⟩
  intro σ hσ0 hση
  have hd₁ : dist σ 0 < δ₁ := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hσ0]
    have := min_le_left δ₁ δ₂
    linarith
  have hd₂ : dist σ 0 < δ₂ := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hσ0]
    have := min_le_right δ₁ δ₂
    linarith
  have h₁ := hspec₁ hd₁
  have h₂ := hspec₂ hd₂
  rw [Real.dist_eq] at h₁ h₂
  refine ⟨le_of_lt ?_, le_of_lt ?_⟩
  · exact h₁
  · rw [sweepW'_zero, sub_zero] at h₂
    exact lt_of_le_of_lt (le_abs_self _) h₂

/-! ## 3. The short-arc tangent estimate -/

/-- **Tangents over a short interval are pairwise positively correlated.**  (Local copy of the
estimate, so that this module does not depend on a file in flux;
`Work.Drive.exists_knot_c2_bounds` is the only input.) -/
theorem arcWin_tangent_rho {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x₁ x₂ : ℝ, |x₂ - x₁| ≤ ρ →
      0 < inner ℝ (velocity r x₁) (velocity r x₂) := by
  obtain ⟨m, M, C, hm, hM, hC, hmin, hmax, hlip⟩ := exists_knot_c2_bounds (r := r) hr
  refine ⟨m ^ 2 / (2 * (M * C)), by positivity, ?_⟩
  intro x₁ x₂ hx
  have h1 : m ≤ ‖velocity r x₁‖ := hmin x₁
  have h2 : ‖velocity r x₁‖ ≤ M := hmax x₁
  have h3 : ‖velocity r x₂ - velocity r x₁‖ ≤ C * |x₂ - x₁| := by
    rw [norm_sub_rev]
    exact hlip x₁ x₂
  have hkey : inner ℝ (velocity r x₁) (velocity r x₂)
      = inner ℝ (velocity r x₁) (velocity r x₁)
        + inner ℝ (velocity r x₁) (velocity r x₂ - velocity r x₁) := by
    rw [inner_sub_right]; ring
  have hnorm : inner ℝ (velocity r x₁) (velocity r x₁) = ‖velocity r x₁‖ ^ 2 :=
    real_inner_self_eq_norm_sq _
  have hlow : ‖velocity r x₁‖ ^ 2 - ‖velocity r x₁‖ * ‖velocity r x₂ - velocity r x₁‖
      ≤ inner ℝ (velocity r x₁) (velocity r x₂) := by
    rw [hkey, hnorm]
    have hcs : -(‖velocity r x₁‖ * ‖velocity r x₂ - velocity r x₁‖)
        ≤ inner ℝ (velocity r x₁) (velocity r x₂ - velocity r x₁) := by
      have := abs_real_inner_le_norm (velocity r x₁) (velocity r x₂ - velocity r x₁)
      rw [abs_le] at this
      linarith [this.1]
    linarith
  have hb1 : m ^ 2 ≤ ‖velocity r x₁‖ ^ 2 := by
    have := pow_le_pow_left₀ (le_of_lt hm) h1 2
    simpa [pow_two] using this
  have hb2 : ‖velocity r x₁‖ * ‖velocity r x₂ - velocity r x₁‖ ≤ M * (C * |x₂ - x₁|) :=
    mul_le_mul h2 h3 (norm_nonneg _) (le_of_lt hM)
  have hb3 : M * (C * |x₂ - x₁|) ≤ M * (C * (m ^ 2 / (2 * (M * C)))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx (le_of_lt hC)) (le_of_lt hM)
  have hstep : M * (C * (m ^ 2 / (2 * (M * C)))) < m ^ 2 := by
    have hMC : (0:ℝ) < M * C := mul_pos hM hC
    have heq : M * (C * (m ^ 2 / (2 * (M * C)))) = m ^ 2 / 2 := by
      field_simp
    rw [heq]
    nlinarith [hm]
  linarith


/-- **Over a short parameter interval the tangent of a knot never makes an obtuse angle with the
chord.**  For an analytic knot there is `w₀ > 0` such that for every `a < b` with `b - a ≤ w₀` and
every `s ∈ [a,b]` one has `0 < ⟪velocity r s, r b - r a⟫`.  (The chord is the integral of the
velocity and the tangents over a short interval are pairwise positively correlated —
`Work.Drive.exists_tangent_rho`.) -/
theorem inner_velocity_chord_pos {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ ∀ a b : ℝ, 0 < b - a → b - a ≤ w₀ → ∀ s ∈ Set.Icc a b,
      0 < inner ℝ (velocity r s) (r b - r a) := by
  obtain ⟨ρ, hρ, hρspec⟩ := arcWin_tangent_rho hr
  have hvelcont : Continuous (velocity r) := by
    have h : Continuous (deriv r) :=
      hr.smooth.continuous_deriv (by simp : (1 : WithTop ℕ∞) ≤ ⊤)
    rw [show velocity r = deriv r from rfl]
    exact h
  refine ⟨ρ, hρ, ?_⟩
  intro a b hab habρ s hs
  have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt r (velocity r x) x := by
    intro x _
    exact ((hr.smooth.differentiable (by simp)) x).hasDerivAt
  have hint : IntervalIntegrable (velocity r) MeasureTheory.volume a b :=
    hvelcont.intervalIntegrable _ _
  have hchord : r b - r a = ∫ x in a..b, velocity r x :=
    (intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint).symm
  rw [hchord]
  have hcomm : inner ℝ (velocity r s) (∫ x in a..b, velocity r x)
      = ∫ x in a..b, inner ℝ (velocity r s) (velocity r x) := by
    rw [← innerSL_apply_apply (𝕜 := ℝ) (v := velocity r s)]
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm (innerSL ℝ (velocity r s)) hint]
    exact intervalIntegral.integral_congr (fun x _ => innerSL_apply_apply ℝ _ _)
  rw [hcomm]
  have hpt : ∀ x ∈ Set.Icc a b, 0 < inner ℝ (velocity r s) (velocity r x) := by
    intro x hx
    refine hρspec s x ?_
    rw [abs_sub_le_iff]
    constructor <;> linarith [hs.1, hs.2, hx.1, hx.2, habρ]
  have hcont : ContinuousOn (fun x : ℝ => inner ℝ (velocity r s) (velocity r x))
      (Set.Icc a b) :=
    ((innerSL ℝ (velocity r s)).continuous.comp hvelcont).continuousOn
  exact intervalIntegral.integral_pos (sub_pos.mp hab) hcont
    (fun x hx => (hpt x ⟨hx.1.le, hx.2⟩).le) ⟨s, hs, hpt s hs⟩

/-! ## 4. The needle's chord vector -/

/-- **The needle's chord vector is the bump-weighted average of the loops' chords.** -/
theorem chordEndB_sub_chordEndA (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    (hr : Continuous r) (δ₂ ε : ℝ) :
    chordEndB r D δ₂ ε - chordEndA r D δ₂ ε
      = ∫ v in (-1 : ℝ)..1, sweepBump v •
          (r (tbR D (ε - δ₂ * v)) - r (taR D (ε - δ₂ * v))) := by
  rw [chordEndB, chordEndA]
  rw [← intervalIntegral.integral_sub]
  · exact intervalIntegral.integral_congr (fun v _ => by rw [smul_sub])
  · exact (sweepBump_continuous.smul
      (hr.comp ((arcWin_tbR_continuous D).comp (by fun_prop)))).intervalIntegrable _ _
  · exact (sweepBump_continuous.smul
      (hr.comp ((arcWin_taR_continuous D).comp (by fun_prop)))).intervalIntegrable _ _

end Work.Drive
