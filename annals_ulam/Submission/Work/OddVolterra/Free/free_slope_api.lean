import Mathlib
import Submission.Work.OddCurve.Free
import Submission.Work.OddVolterra.Free.Defs

/-!
# The slope API of the free-tip envelope curve

`Work.OddCurve.Free.IsEnvelopeCurveFree` drops the two tip normalisations of
`Work.OddEnvelope.IsEnvelopeCurve` (`x s → 1`, `y s → 1` as `s → 0⁺`) and keeps only the
existence of *some* positive limit.  The price is that `Work.OddEnvelope.IsChordCurve.lt_one`
(and with it the surjectivity of the chord curve onto `(0,1)`) is no longer available, so the
inverse-slope machinery has to be rebuilt from scratch.

This file provides exactly that.  Its content is:

* `pos_x`, `pos_y` : the two curves are positive on `(0,∞)` (they are strictly decreasing and
  equal to `profileX` on the tail `[1-τ, ∞)`);
* `exists_slope_y`, `exists_slope_x` : if `0 < t ≤ y s` then there is a slope `σ ≥ s` with
  `y σ = t` (the realising slope is *not* beyond the tip: `y ρ = profileX ρ < t` for a
  sufficiently large explicit `ρ`, then the intermediate value theorem on `[s, ρ]`);
* `slopeRight_eq_of`, `slopeLeft_eq_of` : uniqueness of the realising slope, from the
  injectivity of the two strictly antitone curves on `(0,∞)`.
-/

namespace Work.OddCurve.Free

noncomputable section

open Set Filter
open scoped Topology ContDiff

variable {h x y : ℝ → ℝ}

/-- The right chord-endpoint curve of a free-tip envelope curve is strictly decreasing. -/
lemma IsEnvelopeCurveFree.strictAntiOn_y (H : IsEnvelopeCurveFree h x y) :
    StrictAntiOn y (Set.Ioi 0) :=
  strictAntiOn_of_deriv_neg (convex_Ioi 0) H.smooth_y.continuousOn (by
    intro s hs
    rw [interior_Ioi] at hs
    exact H.y_deriv_neg s hs)

/-- The left chord-endpoint curve of a free-tip envelope curve is strictly decreasing. -/
lemma IsEnvelopeCurveFree.strictAntiOn_x (H : IsEnvelopeCurveFree h x y) :
    StrictAntiOn x (Set.Ioi 0) :=
  strictAntiOn_of_deriv_neg (convex_Ioi 0) H.smooth_x.continuousOn (by
    intro s hs
    rw [interior_Ioi] at hs
    exact H.x_deriv_neg s hs)

/-- Beyond the perturbation window the bump vanishes. -/
lemma IsEnvelopeCurveFree.h_eq_zero_of_gt (H : IsEnvelopeCurveFree h x y) {s : ℝ}
    (hs : 1 - Work.OddCurve.tau < s) : h s = 0 := by
  by_contra hne
  exact absurd (H.h_support (Function.mem_support.mpr hne)).2 (not_le.mpr hs)

/-- The right chord-endpoint curve is positive on `(0,∞)`. -/
theorem IsEnvelopeCurveFree.pos_y (H : IsEnvelopeCurveFree h x y) {s : ℝ} (hs : 0 < s) :
    0 < y s := by
  have hτ : (0 : ℝ) < 1 - Work.OddCurve.tau := by norm_num [Work.OddCurve.tau]
  rcases lt_or_ge s (1 - Work.OddCurve.tau) with hlt | hge
  · have h1 : y (1 - Work.OddCurve.tau) < y s := H.strictAntiOn_y hs hτ hlt
    rw [H.y_tail (1 - Work.OddCurve.tau) le_rfl] at h1
    exact lt_trans (Work.OddEnvelope.profileX_pos _) h1
  · rw [H.y_tail s hge]
    exact Work.OddEnvelope.profileX_pos s

/-- The left chord-endpoint curve is positive on `(0,∞)`. -/
theorem IsEnvelopeCurveFree.pos_x (H : IsEnvelopeCurveFree h x y) {s : ℝ} (hs : 0 < s) :
    0 < x s := by
  have hτ : (0 : ℝ) < 1 - Work.OddCurve.tau := by norm_num [Work.OddCurve.tau]
  rcases lt_or_ge s (1 - Work.OddCurve.tau) with hlt | hge
  · have h1 : x (1 - Work.OddCurve.tau) < x s := H.strictAntiOn_x hs hτ hlt
    rw [H.x_tail (1 - Work.OddCurve.tau) le_rfl] at h1
    exact lt_trans (Work.OddEnvelope.profileX_pos _) h1
  · rw [H.x_tail s hge]
    exact Work.OddEnvelope.profileX_pos s

/-- The explicit large slope used to bracket a point of the body from above. -/
theorem IsEnvelopeCurveFree.lt_profileX_of_lt_div {t ρ : ℝ} (ht : 0 < t)
    (h : 1 / t < ρ) : Work.OddEnvelope.profileX ρ < t := by
  have hρpos : 0 < ρ := lt_trans (by positivity) h
  have hsQ : (0 : ℝ) < Real.sqrt (1 + ρ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hρlt1 : 1 < t * ρ := by
    have h' : 1 < ρ * t := (div_lt_iff₀ ht).mp h
    linarith
  have hlt : ρ < Real.sqrt (1 + ρ ^ 2) := by
    have := (Real.lt_sqrt (x := ρ) (y := 1 + ρ ^ 2) hρpos.le).mpr (by nlinarith [sq_nonneg ρ])
    simpa [add_comm] using this
  rw [Work.OddEnvelope.profileX, div_lt_iff₀ hsQ]
  calc (1 : ℝ) < t * ρ := hρlt1
    _ < t * Real.sqrt (1 + ρ ^ 2) := mul_lt_mul_of_pos_left hlt ht

/-- **The realising slope of a point of the right branch.**  If `0 < t ≤ y s` then some slope
`σ ≥ s` realises `t`; it is the unique such slope (see `slopeRight_eq_of`). -/
theorem IsEnvelopeCurveFree.exists_slope_y (H : IsEnvelopeCurveFree h x y) {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hts : t ≤ y s) : ∃ σ : ℝ, s ≤ σ ∧ 0 < σ ∧ y σ = t := by
  set ρ : ℝ := max s (1 - Work.OddCurve.tau) + 1 / t + 1 with hρdef
  have hρgt : max s (1 - Work.OddCurve.tau) < ρ := by
    have h2 : (0 : ℝ) < 1 / t := by positivity
    rw [hρdef]; linarith
  have hρs : s < ρ := lt_of_le_of_lt (le_max_left _ _) hρgt
  have hρτ : 1 - Work.OddCurve.tau ≤ ρ :=
    le_of_lt (lt_of_le_of_lt (le_max_right _ _) hρgt)
  have hrec : 1 / t < ρ := by
    rw [hρdef]
    have h2 : (0 : ℝ) < 1 / t := by positivity
    have h3 : (0 : ℝ) ≤ max s (1 - Work.OddCurve.tau) := le_trans hs.le (le_max_left _ _)
    linarith
  have hyρ : y ρ = Work.OddEnvelope.profileX ρ := H.y_tail ρ hρτ
  have hpxρ : Work.OddEnvelope.profileX ρ < t :=
    IsEnvelopeCurveFree.lt_profileX_of_lt_div ht hrec
  have hyρlt : y ρ < t := by rw [hyρ]; exact hpxρ
  have hcont : ContinuousOn (fun σ : ℝ => -y σ) (Set.Icc s ρ) :=
    ((H.smooth_y.continuousOn).mono (fun u hu => lt_of_lt_of_le hs hu.1)).neg
  have hmem : -t ∈ Set.Icc ((fun σ : ℝ => -y σ) s) ((fun σ : ℝ => -y σ) ρ) :=
    ⟨by simpa using neg_le_neg hts, by simpa using neg_le_neg hyρlt.le⟩
  obtain ⟨σ, hσ, hσeq⟩ := intermediate_value_Icc hρs.le hcont hmem
  exact ⟨σ, hσ.1, lt_of_lt_of_le hs hσ.1, by simpa using hσeq⟩

/-- **The realising slope of a point of the left branch.**  Same statement for `x`. -/
theorem IsEnvelopeCurveFree.exists_slope_x (H : IsEnvelopeCurveFree h x y) {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hts : t ≤ x s) : ∃ σ : ℝ, s ≤ σ ∧ 0 < σ ∧ x σ = t := by
  set ρ : ℝ := max s (1 - Work.OddCurve.tau) + 1 / t + 1 with hρdef
  have hρgt : max s (1 - Work.OddCurve.tau) < ρ := by
    have h2 : (0 : ℝ) < 1 / t := by positivity
    rw [hρdef]; linarith
  have hρs : s < ρ := lt_of_le_of_lt (le_max_left _ _) hρgt
  have hρτ : 1 - Work.OddCurve.tau ≤ ρ :=
    le_of_lt (lt_of_le_of_lt (le_max_right _ _) hρgt)
  have hrec : 1 / t < ρ := by
    rw [hρdef]
    have h2 : (0 : ℝ) < 1 / t := by positivity
    have h3 : (0 : ℝ) ≤ max s (1 - Work.OddCurve.tau) := le_trans hs.le (le_max_left _ _)
    linarith
  have hxρ : x ρ = Work.OddEnvelope.profileX ρ := H.x_tail ρ hρτ
  have hpxρ : Work.OddEnvelope.profileX ρ < t :=
    IsEnvelopeCurveFree.lt_profileX_of_lt_div ht hrec
  have hxρlt : x ρ < t := by rw [hxρ]; exact hpxρ
  have hcont : ContinuousOn (fun σ : ℝ => -x σ) (Set.Icc s ρ) :=
    ((H.smooth_x.continuousOn).mono (fun u hu => lt_of_lt_of_le hs hu.1)).neg
  have hmem : -t ∈ Set.Icc ((fun σ : ℝ => -x σ) s) ((fun σ : ℝ => -x σ) ρ) :=
    ⟨by simpa using neg_le_neg hts, by simpa using neg_le_neg hxρlt.le⟩
  obtain ⟨σ, hσ, hσeq⟩ := intermediate_value_Icc hρs.le hcont hmem
  exact ⟨σ, hσ.1, lt_of_lt_of_le hs hσ.1, by simpa using hσeq⟩

/-- **Uniqueness of the realising slope** (right branch): the inverse slope of `y` at `t` is the
unique slope `σ > 0` with `y σ = t`. -/
theorem IsEnvelopeCurveFree.slopeRight_eq_of (H : IsEnvelopeCurveFree h x y) {σ t : ℝ}
    (hσ : 0 < σ) (h : y σ = t) : Work.OddEnvelope.slopeRight y t = σ := by
  have hmem := Function.invFunOn_pos (s := Set.Ioi (0 : ℝ)) ⟨σ, hσ, h⟩
  exact H.strictAntiOn_y.injOn hmem.1 hσ (by rw [hmem.2, h])

/-- **Uniqueness of the realising slope** (left branch): the inverse slope of `x` at `t` is the
unique slope `σ > 0` with `x σ = -t`. -/
theorem IsEnvelopeCurveFree.slopeLeft_eq_of (H : IsEnvelopeCurveFree h x y) {σ t : ℝ}
    (hσ : 0 < σ) (h : x σ = -t) : Work.OddEnvelope.slopeLeft x t = σ := by
  have hmem := Function.invFunOn_pos (s := Set.Ioi (0 : ℝ)) ⟨σ, hσ, by simpa using h⟩
  exact H.strictAntiOn_x.injOn hmem.1 hσ (by rw [hmem.2]; exact h.symm)

end

end Work.OddCurve.Free
