/-
# Vocabulary for the volume bound of FI Lemma 7.1

The region (7.4) of *FI* §7 is contained in the "square annulus" set
`S = {|t₁² − t₂²| ≤ 2√M} ∩ {t₁² + t₂² ≤ C}` with `C = 4√M/√(1−γ²)`.  Fubini reduces the
volume of `S` to `∫ u, (length of the u-section)`, and the section
`{t : |u² − t²| ≤ 2√M, u² + t² ≤ C}` is the set `{t : a(u) ≤ t² ≤ b(u)}` with
`a(u) = max 0 (u² − 2√M)`, `b(u) = min (u² + 2√M) (C − u²)`, of length `2(√b − √a)`.

This module fixes the elementary dominating function `volBound M C : ℝ → ℝ` for `2(√b(u) − √a(u))`:

* `√6 · r` for `|u| ≤ min r T`,
* `4√2 √M / |u|` for `min r T < |u| < T`,
* `0` for `|u| ≥ T`,

where `r = √(4√M)` and `T = √((C + 2√M)/2)`; `T` is the threshold beyond which the section is
empty, and `r` the threshold `u² = 4√M` of the two elementary bounds of Lemma 7.1's proof.  The
integral of `volBound` is then computed in `Submission.Work.FIArea2.lemma_7_1_volume`.
-/
import Mathlib
import Submission.Work.FIArea2.biquadratic_ellipse_bounds

set_option autoImplicit false

namespace Work.FIArea2

noncomputable section

open MeasureTheory

/-- `r = √(4√M)`: the threshold `u² = 4√M` of the two elementary section bounds. -/
def volR (M : ℝ) : ℝ := Real.sqrt (4 * Real.sqrt M)

/-- `T = √((C + 2√M)/2)`: beyond `|u| = T` the `u`-section of the region is empty. -/
def volT (M C : ℝ) : ℝ := Real.sqrt ((C + 2 * Real.sqrt M) / 2)

/-- `s = min r T`. -/
def volS (M C : ℝ) : ℝ := min (volR M) (volT M C)

/-- A dominating function for the length `2(√b(u) − √a(u))` of the `u`-section of
`{|t₁² − t₂²| ≤ 2√M} ∩ {t₁² + t₂² ≤ C}`. -/
def volBound (M C : ℝ) : ℝ → ℝ :=
  (Set.Icc (-(volR M)) (volR M)).indicator (fun _ => Real.sqrt 6 * volR M)
    + (Set.Ioo (-(volT M C)) (-(volS M C)) ∪ Set.Ioo (volS M C) (volT M C)).indicator
        (fun x => 4 * Real.sqrt 2 * Real.sqrt M / |x|)

lemma volR_nonneg (M : ℝ) : 0 ≤ volR M := Real.sqrt_nonneg _

lemma volR_sq (M : ℝ) (hM : 0 ≤ M) : volR M ^ 2 = 4 * Real.sqrt M :=
  Real.sq_sqrt (by positivity)

lemma volR_pos (M : ℝ) (hM : 0 < M) : 0 < volR M :=
  Real.sqrt_pos.mpr (by positivity)

lemma volT_nonneg (M C : ℝ) : 0 ≤ volT M C := Real.sqrt_nonneg _

lemma volT_sq (M C : ℝ) (h : 0 ≤ (C + 2 * Real.sqrt M) / 2) : volT M C ^ 2 = (C + 2 * Real.sqrt M) / 2 :=
  Real.sq_sqrt h

lemma volT_pos (M C : ℝ) (h : 0 < (C + 2 * Real.sqrt M) / 2) : 0 < volT M C :=
  Real.sqrt_pos.mpr h

lemma volS_eq (M C : ℝ) : volS M C = min (volR M) (volT M C) := rfl

lemma volS_le_volR (M C : ℝ) : volS M C ≤ volR M := min_le_left _ _

lemma volS_le_volT (M C : ℝ) : volS M C ≤ volT M C := min_le_right _ _

lemma volS_eq_left_or_right (M C : ℝ) : volS M C = volR M ∨ volS M C = volT M C :=
  min_choice _ _

lemma volS_nonneg (M C : ℝ) : 0 ≤ volS M C := le_min (volR_nonneg M) (volT_nonneg M C)

lemma volS_pos (M C : ℝ) (hM : 0 < M) (hC : 0 < (C + 2 * Real.sqrt M) / 2) : 0 < volS M C :=
  lt_min (volR_pos M hM) (volT_pos M C hC)

lemma volBound_nonneg (M C x : ℝ) : 0 ≤ volBound M C x := by
  simp only [volBound, Pi.add_apply]
  apply add_nonneg
  · by_cases h : x ∈ Set.Icc (-(volR M)) (volR M)
    · simp only [Set.indicator_of_mem h]
      have : 0 ≤ Real.sqrt 6 * volR M := mul_nonneg (Real.sqrt_nonneg 6) (volR_nonneg M)
      exact this
    · simp only [Set.indicator_of_notMem h, le_refl]
  · by_cases h : x ∈ Set.Ioo (-(volT M C)) (-(volS M C)) ∪ Set.Ioo (volS M C) (volT M C)
    · simp only [Set.indicator_of_mem h]
      positivity
    · simp only [Set.indicator_of_notMem h, le_refl]

end

end Work.FIArea2
