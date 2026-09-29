import Mathlib
import Submission.Work.TMC16Core.Basic.nnDist
import Submission.Work.TMC16Core.Trig.gridW

/-!
# `q · nn (s + j/q) = gridW q (q·s) j`

With `0 < q`, `0 ≤ s < 1`, `j < q`, put `y = j + q·s ∈ [0, 2q)`.  Then
`s + j/q = y/q`, and `nn (y/q)` is the distance from `y/q` to the nearest integer `r`,
so `q · nn (y/q) = |y - q·r|`.  Because `y/q ∈ [0,2)` the nearest integer `r` lies in
`{0,1,2}`, and since `r` is at least as close to `y/q` as `0`, `1`, `2`, this is exactly
`min { |y|, |y - q|, |2q - y| } = gridW q (q·s) j`.
-/

noncomputable section

namespace Work.TMC16Core.Trig

open Work.TMC16Core.Basic

theorem q_mul_nn_eq_gridW {q : ℕ} (hq : 0 < q) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) {j : ℕ} (hj : j < q) :
    (q : ℝ) * Work.TMC16Core.Basic.nn (s + (j : ℝ) / (q : ℝ)) =
      Work.TMC16Core.Trig.gridW q ((q : ℝ) * s) j := by
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hqne : (q:ℝ) ≠ 0 := ne_of_gt hqR
  set y : ℝ := (j:ℝ) + (q:ℝ)*s with hydef
  have hy0 : 0 ≤ y := by rw [hydef]; positivity
  have hyq : y < 2*(q:ℝ) := by
    have hj' : (j:ℝ) ≤ (q:ℝ) - 1 := by
      have : j + 1 ≤ q := by omega
      have : (j:ℝ) + 1 ≤ (q:ℝ) := by exact_mod_cast this
      linarith
    have hs' : (q:ℝ)*s < (q:ℝ) := by nlinarith [hqR, hs1]
    rw [hydef]; linarith
  have harg : s + (j:ℝ)/(q:ℝ) = y/(q:ℝ) := by
    rw [hydef]; field_simp; ring
  rw [harg]
  set r : ℤ := round (y/(q:ℝ)) with hrdef
  -- `q · |z| = |q · z|` for `q ≥ 0`.
  have habsq : ∀ z : ℝ, (q:ℝ) * |z| = |(q:ℝ) * z| := by
    intro z
    rw [abs_mul, abs_of_nonneg (le_of_lt hqR)]
  -- `q · |y/q - m| = |y - q·m|`.
  have habs : ∀ m : ℤ, (q:ℝ) * |y/(q:ℝ) - (m:ℝ)| = |y - (q:ℝ)*(m:ℝ)| := by
    intro m
    rw [habsq, mul_sub, mul_div_cancel₀ y hqne]
  -- the central identity `q · nn (y/q) = |y - q·r|`
  have hkey : (q:ℝ) * nn (y/(q:ℝ)) = |y - (q:ℝ)*(r:ℝ)| := by
    have h1 : nn (y/(q:ℝ)) = |y/(q:ℝ) - (r:ℝ)| := by rw [nn, hrdef]
    rw [h1, habsq, mul_sub, mul_div_cancel₀ y hqne]
  rw [hkey]
  -- `r`, the nearest integer, is at least as close as `0`, `1`, `2`.
  have hmul : ∀ m : ℤ, |y - (q:ℝ)*(r:ℝ)| ≤ |y - (q:ℝ)*(m:ℝ)| := by
    intro m
    have h1 : |y/(q:ℝ) - (r:ℝ)| ≤ |y/(q:ℝ) - (m:ℝ)| := by
      rw [hrdef]; exact round_le (y/(q:ℝ)) m
    have h2 : (q:ℝ) * |y/(q:ℝ) - (r:ℝ)| ≤ (q:ℝ) * |y/(q:ℝ) - (m:ℝ)| :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt hqR)
    rw [habs r, habs m] at h2
    exact h2
  have hgu0 : |y - (q:ℝ)*(r:ℝ)| ≤ y := by
    have h := hmul 0
    simpa [abs_of_nonneg hy0] using h
  have hgu1 : |y - (q:ℝ)*(r:ℝ)| ≤ |y - (q:ℝ)| := by
    have h := hmul 1
    simpa using h
  have hgu2 : |y - (q:ℝ)*(r:ℝ)| ≤ 2*(q:ℝ) - y := by
    have h := hmul 2
    have h2 : (0:ℝ) ≤ 2*(q:ℝ) - y := by linarith [hyq.le]
    have hh : |y - (q:ℝ)*((2:ℤ):ℝ)| = 2*(q:ℝ) - y := by
      have : y - (q:ℝ)*((2:ℤ):ℝ) = -(2*(q:ℝ) - y) := by push_cast; ring
      rw [this, abs_neg, abs_of_nonneg h2]
    rw [hh] at h
    exact h
  have hgrid : Work.TMC16Core.Trig.gridW q ((q:ℝ)*s) j =
      min (min y |y - (q:ℝ)|) (2*(q:ℝ) - y) := by
    unfold Work.TMC16Core.Trig.gridW
    rw [hydef]
    congr 1
    ring
  rw [hgrid]
  refine le_antisymm ?_ ?_
  · exact le_min (le_min hgu0 hgu1) hgu2
  · -- `r ∈ {0,1,2}`, so `|y - q·r|` is one of the three values in the `min`.
    have hr012 : r = 0 ∨ r = 1 ∨ r = 2 := by
      have hb := abs_sub_round (y/(q:ℝ))
      rw [← hrdef] at hb
      have hyq2 : y/(q:ℝ) < 2 := by
        rw [div_lt_iff₀ hqR]; linarith
      have hle := abs_le.mp hb
      have hlow : ((-1:ℤ):ℝ) < (r:ℝ) := by
        have h1 : (y/(q:ℝ) - 1/2) ≤ (r:ℝ) := by linarith [hle.2]
        have h2 : (-1:ℝ) < (y/(q:ℝ) - 1/2) := by
          have : 0 ≤ y/(q:ℝ) := div_nonneg hy0 (le_of_lt hqR)
          linarith
        push_cast
        linarith
      have hhigh : (r:ℝ) < (3:ℝ) := by
        have h1 : (r:ℝ) ≤ y/(q:ℝ) + 1/2 := by linarith [hle.1]
        linarith
      have hlow' : (-1:ℤ) < r := by exact_mod_cast hlow
      have hhigh' : r < 3 := by exact_mod_cast hhigh
      omega
    rcases hr012 with h | h | h
    · rw [h]
      simp only [Int.cast_zero, mul_zero, sub_zero, abs_of_nonneg hy0]
      exact le_trans (min_le_left _ _) (min_le_left _ _)
    · rw [h]
      simp only [Int.cast_one, mul_one]
      exact le_trans (min_le_left _ _) (min_le_right _ _)
    · rw [h]
      have h2 : (0:ℝ) ≤ 2*(q:ℝ) - y := by linarith [hyq.le]
      have hh : |y - (q:ℝ)*((2:ℤ):ℝ)| = 2*(q:ℝ) - y := by
        have : y - (q:ℝ)*((2:ℤ):ℝ) = -(2*(q:ℝ) - y) := by push_cast; ring
        rw [this, abs_neg, abs_of_nonneg h2]
      rw [hh]
      exact min_le_right _ _

end Work.TMC16Core.Trig
