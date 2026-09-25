import Mathlib
import Submission.Work.RHContract.A.regionII.abnum

/-!
# `sqL n ≤ √n` for `173 ≤ n ≤ 501`

`sqL` (defined in `Work.RHContract.A.RegionII`) is the piecewise-linear chord lower bound
for `√·` used in the Region II numeric check: on `[173,273]` it is the chord joining
`(173, sq173l)` to `(273, sq273l)`, and on `[274,501]` the chord joining `(274, sq274l)` to
`(501, sq501l)`.

The proof is the concavity of `√` on `[0,∞)`: for `a ≤ n ≤ b` the graph of `√` lies above
the chord through `(a, √a)` and `(b, √b)` (`Real.strictConcaveOn_sqrt`), while each chord
endpoint value `sq…l` is below the corresponding `√` by a direct squaring estimate. Hence
`sqL n`, the chord through the slightly lower endpoints, is below the chord through
`(a, √a)`, `(b, √b)`, which is below `√n`.
-/

namespace Work.RHContract.A.regionII

open Work.RHContract.A.RegionII

/-- Concavity of `√` in chord form: for `0 ≤ a < b` and `a ≤ n ≤ b` the chord through
`(a, √a)` and `(b, √b)` lies below the graph of `√` at `n`. -/
theorem sqrt_chord_le {a b n : ℝ} (ha : 0 ≤ a) (hab : a < b) (han : a ≤ n) (hnb : n ≤ b) :
    (b - n) * Real.sqrt a + (n - a) * Real.sqrt b ≤ (b - a) * Real.sqrt n := by
  have hb : 0 ≤ b := le_of_lt (lt_of_le_of_lt ha hab)
  have hba : 0 < b - a := sub_pos.mpr hab
  have hf := Real.strictConcaveOn_sqrt.concaveOn
  set ca := (b - n) / (b - a) with hca
  set cb := (n - a) / (b - a) with hcb
  have hcan : 0 ≤ ca := div_nonneg (sub_nonneg.mpr hnb) hba.le
  have hcbn : 0 ≤ cb := div_nonneg (sub_nonneg.mpr han) hba.le
  have hsum : ca + cb = 1 := by
    rw [hca, hcb]; field_simp; ring
  have hpoint : ca * a + cb * b = n := by
    rw [hca, hcb]; field_simp; ring
  have key := hf.2 (Set.mem_Ici.mpr ha) (Set.mem_Ici.mpr hb) hcan hcbn hsum
  simp only [smul_eq_mul] at key
  rw [hpoint] at key
  have hmul := mul_le_mul_of_nonneg_left key hba.le
  calc (b - n) * Real.sqrt a + (n - a) * Real.sqrt b
      = (b - a) * (ca * Real.sqrt a + cb * Real.sqrt b) := by
        rw [hca, hcb]; field_simp
    _ ≤ (b - a) * Real.sqrt n := hmul

theorem sqL_le_sqrt (n : ℕ) (h1 : 173 ≤ n) (h2 : n ≤ 501) :
    Work.RHContract.A.RegionII.sqL n ≤ Real.sqrt (n : ℝ) := by
  have h173 : sq173l ≤ Real.sqrt 173 := by
    rw [sq173l, Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have h273 : sq273l ≤ Real.sqrt 273 := by
    rw [sq273l, Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have h274 : sq274l ≤ Real.sqrt 274 := by
    rw [sq274l, Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have h501 : sq501l ≤ Real.sqrt 501 := by
    rw [sq501l, Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  by_cases h : n ≤ 273
  · -- chord on `[173, 273]`
    have hNlo : (173:ℝ) ≤ (n:ℝ) := by exact_mod_cast h1
    have hNhi : (n:ℝ) ≤ 273 := by exact_mod_cast h
    have key := sqrt_chord_le (a := (173:ℝ)) (b := (273:ℝ)) (n := (n:ℝ))
        (by norm_num) (by norm_num) hNlo hNhi
    have hsq : sqL n = ((273 - (n:ℝ)) * sq173l + ((n:ℝ) - 173) * sq273l) / 100 := by
      rw [sqL, if_pos h]; ring
    rw [hsq]
    have h1' : (273 - (n:ℝ)) * sq173l ≤ (273 - (n:ℝ)) * Real.sqrt 173 :=
      mul_le_mul_of_nonneg_left h173 (by linarith)
    have h2' : ((n:ℝ) - 173) * sq273l ≤ ((n:ℝ) - 173) * Real.sqrt 273 :=
      mul_le_mul_of_nonneg_left h273 (by linarith)
    have hsum : (273 - (n:ℝ)) * sq173l + ((n:ℝ) - 173) * sq273l ≤
        100 * Real.sqrt (n:ℝ) := by
      have := add_le_add h1' h2'
      linarith [key]
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 100)]
    nlinarith [hsum]
  · -- chord on `[274, 501]`
    have hn274 : 274 ≤ n := by omega
    have hNlo : (274:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn274
    have hNhi : (n:ℝ) ≤ 501 := by exact_mod_cast h2
    have key := sqrt_chord_le (a := (274:ℝ)) (b := (501:ℝ)) (n := (n:ℝ))
        (by norm_num) (by norm_num) hNlo hNhi
    have hsq : sqL n = ((501 - (n:ℝ)) * sq274l + ((n:ℝ) - 274) * sq501l) / 227 := by
      rw [sqL, if_neg h]; ring
    rw [hsq]
    have h1' : (501 - (n:ℝ)) * sq274l ≤ (501 - (n:ℝ)) * Real.sqrt 274 :=
      mul_le_mul_of_nonneg_left h274 (by linarith)
    have h2' : ((n:ℝ) - 274) * sq501l ≤ ((n:ℝ) - 274) * Real.sqrt 501 :=
      mul_le_mul_of_nonneg_left h501 (by linarith)
    have hsum : (501 - (n:ℝ)) * sq274l + ((n:ℝ) - 274) * sq501l ≤
        227 * Real.sqrt (n:ℝ) := by
      have := add_le_add h1' h2'
      linarith [key]
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 227)]
    nlinarith [hsum]

end Work.RHContract.A.regionII
