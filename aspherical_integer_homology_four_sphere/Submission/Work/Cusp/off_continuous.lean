import Mathlib
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Continuity of the ceiling height offset `off`

`off t = 1/2 - |fract t - 1/2|` is the distance of `t` to the nearest half-integer offset, i.e. the
`i`-th coordinate offset of a point from the centre of the unit cube it lies in (`Basic.off`).  It is
a triangular wave of period `1` and it is continuous, even though `Int.fract` is not: the two jumps
of `Int.fract` at the integers occur exactly at the zeros of the wave.

The proof identifies `off` with the distance function to the integers,

`off t = infDist t (range (fun n : ℤ => (n : ℝ)))`

and uses `Metric.continuous_infDist_pt`.  The key algebraic identity is
`1/2 - |x - 1/2| = min x (1 - x)`.
-/

noncomputable section

namespace Work.Cusp

open scoped Real

/-- `1/2 - |x - 1/2|` is `min x (1 - x)`: the "tent" function of the fractional part. -/
lemma half_sub_abs_sub_half (x : ℝ) : 1/2 - |x - 1/2| = min x (1 - x) := by
  rcases le_total x (1/2) with h | h
  · rw [min_eq_left (by linarith), abs_of_nonpos (by linarith)]
    ring
  · rw [min_eq_right (by linarith), abs_of_nonneg (by linarith)]
    ring

/-- **`off` is `min` of the two pieces of the fractional part.** -/
lemma off_eq_min (t : ℝ) : off t = min (Int.fract t) (1 - Int.fract t) := by
  rw [off, half_sub_abs_sub_half]

/-- **`off` is the distance of `t` to the nearest integer.** -/
lemma off_eq_infDist_int (t : ℝ) :
    off t = Metric.infDist t (Set.range (fun n : ℤ => (n : ℝ))) := by
  rw [off_eq_min]
  have hne : (Set.range (fun n : ℤ => (n : ℝ))).Nonempty := ⟨0, ⟨0, by simp⟩⟩
  refine le_antisymm ?_ ?_
  · -- `min (fract t) (1 - fract t) ≤ infDist t ℤ`: every integer is at distance at least `min` from
    -- `t`, so it suffices to test the two neighbours `⌊t⌋` and `⌊t⌋ + 1`.
    rw [Metric.le_infDist hne]
    rintro y ⟨n, rfl⟩
    rw [Real.dist_eq]
    rcases lt_trichotomy (n : ℝ) t with h | h | h
    · -- `n < t`: `|t - n| = t - n ≥ t - ⌊t⌋ = fract t`
      rw [abs_of_nonneg (by linarith)]
      refine le_trans (min_le_left _ _) ?_
      have hle : ((n : ℤ) : ℝ) ≤ (⌊t⌋ : ℝ) := by
        exact_mod_cast (Int.le_floor.mpr (le_of_lt h))
      rw [Int.fract]; linarith
    · -- `n = t`: `fract t = 0` and the distance is `0`
      rw [← h, sub_self, abs_zero, Int.fract_intCast]
      norm_num
    · -- `t < n`: `n ≥ ⌊t⌋ + 1`, so `|t - n| = n - t ≥ ⌊t⌋ + 1 - t = 1 - fract t`
      rw [abs_of_neg (by linarith)]
      refine le_trans (min_le_right _ _) ?_
      have hlt : ⌊t⌋ < n := Int.floor_lt.mpr h
      have hle : (⌊t⌋ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast Int.lt_iff_add_one_le.mp hlt
      rw [Int.fract]; linarith
  · -- `infDist t ℤ ≤ min (fract t) (1 - fract t)`: `⌊t⌋` and `⌊t⌋ + 1` are integers at those
    -- distances from `t`.
    refine le_min ?_ ?_
    · have h := Metric.infDist_le_dist_of_mem (x := t) (s := Set.range (fun n : ℤ => (n : ℝ)))
        (y := (⌊t⌋ : ℝ)) ⟨⌊t⌋, rfl⟩
      rw [Real.dist_eq, abs_of_nonneg (by linarith [Int.floor_le t])] at h
      exact h
    · have h := Metric.infDist_le_dist_of_mem (x := t) (s := Set.range (fun n : ℤ => (n : ℝ)))
        (y := (⌊t⌋ : ℝ) + 1) ⟨⌊t⌋ + 1, by push_cast; ring⟩
      rw [Real.dist_eq, abs_of_nonpos (by linarith [Int.lt_floor_add_one t])] at h
      have h2 : (1 : ℝ) - Int.fract t = -(t - ((⌊t⌋ : ℝ) + 1)) := by
        rw [Int.fract]; ring
      rw [h2]; exact h

/-- **`off` is continuous**: it is the distance to the (closed, discrete) set of integers. -/
theorem off_continuous : Continuous off := by
  have h : off = fun t : ℝ => Metric.infDist t (Set.range (fun n : ℤ => (n : ℝ))) :=
    funext off_eq_infDist_int
  rw [h]
  exact Metric.continuous_infDist_pt _

end Work.Cusp
