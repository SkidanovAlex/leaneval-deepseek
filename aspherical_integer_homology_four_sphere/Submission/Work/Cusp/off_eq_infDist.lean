import Mathlib
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

open Metric

/-- For `|a| ≤ 1/2` the distance of `a` to `0` is at most its distance to any integer translate
of `0`.  (The half-width `1/2` is exactly the largest `a` admitting a nearest-integer interval
that contains no other integer translate.) -/
private lemma abs_le_abs_add_int {a : ℝ} (ha : |a| ≤ 1/2) (k : ℤ) : |a| ≤ |a + k| := by
  rcases eq_or_ne k 0 with hk | hk
  · simp [hk]
  · have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      have h : (1 : ℤ) ≤ |k| := Int.one_le_abs hk
      have hc : ((1 : ℤ) : ℝ) ≤ ((|k| : ℤ) : ℝ) := by exact_mod_cast h
      simpa using hc
    have hmain : abs (|(k : ℝ)| - |a|) ≤ |(k : ℝ) + a| := by
      have h := abs_abs_sub_abs_le_abs_sub (k : ℝ) (-a)
      rwa [abs_neg, sub_neg_eq_add] at h
    have hpos : 0 ≤ |(k : ℝ)| - |a| := by linarith
    have hfin : (1 : ℝ) - |a| ≤ |a + k| := by
      have h1 : abs (|(k : ℝ)| - |a|) = |(k : ℝ)| - |a| := abs_of_nonneg hpos
      rw [h1] at hmain
      have h2 : (1 : ℝ) - |a| ≤ |(k : ℝ) + a| := by linarith
      rw [add_comm] at h2
      exact h2
    linarith

/-- **The ceiling offset is the distance to the nearest half-integer.**
`off t = ½ − |frac t − ½|` and the distance from `t` to the set `ℤ + ½` of half-integers is
`|frac t − ½|`, since the fractional part `frac t ∈ [0,1)` has nearest half-integer `½`. -/
theorem off_eq_infDist (t : ℝ) :
    off t = 1/2 - Metric.infDist t (Set.range (fun n : ℤ => (n : ℝ) + 1/2)) := by
  rw [off, sub_right_inj]
  have hS : (Set.range (fun n : ℤ => (n : ℝ) + 1/2)).Nonempty := ⟨1/2, ⟨0, by norm_num⟩⟩
  apply le_antisymm
  · rw [Metric.le_infDist hS]
    intro y hy
    rcases hy with ⟨n, rfl⟩
    rw [Real.dist_eq]
    have hfract : t - ((n : ℝ) + 1/2) = (Int.fract t - 1/2) + ((⌊t⌋ - n : ℤ) : ℝ) := by
      have hfl : (⌊t⌋ : ℝ) = t - Int.fract t := by linarith [Int.self_sub_floor t]
      push_cast
      rw [hfl]
      ring
    rw [hfract]
    exact abs_le_abs_add_int (by
      rw [abs_le]
      exact ⟨by linarith [Int.fract_nonneg t], by linarith [Int.fract_lt_one t]⟩) _
  · calc Metric.infDist t (Set.range (fun n : ℤ => (n : ℝ) + 1/2))
        ≤ dist t (((⌊t⌋ : ℤ) : ℝ) + 1/2) := Metric.infDist_le_dist_of_mem ⟨⌊t⌋, rfl⟩
      _ = |Int.fract t - 1/2| := by
            rw [Real.dist_eq]
            congr 1
            linarith [Int.self_sub_floor t]

end Work.Cusp
