import Mathlib
import Submission.Work.RTOwed.cuspChart

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RTOwed

/-!
# The ceiling of a cube in the cusp coordinates of `Work.Cusp`

`ceilH a x = √(9/4 − ∑ᵢ (xᵢ − (cubeCorner aᵢ + 1/2))²)` is the height of the truncation facet of
the cube `a` in the *cube* UHS coordinates, i.e. the hemisphere of radius `3/2` centred at the
centre `cubeCorner a + (1/2,1/2,1/2)` of the cube (`Submission/Work/RTOwed/cuspChart.lean`).
`beta y = √(9/4 − ∑ᵢ off(yᵢ)²)` is the same ceiling written in the UHS coordinates of the cusp
chapter `Work.Cusp`, as a single `ℤ³`-periodic formula through the triangle wave
`off t = 1/2 − |frac t − 1/2|`.

Since the two coordinate systems differ by the translation `h = (1/2,1/2,1/2)`
(`cuspH`), for `y + h` in the cube `a` — i.e. `y` within distance `1/2` of the corner
`cubeCorner a` in each coordinate — the offset `off (yᵢ)` is exactly the distance
`|yᵢ − cubeCorner aᵢ|`, and the two ceilings agree.
-/

/-- `off` has every integer as a period. -/
private lemma off_add_int (t : ℝ) (n : ℤ) : Work.Cusp.off (t + n) = Work.Cusp.off t := by
  simp [Work.Cusp.off, Int.fract_add_intCast]

/-- On the interval `[-1/2, 1/2]` the triangle wave `off` is the absolute value: this is the
statement that the nearest half-integer to `s` is at distance `off s`, which for `|s| ≤ 1/2` is
the half-integer `1/2` itself. -/
private lemma off_eq_abs_of_abs_le (s : ℝ) (hs : |s| ≤ 1/2) : Work.Cusp.off s = |s| := by
  have hge : -(1/2 : ℝ) ≤ s := (abs_le.mp hs).1
  have hle : s ≤ (1/2 : ℝ) := (abs_le.mp hs).2
  unfold Work.Cusp.off
  rcases lt_or_ge s 0 with h | h
  · have hf : Int.fract s = s + 1 := by
      rw [Int.fract_eq_iff]
      exact ⟨by linarith, by linarith, ⟨-1, by push_cast; ring⟩⟩
    rw [hf, show s + 1 - 1/2 = s + 1/2 by ring, abs_of_nonneg (by linarith), abs_of_neg h]
    ring
  · have hf : Int.fract s = s := Int.fract_eq_self.mpr ⟨h, by linarith⟩
    rw [hf, show s - 1/2 = -(1/2 - s) by ring, abs_neg, abs_of_nonneg (by linarith),
      abs_of_nonneg h]
    ring

/-- **The offset from an integer corner.** For `t` at distance at most `1/2` from the integer `k`,
the triangle wave `off t` is the distance `|t − k|`. -/
private lemma off_eq_abs_sub (t : ℝ) (k : ℤ) (h1 : (k : ℝ) - 1/2 ≤ t)
    (h2 : t ≤ (k : ℝ) + 1/2) : Work.Cusp.off t = |t - (k : ℝ)| := by
  have hper : Work.Cusp.off ((t - (k:ℝ)) + (k:ℝ)) = Work.Cusp.off (t - (k:ℝ)) := off_add_int _ k
  rw [show (t - (k:ℝ)) + (k:ℝ) = t by ring] at hper
  rw [hper]
  exact off_eq_abs_of_abs_le (t - (k:ℝ)) (abs_le.mpr ⟨by linarith, by linarith⟩)

theorem ceilH_eq_beta (a : Fin 48) {y : Work.RTOwed.CuspE3}
    (hy : y + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox a) :
    Work.RTOwed.ceilH a (y + Work.RTOwed.cuspH) = Work.Cusp.beta y := by
  have hy' : ∀ i : Fin 3, (Work.Cusp.cubeCorner a i : ℝ) ≤ (y + cuspH) i ∧
      (y + cuspH) i ≤ (Work.Cusp.cubeCorner a i : ℝ) + 1 := by
    simpa only [cubeBox, Set.mem_ofPred_eq] using hy
  have hadd : ∀ i : Fin 3, (y + cuspH) i = y i + 1/2 := by
    intro i; simp [cuspH]
  have hsum : (∑ i : Fin 3, ((y + cuspH) i - ((Work.Cusp.cubeCorner a i : ℝ) + 1/2))^2)
      = ∑ i : Fin 3, (Work.Cusp.off (y i))^2 := by
    apply Finset.sum_congr rfl
    intro i _
    have h := hy' i
    have hh : (y + cuspH) i = y i + 1/2 := hadd i
    rw [hh] at h ⊢
    have h1 : (Work.Cusp.cubeCorner a i : ℝ) - 1/2 ≤ y i := by linarith [h.1]
    have h2 : y i ≤ (Work.Cusp.cubeCorner a i : ℝ) + 1/2 := by linarith [h.2]
    rw [off_eq_abs_sub (y i) (Work.Cusp.cubeCorner a i) h1 h2, sq_abs]
    ring
  unfold ceilH Work.Cusp.beta
  rw [hsum]

end Work.RTOwed
