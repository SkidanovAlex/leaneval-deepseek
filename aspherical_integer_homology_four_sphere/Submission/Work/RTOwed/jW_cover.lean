/-
# The finite cover of the `w`-unit square by the section boxes `jWSet`

The junction charts of `M̂` are indexed by boxes `Work.RTOwed.jWSet v c` of the `w`-coordinates
(`Submission/Work/RTOwed/jCollarAux.lean`), and the finiteness of the junction family rests on
covering the unit square `[0,1]²` of the `w`-plane by finitely many of them.  This file supplies
that cover.

The claim is independent of the cusp `v`.  Indeed, by definition
`jWSet v c = {w | invY v w ∈ jWBox c}` with `jWBox c = {y | ∀ j, |y j − c j| < 1/4}`, and
`invY v` inverts `wOf v` (`Work.Cusp.invY_wOf`), so

  `wOf v w ∈ jWSet v c ↔ w ∈ jWBox c ↔ ∀ j, |w j − c j| < 1/4`.

Thus it suffices to cover `[0,1]²` by boxes of half-width `1/4` centred at the twenty-five grid
points `{0, 1/4, 1/2, 3/4, 1}²`: every `t ∈ [0,1]` is within `1/8` of a grid point, hence within
`1/4` of one, coordinate by coordinate.
-/
import Mathlib
import Submission.Work.RTOwed.jCollarAux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Work.Cusp

namespace Work.RTOwed

/-- **The grid of centres of the `w`-section boxes**: the five points `0, 1/4, 1/2, 3/4, 1` of the
unit interval. -/
def jWGrid : Finset ℝ := {0, 1/4, 1/2, 3/4, 1}

/-- **The finite family of centres of the `w`-section boxes**: the `5 × 5` grid
`{0, 1/4, 1/2, 3/4, 1}² ⊂ ℝ² = E2`. -/
def jWCenters : Finset Work.Cusp.E2 :=
  (jWGrid ×ˢ jWGrid).image (fun p : ℝ × ℝ => (!₂[p.1, p.2] : Work.Cusp.E2))

/-- **Every point of the unit interval is within `1/8` of a grid point** of `jWGrid`. -/
theorem jWGrid_cover (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    ∃ s ∈ jWGrid, |t - s| ≤ 1 / 8 := by
  by_cases hc1 : t ≤ 1 / 8
  · exact ⟨0, by simp [jWGrid], by rw [sub_zero, abs_of_nonneg h0]; exact hc1⟩
  · rw [not_le] at hc1
    by_cases hc2 : t ≤ 3 / 8
    · refine ⟨1 / 4, by norm_num [jWGrid], ?_⟩
      rw [abs_sub_le_iff]; constructor <;> linarith
    · rw [not_le] at hc2
      by_cases hc3 : t ≤ 5 / 8
      · refine ⟨1 / 2, by norm_num [jWGrid], ?_⟩
        rw [abs_sub_le_iff]; constructor <;> linarith
      · rw [not_le] at hc3
        by_cases hc4 : t ≤ 7 / 8
        · refine ⟨3 / 4, by norm_num [jWGrid], ?_⟩
          rw [abs_sub_le_iff]; constructor <;> linarith
        · rw [not_le] at hc4
          refine ⟨1, by norm_num [jWGrid], ?_⟩
          rw [abs_sub_le_iff]; constructor <;> linarith

/-- **The `w`-section box of a box centre in the `y`-coordinates.**  On `jWSet v c` the
`w`-coordinates are precisely the points of the box `jWBox c`: because `invY v` inverts `wOf v`,
`wOf v w ∈ jWSet v c ↔ ∀ j, |w j − c j| < 1/4`. -/
theorem wOf_mem_jWSet_iff (v : Work.Space.Cusp) (c w : Work.Cusp.E2) :
    Work.Cusp.wOf v w ∈ jWSet v c ↔ w ∈ jWBox c := by
  rw [jWSet, Set.mem_ofPred_eq, Work.Cusp.invY_wOf]

theorem jW_cover (v : Work.Space.Cusp) :
    ∃ C : Finset Work.Cusp.E2, ∀ w : Work.Cusp.E2, (∀ j, 0 ≤ w j ∧ w j ≤ 1) →
      ∃ c ∈ C, Work.Cusp.wOf v w ∈ Work.RTOwed.jWSet v c := by
  refine ⟨jWCenters, fun w hw => ?_⟩
  obtain ⟨s0, hs0, h0⟩ := jWGrid_cover (w 0) (hw 0).1 (hw 0).2
  obtain ⟨s1, hs1, h1⟩ := jWGrid_cover (w 1) (hw 1).1 (hw 1).2
  refine ⟨(!₂[s0, s1] : Work.Cusp.E2), ?mem, ?hbox⟩
  · refine Finset.mem_image.mpr ⟨(s0, s1), ?_, rfl⟩
    exact Finset.mem_product.mpr ⟨hs0, hs1⟩
  · rw [wOf_mem_jWSet_iff, jWBox]
    intro j
    fin_cases j
    · simpa using lt_of_le_of_lt h0 (by norm_num : (1 : ℝ) / 8 < 1 / 4)
    · simpa using lt_of_le_of_lt h1 (by norm_num : (1 : ℝ) / 8 < 1 / 4)

end Work.RTOwed
