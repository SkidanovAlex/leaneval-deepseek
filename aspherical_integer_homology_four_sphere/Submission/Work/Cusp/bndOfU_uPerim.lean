import Mathlib
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `bndOfU` is a left inverse of `uPerim` on the boundary of the square

`uPerim` assigns to a point `q` of the boundary `∂Sq = {p | ‖p‖∞ = 1}` of the filling square
`Sq = [-1,1]²` its (normalised) counterclockwise perimeter parameter, running from `q = (1,1)`
at `uPerim q = 0` through `(1,-1)` (`1/4`), `(-1,-1)` (`1/2`), `(-1,1)` (`3/4`) and back.  The
piecewise definition `bndOfU` of `Basic` is its inverse: for every boundary point `q`,

`bndOfU (uPerim q) = q`.

This is the statement proved here.  The proof is a direct verification: the value `uPerim q`
lies in the appropriate quarter `[0,1/4]`, `[1/4,1/2]`, `[1/2,3/4]`, `[3/4,1)` determined by
which edge of `Sq` carries `q`; the corresponding branch of `bndOfU` then recovers the two
coordinates of `q`.  The four corners `(1,-1)`, `(-1,-1)`, `(-1,1)`, `(1,1)` lie at `u = 1/4`,
`1/2`, `3/4`, `0`, and are handled by the closing branch in each region (the two formulas
involved agree there).  The only place where the *global* hypothesis `nrm q = 1` is used
beyond bounding the coordinates is the fourth region, which must see that a boundary point with
`q 0 ≠ ±1` has `q 1 = 1`.
-/

noncomputable section

namespace Work.Cusp

/-- **Region `q 0 = 1`** (the right edge, `uPerim q = (1 - q 1)/8 ∈ [0,1/4]`).  The first branch of
`bndOfU` recovers `q`, and at the corner `q = (1,-1)` (`uPerim q = 1/4`) the second branch does. -/
private lemma bndOfU_uPerim_right {q : E2} (hA : q 0 = 1) (h1 : |q 1| ≤ 1) :
    bndOfU ((1 - q 1)/8) = q := by
  have hq1 : -1 ≤ q 1 ∧ q 1 ≤ 1 := abs_le.mp h1
  have hf : Int.fract ((1 - q 1)/8) = (1 - q 1)/8 :=
    Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  rw [bndOfU, hf]
  split_ifs with hc hc2 hc3 <;> ext i <;> fin_cases i <;> simp_all <;> linarith

/-- **Region `q 1 = -1`** (the bottom edge, `uPerim q = (3 - q 0)/8 ∈ [1/4,1/2]`).  The second
branch of `bndOfU` recovers `q`, and at the corner `q = (-1,-1)` (`uPerim q = 1/2`) the third
branch does. -/
private lemma bndOfU_uPerim_bottom {q : E2} (h0 : |q 0| ≤ 1) (hB : q 1 = -1) :
    bndOfU ((3 - q 0)/8) = q := by
  have hq0 : -1 ≤ q 0 ∧ q 0 ≤ 1 := abs_le.mp h0
  have hf : Int.fract ((3 - q 0)/8) = (3 - q 0)/8 :=
    Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  rw [bndOfU, hf]
  split_ifs with hc hc2 hc3 <;> ext i <;> fin_cases i <;> simp_all <;> linarith

/-- **Region `q 0 = -1`** (the left edge, `uPerim q = (5 + q 1)/8 ∈ [1/2,3/4]`).  The third branch
of `bndOfU` recovers `q`, and at the corner `q = (-1,1)` (`uPerim q = 3/4`) the fourth branch
does. -/
private lemma bndOfU_uPerim_left {q : E2} (hC : q 0 = -1) (h1 : |q 1| ≤ 1) :
    bndOfU ((5 + q 1)/8) = q := by
  have hq1 : -1 ≤ q 1 ∧ q 1 ≤ 1 := abs_le.mp h1
  have hf : Int.fract ((5 + q 1)/8) = (5 + q 1)/8 :=
    Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  rw [bndOfU, hf]
  split_ifs with hc hc2 hc3 <;> ext i <;> fin_cases i <;> simp_all <;> linarith

/-- **Region `q 0 ≠ ±1`, `q 1 ≠ -1`** (the top edge, `uPerim q = (7 + q 0)/8 ∈ (3/4,1)`).  The
fourth branch of `bndOfU` recovers `q`, using `nrm q = 1` to conclude `q 1 = 1`. -/
private lemma bndOfU_uPerim_top {q : E2} (h0 : |q 0| ≤ 1) (hA : q 0 ≠ 1) (hC : q 0 ≠ -1)
    (hmax : max |q 0| |q 1| = 1) (hB : q 1 ≠ -1) :
    bndOfU ((7 + q 0)/8) = q := by
  have hq0 : -1 ≤ q 0 ∧ q 0 ≤ 1 := abs_le.mp h0
  have hq0abs : |q 0| < 1 := by
    rcases lt_or_eq_of_le h0 with h | h
    · exact h
    · exfalso
      rcases (abs_eq (show (0 : ℝ) ≤ 1 by norm_num)).mp h with hh | hh
      · exact hA hh
      · exact hC hh
  have hq0lt : q 0 < 1 := (abs_lt.mp hq0abs).2
  have hq1abs : |q 1| = 1 := by
    have hle1 : |q 1| ≤ 1 := hmax ▸ le_max_right |q 0| |q 1|
    rcases lt_or_eq_of_le hle1 with h | h
    · exfalso
      have : max |q 0| |q 1| < 1 := max_lt hq0abs h
      linarith
    · exact h
  have hq1 : q 1 = 1 := by
    rcases (abs_eq (show (0 : ℝ) ≤ 1 by norm_num)).mp hq1abs with h | h
    · exact h
    · exact absurd h hB
  have hf : Int.fract ((7 + q 0)/8) = (7 + q 0)/8 :=
    Int.fract_eq_self.mpr ⟨by linarith [hq0.1], by linarith [hq0lt]⟩
  rw [bndOfU, hf]
  split_ifs with hc hc2 hc3 <;> ext i <;> fin_cases i <;> simp_all <;> linarith

/-- `bndOfU` is a left inverse of `uPerim` on the boundary `{q | nrm q = 1}` of the square: the
point of `∂Sq` with perimeter parameter `uPerim q` is `q` itself. -/
theorem bndOfU_uPerim {q : E2} (hq : nrm q = 1) : bndOfU (uPerim q) = q := by
  have hmax : max |q 0| |q 1| = 1 := hq
  have h0 : |q 0| ≤ 1 := hmax ▸ le_max_left |q 0| |q 1|
  have h1 : |q 1| ≤ 1 := hmax ▸ le_max_right |q 0| |q 1|
  by_cases hA : q 0 = 1
  · rw [uPerim, ite_eq_left hA]
    exact bndOfU_uPerim_right hA h1
  · by_cases hB : q 1 = -1
    · rw [uPerim, ite_eq_right hA, ite_eq_left hB]
      exact bndOfU_uPerim_bottom h0 hB
    · by_cases hC : q 0 = -1
      · rw [uPerim, ite_eq_right hA, ite_eq_right hB, ite_eq_left hC]
        exact bndOfU_uPerim_left hC h1
      · rw [uPerim, ite_eq_right hA, ite_eq_right hB, ite_eq_right hC]
        exact bndOfU_uPerim_top h0 hA hC hmax hB

end Work.Cusp
