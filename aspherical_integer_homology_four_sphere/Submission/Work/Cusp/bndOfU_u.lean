/-
# `bndOfU` inverts the perimeter parameter, and `bndOfU (u p) = bnd p`

`bndOfU : ℝ → ∂Sq` is the parametrisation of the boundary of the square by the perimeter
parameter `u ∈ ℝ/ℤ` (`(1,1)` at `u = 0`, counterclockwise, one lap per unit of `u`), and
`uPerim : ∂Sq → [0,1)` is the inverse parametrisation (arclength, normalised so that each of the
four edges has length `1/4`).  This file proves

* `bndOfU (uPerim q) = q` for every `q` of sup norm `1` (i.e. `q ∈ ∂Sq`), the round-trip identity
  along `∂Sq` (`bndOfU_uPerim_aux`, the auxiliary statements `bndOfU_lt_quarter`, …,
  `bndOfU_le_one` being the four branch evaluations of `bndOfU` on the four quarter intervals);
* the requested consequence `bndOfU (u p) = bnd p` for every nonzero `p ∈ Sq`: the layer parameter
  `u p = uPerim (bnd p)` lives on the boundary, where `bndOfU` is the inverse of `uPerim`.

The two ingredients are `nrm_bnd` (`‖bnd p‖∞ = 1` for `p ≠ 0`) and the definition
`u p = uPerim (bnd p)`.
-/
import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.nrm_bnd

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.unusedVariables false

noncomputable section

namespace Work.Cusp

open scoped Real InnerProductSpace
open Function

/-! ### The four branches of `bndOfU` -/

/-- `bndOfU` on the first quarter interval `[0, 1/4)`: the right edge of the square, from `(1,1)`
down to `(1,-1)`. -/
private lemma bndOfU_lt_quarter {v : ℝ} (h0 : 0 ≤ v) (h1 : v < 1 / 4) :
    bndOfU v = !₂[1, 1 - 8 * v] := by
  unfold bndOfU
  rw [(Int.fract_eq_self).mpr ⟨h0, by linarith⟩]
  rw [ite_eq_left h1]

/-- `bndOfU` on `[1/4, 1/2)`: the bottom edge, from `(1,-1)` to `(-1,-1)`. -/
private lemma bndOfU_lt_half {v : ℝ} (h0 : 1 / 4 ≤ v) (h1 : v < 1 / 2) :
    bndOfU v = !₂[3 - 8 * v, -1] := by
  unfold bndOfU
  rw [(Int.fract_eq_self).mpr ⟨by linarith, by linarith⟩]
  rw [ite_eq_right (not_lt.mpr h0), ite_eq_left h1]

/-- `bndOfU` on `[1/2, 3/4)`: the left edge, from `(-1,-1)` to `(-1,1)`. -/
private lemma bndOfU_lt_threequarter {v : ℝ} (h0 : 1 / 2 ≤ v) (h1 : v < 3 / 4) :
    bndOfU v = !₂[-1, 8 * v - 5] := by
  unfold bndOfU
  rw [(Int.fract_eq_self).mpr ⟨by linarith, by linarith⟩]
  rw [ite_eq_right (not_lt.mpr (by linarith : (1:ℝ) / 4 ≤ v)), ite_eq_right (not_lt.mpr h0),
    ite_eq_left h1]

/-- `bndOfU` on `[3/4, 1)`: the top edge, from `(-1,1)` back to `(1,1)`. -/
private lemma bndOfU_le_one {v : ℝ} (h0 : 3 / 4 ≤ v) (h1 : v < 1) :
    bndOfU v = !₂[8 * v - 7, 1] := by
  unfold bndOfU
  rw [(Int.fract_eq_self).mpr ⟨by linarith, h1⟩]
  rw [ite_eq_right (not_lt.mpr (by linarith : (1:ℝ) / 4 ≤ v)),
    ite_eq_right (not_lt.mpr (by linarith : (1:ℝ) / 2 ≤ v)), ite_eq_right (not_lt.mpr h0)]

/-! ### The round-trip identity on `∂Sq` -/

/-- **`bndOfU` is a left inverse of `uPerim` on `∂Sq`.**  If `nrm q = 1` (i.e. `q ∈ ∂Sq`, since
`nrm q = max (|q 0|) (|q 1|)`), then `bndOfU` sends the perimeter parameter `uPerim q ∈ [0,1)` of
`q` back to `q`.

The proof is the four-way case analysis on which edge of the square carries `q`; on each edge
`uPerim q` is affine in the free coordinate, and it runs through the corresponding quarter
interval, with the four corners shared between the two neighbouring branches — exactly the
endpoints at which the four branches of `bndOfU` meet. -/
private lemma bndOfU_uPerim_aux {q : E2} (hq : nrm q = 1) : bndOfU (uPerim q) = q := by
  have hm : max |q 0| |q 1| = 1 := hq
  have hq0a : |q 0| ≤ 1 := hm ▸ le_max_left _ _
  have hq1a : |q 1| ≤ 1 := hm ▸ le_max_right _ _
  have h0le : q 0 ≤ 1 := (abs_le.mp hq0a).2
  have h0ge : -1 ≤ q 0 := (abs_le.mp hq0a).1
  have h1le : q 1 ≤ 1 := (abs_le.mp hq1a).2
  have h1ge : -1 ≤ q 1 := (abs_le.mp hq1a).1
  by_cases hA : q 0 = 1
  · -- right edge: `u = (1 - q 1)/8 ∈ [0, 1/4]`
    have hu : uPerim q = (1 - q 1) / 8 := by rw [uPerim, ite_eq_left hA]
    have hv0 : 0 ≤ (1 - q 1) / 8 := by linarith
    have hv1 : (1 - q 1) / 8 ≤ 1 / 4 := by linarith
    rcases lt_or_eq_of_le hv1 with hlt | heq
    · rw [hu, bndOfU_lt_quarter hv0 hlt]
      have hc : 1 - 8 * ((1 - q 1) / 8) = q 1 := by ring
      ext i
      fin_cases i <;> simp [hA, hc]
    · -- the corner `(1,-1)`: `u = 1/4` lies in the second branch of `bndOfU`
      rw [hu, heq, bndOfU_lt_half le_rfl (by norm_num)]
      have hq1 : q 1 = -1 := by linarith
      ext i
      fin_cases i
      · simp [hA]; norm_num
      · simp [hq1]
  · by_cases hB : q 1 = -1
    · -- bottom edge: `u = (3 - q 0)/8 ∈ (1/4, 1/2]`
      have h0lt : q 0 < 1 := lt_of_le_of_ne h0le hA
      have hu : uPerim q = (3 - q 0) / 8 := by rw [uPerim, ite_eq_right hA, ite_eq_left hB]
      have hv0 : 1 / 4 < (3 - q 0) / 8 := by linarith
      have hv1 : (3 - q 0) / 8 ≤ 1 / 2 := by linarith
      rcases lt_or_eq_of_le hv1 with hlt | heq
      · rw [hu, bndOfU_lt_half (le_of_lt hv0) hlt]
        have hc : 3 - 8 * ((3 - q 0) / 8) = q 0 := by ring
        ext i
        fin_cases i <;> simp [hB, hc]
      · -- the corner `(-1,-1)`: `u = 1/2` lies in the third branch of `bndOfU`
        rw [hu, heq, bndOfU_lt_threequarter le_rfl (by norm_num)]
        have hq0 : q 0 = -1 := by linarith
        ext i
        fin_cases i
        · simp [hq0]
        · simp [hB]; norm_num
    · by_cases hC : q 0 = -1
      · -- left edge: `u = (5 + q 1)/8 ∈ (1/2, 3/4]`
        have h1gt : -1 < q 1 := lt_of_le_of_ne h1ge (Ne.symm hB)
        have hu : uPerim q = (5 + q 1) / 8 := by
          rw [uPerim, ite_eq_right hA, ite_eq_right hB, ite_eq_left hC]
        have hv0 : 1 / 2 < (5 + q 1) / 8 := by linarith
        have hv1 : (5 + q 1) / 8 ≤ 3 / 4 := by linarith
        rcases lt_or_eq_of_le hv1 with hlt | heq
        · rw [hu, bndOfU_lt_threequarter (le_of_lt hv0) hlt]
          have hc : 8 * ((5 + q 1) / 8) - 5 = q 1 := by ring
          ext i
          fin_cases i <;> simp [hC, hc]
        · -- the corner `(-1,1)`: `u = 3/4` lies in the fourth branch of `bndOfU`
          rw [hu, heq, bndOfU_le_one le_rfl (by norm_num)]
          have hq1 : q 1 = 1 := by linarith
          ext i
          fin_cases i
          · simp [hC]; norm_num
          · simp [hq1]
      · -- top edge: `u = (7 + q 0)/8 ∈ (3/4, 1)`
        have h0lt : q 0 < 1 := lt_of_le_of_ne h0le hA
        have h0gt : -1 < q 0 := lt_of_le_of_ne h0ge (Ne.symm hC)
        have hu : uPerim q = (7 + q 0) / 8 := by
          rw [uPerim, ite_eq_right hA, ite_eq_right hB, ite_eq_right hC]
        have hq0abs : |q 0| < 1 := abs_lt.mpr ⟨h0gt, h0lt⟩
        -- on the top edge the second coordinate is `1`; `nrm q = 1` forces `|q 1| = 1`
        have hq1abs : |q 1| = 1 := by
          rcases le_total |q 1| |q 0| with hle | hle
          · rw [max_eq_left hle] at hm
            linarith
          · rw [max_eq_right hle] at hm
            exact hm
        have hq1 : q 1 = 1 := by
          rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hq1abs with h | h
          · exact h
          · exact absurd h hB
        have hv0 : 3 / 4 < (7 + q 0) / 8 := by linarith
        have hv1 : (7 + q 0) / 8 < 1 := by linarith
        rw [hu, bndOfU_le_one (le_of_lt hv0) hv1]
        have hc : 8 * ((7 + q 0) / 8) - 7 = q 0 := by ring
        ext i
        fin_cases i <;> simp [hq1, hc]

/-- **The requested identity.**  For a nonzero point `p` of the square `Sq = [-1,1]²`, the
`bndOfU`-image of the perimeter parameter `u p` of the ray through `p` is the radial projection
`bnd p` of `p` to `∂Sq`.

Indeed `u p = uPerim (bnd p)` by definition, and `nrm (bnd p) = 1` for `p ≠ 0` (`nrm_bnd`), so
`bndOfU_uPerim_aux` applies to `q = bnd p`. -/
theorem bndOfU_u {p : E2} (hp : p ∈ Sq) (h0 : p ≠ 0) : bndOfU (u p) = bnd p :=
  bndOfU_uPerim_aux (nrm_bnd h0)

end Work.Cusp
