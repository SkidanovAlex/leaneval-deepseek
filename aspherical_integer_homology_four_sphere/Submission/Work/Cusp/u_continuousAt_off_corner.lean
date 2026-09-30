/-
# Continuity of the perimeter parameter `u` away from the corner `(1,1)`

`u p = uPerim (bnd p)` is the (normalised) counterclockwise arclength coordinate of the ray through
`p` in the filling square `Sq = [-1,1]²` (`Work.Cusp.Basic`).  As a function of `p` it is *not*
continuous at the ray through the corner `(1,1)`, where it jumps between values near `0` (approached
along the top edge, `uPerim q = (7 + q₀)/8`) and values near `1` (approached along the right edge,
`uPerim q = (1 - q₁)/8`).  Off that ray it *is* continuous, and this file proves it:

`u_continuousAt_off_corner : 0 < nrm p → bnd p ≠ (1,1) → ContinuousAt u p`.

The proof splits into two parts.

* **The boundary.**  `uPerim` is continuous on `∂Sq = {q | nrm q = 1}` away from `(1,1)`
  (`uPerim_continuousWithinAt`).  The argument is a direct `ε`-`δ` proof.  On the relative interior
  of an edge, the coordinate that is pinned to `±1` is *forced* by a small bound on the distance to
  `p`, so `uPerim` agrees there with one of the four affine branches, which is `1/8`-Lipschitz; at
  the three corners other than `(1,1)` the point is on one of the two adjacent edges, and the two
  branch values are controlled by the corresponding coordinate of the displacement.

* **The composition.**  `u = uPerim ∘ bnd` and `bnd` is continuous at any `p` with `nrm p > 0`
  (there `nrm` is invertible on a neighbourhood, `nrm_bnd` then puts `bnd` on `∂Sq`).  Composing
  the two limits with `Filter.Tendsto.comp` gives `ContinuousAt u p`.
-/
import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.nrm_continuous
import Submission.Work.Cusp.nrm_bnd

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.Cusp

open scoped Real Topology
open Filter

/-! ### Distance helpers -/

/-- On `E2 = ℝ²` the `i`-th coordinate difference is bounded by the distance. -/
private lemma abs_coord_sub_le_dist (x p : E2) (i : Fin 2) : |x i - p i| ≤ dist x p := by
  rw [← Real.dist_eq]
  simpa using PiLp.dist_apply_le x p i

/-- If the `i`-th coordinate displacement is `< 8ε` then so is the displacement of the affine
expression `(s - ·)/8`. -/
private lemma bound_sub {x p : E2} {i : Fin 2} {ε s : ℝ} (h : |x i - p i| < 8 * ε) :
    |(s - x i) / 8 - (s - p i) / 8| < ε := by
  have hkey : (s - x i) / 8 - (s - p i) / 8 = (p i - x i) / 8 := by ring
  rw [hkey, abs_div, abs_sub_comm, abs_of_pos (show (0 : ℝ) < 8 by norm_num)]
  linarith

/-- If the `i`-th coordinate displacement is `< 8ε` then so is the displacement of the affine
expression `(s + ·)/8`. -/
private lemma bound_add {x p : E2} {i : Fin 2} {ε s : ℝ} (h : |x i - p i| < 8 * ε) :
    |(s + x i) / 8 - (s + p i) / 8| < ε := by
  have hkey : (s + x i) / 8 - (s + p i) / 8 = (x i - p i) / 8 := by ring
  rw [hkey, abs_div, abs_of_pos (show (0 : ℝ) < 8 by norm_num)]
  linarith

/-! ### The four affine branches of `uPerim` on the edges of the square -/

private lemma uPerim_right {q : E2} (h : q 0 = 1) : uPerim q = (1 - q 1) / 8 := by
  rw [uPerim, ite_eq_left h]

private lemma uPerim_bottom {q : E2} (h : q 1 = -1) : uPerim q = (3 - q 0) / 8 := by
  by_cases h0 : q 0 = 1
  · rw [uPerim, ite_eq_left h0, h, h0]; norm_num
  · rw [uPerim, ite_eq_right h0, ite_eq_left h]

private lemma uPerim_left {q : E2} (h : q 0 = -1) : uPerim q = (5 + q 1) / 8 := by
  by_cases h0 : q 0 = 1
  · rw [h] at h0; norm_num at h0
  · by_cases h1 : q 1 = -1
    · rw [uPerim, ite_eq_right h0, ite_eq_left h1, h, h1]; norm_num
    · rw [uPerim, ite_eq_right h0, ite_eq_right h1, ite_eq_left h]

private lemma uPerim_top {q : E2} (h0 : q 0 ≠ 1) (h2 : q 1 = 1) :
    uPerim q = (7 + q 0) / 8 := by
  have h1 : q 1 ≠ -1 := by rw [h2]; norm_num
  by_cases h3 : q 0 = -1
  · rw [uPerim, ite_eq_right h0, ite_eq_right h1, ite_eq_left h3, h2, h3]; norm_num
  · rw [uPerim, ite_eq_right h0, ite_eq_right h1, ite_eq_right h3]

/-! ### Continuity of `uPerim` along the boundary, away from the corner `(1,1)` -/

/-- `|a| = 1` for a real number gives `a = ±1`. -/
private lemma abs_eq_one {a : ℝ} (h : |a| = 1) : a = 1 ∨ a = -1 :=
  (abs_eq (show (0 : ℝ) ≤ 1 by norm_num)).mp h

/-- **Right edge.**  On `{q | q 0 = 1}` (minus the corners) the perimeter parameter is the affine
function `(1 - q 1)/8`; a small ball in the boundary forces `q 0 = 1`, which is what makes `uPerim`
continuous there. -/
private lemma contWithin_right (p : E2) (hp0 : p 0 = 1) (hp1 : |p 1| < 1) :
    ContinuousWithinAt uPerim {q : E2 | nrm q = 1} p := by
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  refine ⟨min (1 - |p 1|) (8 * ε), lt_min (by linarith [abs_nonneg (p 1)]) (by linarith), ?_⟩
  intro x hxS hx
  have hδ1 : min (1 - |p 1|) (8 * ε) ≤ 1 - |p 1| := min_le_left _ _
  have hδ2 : min (1 - |p 1|) (8 * ε) ≤ 8 * ε := min_le_right _ _
  have hxmax : max |x 0| |x 1| = 1 := by simpa [nrm] using hxS
  have hx0le : |x 0| ≤ 1 := hxmax ▸ le_max_left |x 0| |x 1|
  have hx1le : |x 1| ≤ 1 := hxmax ▸ le_max_right |x 0| |x 1|
  have hx1lt : |x 1| < 1 := by
    have h := abs_coord_sub_le_dist x p 1
    have hlt : |x 1 - p 1| < 1 - |p 1| := lt_of_lt_of_le (lt_of_le_of_lt h hx) hδ1
    have hrev : |x 1| ≤ |x 1 - p 1| + |p 1| := by
      calc |x 1| = |(x 1 - p 1) + p 1| := by rw [sub_add_cancel]
        _ ≤ |x 1 - p 1| + |p 1| := abs_add_le _ _
    linarith
  have hx0 : x 0 = 1 := by
    by_contra h0
    have hx0lt : |x 0| < 1 := by
      rcases lt_or_eq_of_le hx0le with hlt | heq
      · exact hlt
      · exfalso
        have hone : x 0 = -1 := by
          rcases abs_eq_one heq with h | h
          · exact absurd h h0
          · exact h
        have hc := abs_coord_sub_le_dist x p 0
        rw [hone, hp0] at hc
        norm_num at hc
        linarith [hx, hδ1, abs_nonneg (p 1)]
    have : max |x 0| |x 1| < 1 := max_lt hx0lt hx1lt
    rw [hxmax] at this
    exact lt_irrefl 1 this
  rw [uPerim_right hx0, uPerim_right hp0, Real.dist_eq]
  exact bound_sub (i := 1) (s := 1)
    (lt_of_lt_of_le (lt_of_le_of_lt (abs_coord_sub_le_dist x p 1) hx) hδ2)

/-- **Bottom edge.**  On `{q | q 1 = -1}` (minus the corners) a small ball in the boundary forces
`q 1 = -1` and `uPerim` is the affine function `(3 - q 0)/8`. -/
private lemma contWithin_bottom (p : E2) (hp0 : p 0 ≠ 1) (hp1 : p 1 = -1) (hp2 : |p 0| < 1) :
    ContinuousWithinAt uPerim {q : E2 | nrm q = 1} p := by
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  refine ⟨min (1 - |p 0|) (8 * ε), lt_min (by linarith [abs_nonneg (p 0)]) (by linarith), ?_⟩
  intro x hxS hx
  have hδ1 : min (1 - |p 0|) (8 * ε) ≤ 1 - |p 0| := min_le_left _ _
  have hδ2 : min (1 - |p 0|) (8 * ε) ≤ 8 * ε := min_le_right _ _
  have hxmax : max |x 0| |x 1| = 1 := by simpa [nrm] using hxS
  have hx0le : |x 0| ≤ 1 := hxmax ▸ le_max_left |x 0| |x 1|
  have hx1le : |x 1| ≤ 1 := hxmax ▸ le_max_right |x 0| |x 1|
  have hx0lt : |x 0| < 1 := by
    have h := abs_coord_sub_le_dist x p 0
    have hlt : |x 0 - p 0| < 1 - |p 0| := lt_of_lt_of_le (lt_of_le_of_lt h hx) hδ1
    have hrev : |x 0| ≤ |x 0 - p 0| + |p 0| := by
      calc |x 0| = |(x 0 - p 0) + p 0| := by rw [sub_add_cancel]
        _ ≤ |x 0 - p 0| + |p 0| := abs_add_le _ _
    linarith
  have hx1 : x 1 = -1 := by
    by_contra h1
    have hx1lt : |x 1| < 1 := by
      rcases lt_or_eq_of_le hx1le with hlt | heq
      · exact hlt
      · exfalso
        have hone : x 1 = 1 := by
          rcases abs_eq_one heq with h | h
          · exact h
          · exact absurd h h1
        have hc := abs_coord_sub_le_dist x p 1
        rw [hone, hp1] at hc
        norm_num at hc
        linarith [hx, hδ1, abs_nonneg (p 0)]
    have : max |x 0| |x 1| < 1 := max_lt hx0lt hx1lt
    rw [hxmax] at this
    exact lt_irrefl 1 this
  rw [uPerim_bottom hx1, uPerim_bottom hp1, Real.dist_eq]
  exact bound_sub (i := 0) (s := 3)
    (lt_of_lt_of_le (lt_of_le_of_lt (abs_coord_sub_le_dist x p 0) hx) hδ2)

/-- **Left edge.**  On `{q | q 0 = -1}` (minus the corners) a small ball in the boundary forces
`q 0 = -1` and `uPerim` is the affine function `(5 + q 1)/8`. -/
private lemma contWithin_left (p : E2) (hp0 : p 0 = -1) (hp1 : |p 1| < 1) :
    ContinuousWithinAt uPerim {q : E2 | nrm q = 1} p := by
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  refine ⟨min (1 - |p 1|) (8 * ε), lt_min (by linarith [abs_nonneg (p 1)]) (by linarith), ?_⟩
  intro x hxS hx
  have hδ1 : min (1 - |p 1|) (8 * ε) ≤ 1 - |p 1| := min_le_left _ _
  have hδ2 : min (1 - |p 1|) (8 * ε) ≤ 8 * ε := min_le_right _ _
  have hxmax : max |x 0| |x 1| = 1 := by simpa [nrm] using hxS
  have hx0le : |x 0| ≤ 1 := hxmax ▸ le_max_left |x 0| |x 1|
  have hx1le : |x 1| ≤ 1 := hxmax ▸ le_max_right |x 0| |x 1|
  have hx1lt : |x 1| < 1 := by
    have h := abs_coord_sub_le_dist x p 1
    have hlt : |x 1 - p 1| < 1 - |p 1| := lt_of_lt_of_le (lt_of_le_of_lt h hx) hδ1
    have hrev : |x 1| ≤ |x 1 - p 1| + |p 1| := by
      calc |x 1| = |(x 1 - p 1) + p 1| := by rw [sub_add_cancel]
        _ ≤ |x 1 - p 1| + |p 1| := abs_add_le _ _
    linarith
  have hx0 : x 0 = -1 := by
    by_contra h0
    have hx0lt : |x 0| < 1 := by
      rcases lt_or_eq_of_le hx0le with hlt | heq
      · exact hlt
      · exfalso
        have hone : x 0 = 1 := by
          rcases abs_eq_one heq with h | h
          · exact h
          · exact absurd h h0
        have hc := abs_coord_sub_le_dist x p 0
        rw [hone, hp0] at hc
        norm_num at hc
        linarith [hx, hδ1, abs_nonneg (p 1)]
    have : max |x 0| |x 1| < 1 := max_lt hx0lt hx1lt
    rw [hxmax] at this
    exact lt_irrefl 1 this
  rw [uPerim_left hx0, uPerim_left hp0, Real.dist_eq]
  exact bound_add (i := 1) (s := 5)
    (lt_of_lt_of_le (lt_of_le_of_lt (abs_coord_sub_le_dist x p 1) hx) hδ2)

/-- **Top edge.**  On `{q | q 1 = 1}` (minus the corners) a small ball in the boundary forces
`q 1 = 1` and `uPerim` is the affine function `(7 + q 0)/8`. -/
private lemma contWithin_top (p : E2) (hp1 : p 1 = 1) (hp0 : |p 0| < 1) :
    ContinuousWithinAt uPerim {q : E2 | nrm q = 1} p := by
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  refine ⟨min (1 - |p 0|) (8 * ε), lt_min (by linarith [abs_nonneg (p 0)]) (by linarith), ?_⟩
  intro x hxS hx
  have hδ1 : min (1 - |p 0|) (8 * ε) ≤ 1 - |p 0| := min_le_left _ _
  have hδ2 : min (1 - |p 0|) (8 * ε) ≤ 8 * ε := min_le_right _ _
  have hxmax : max |x 0| |x 1| = 1 := by simpa [nrm] using hxS
  have hx0le : |x 0| ≤ 1 := hxmax ▸ le_max_left |x 0| |x 1|
  have hx1le : |x 1| ≤ 1 := hxmax ▸ le_max_right |x 0| |x 1|
  have hx0lt : |x 0| < 1 := by
    have h := abs_coord_sub_le_dist x p 0
    have hlt : |x 0 - p 0| < 1 - |p 0| := lt_of_lt_of_le (lt_of_le_of_lt h hx) hδ1
    have hrev : |x 0| ≤ |x 0 - p 0| + |p 0| := by
      calc |x 0| = |(x 0 - p 0) + p 0| := by rw [sub_add_cancel]
        _ ≤ |x 0 - p 0| + |p 0| := abs_add_le _ _
    linarith
  have hx1 : x 1 = 1 := by
    by_contra h1
    have hx1lt : |x 1| < 1 := by
      rcases lt_or_eq_of_le hx1le with hlt | heq
      · exact hlt
      · exfalso
        have hone : x 1 = -1 := by
          rcases abs_eq_one heq with h | h
          · exact absurd h h1
          · exact h
        have hc := abs_coord_sub_le_dist x p 1
        rw [hone, hp1] at hc
        norm_num at hc
        linarith [hx, hδ1, abs_nonneg (p 0)]
    have : max |x 0| |x 1| < 1 := max_lt hx0lt hx1lt
    rw [hxmax] at this
    exact lt_irrefl 1 this
  have hx0ne : x 0 ≠ 1 := by
    intro h; rw [h] at hx0lt; norm_num at hx0lt
  have hp0ne : p 0 ≠ 1 := by
    intro h; rw [h] at hp0; norm_num at hp0
  rw [uPerim_top hx0ne hx1, uPerim_top hp0ne hp1, Real.dist_eq]
  exact bound_add (i := 0) (s := 7)
    (lt_of_lt_of_le (lt_of_le_of_lt (abs_coord_sub_le_dist x p 0) hx) hδ2)

/-- **Corner `(1,-1)`.**  A small ball in the boundary puts a point on one of the two adjacent
edges (`q 0 = 1` or `q 1 = -1`), and each of the two branch values is within `dist q p / 8` of the
common value `1/4`. -/
private lemma contWithin_corner_b (p : E2) (hp0 : p 0 = 1) (hp1 : p 1 = -1) :
    ContinuousWithinAt uPerim {q : E2 | nrm q = 1} p := by
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  refine ⟨min 1 (8 * ε), lt_min one_pos (by linarith), ?_⟩
  intro x hxS hx
  have hδ1 : min 1 (8 * ε) ≤ 1 := min_le_left _ _
  have hδ2 : min 1 (8 * ε) ≤ 8 * ε := min_le_right _ _
  have hxmax : max |x 0| |x 1| = 1 := by simpa [nrm] using hxS
  have hx0le : |x 0| ≤ 1 := hxmax ▸ le_max_left |x 0| |x 1|
  have hx1le : |x 1| ≤ 1 := hxmax ▸ le_max_right |x 0| |x 1|
  have hdisj : x 0 = 1 ∨ x 1 = -1 := by
    by_contra hc
    rw [not_or] at hc
    obtain ⟨h0, h1⟩ := hc
    have hx0lt : |x 0| < 1 := by
      rcases lt_or_eq_of_le hx0le with hlt | heq
      · exact hlt
      · exfalso
        have hone : x 0 = -1 := by
          rcases abs_eq_one heq with h | h
          · exact absurd h h0
          · exact h
        have hc0 := abs_coord_sub_le_dist x p 0
        rw [hone, hp0] at hc0
        norm_num at hc0
        linarith [hx, hδ1]
    have hx1lt : |x 1| < 1 := by
      rcases lt_or_eq_of_le hx1le with hlt | heq
      · exact hlt
      · exfalso
        have hone : x 1 = 1 := by
          rcases abs_eq_one heq with h | h
          · exact h
          · exact absurd h h1
        have hc1 := abs_coord_sub_le_dist x p 1
        rw [hone, hp1] at hc1
        norm_num at hc1
        linarith [hx, hδ1]
    have : max |x 0| |x 1| < 1 := max_lt hx0lt hx1lt
    rw [hxmax] at this
    exact lt_irrefl 1 this
  rcases hdisj with hx0 | hx1
  · rw [uPerim_right hx0, uPerim_right hp0, Real.dist_eq]
    exact bound_sub (i := 1) (s := 1)
      (lt_of_lt_of_le (lt_of_le_of_lt (abs_coord_sub_le_dist x p 1) hx) hδ2)
  · rw [uPerim_bottom hx1, uPerim_bottom hp1, Real.dist_eq]
    exact bound_sub (i := 0) (s := 3)
      (lt_of_lt_of_le (lt_of_le_of_lt (abs_coord_sub_le_dist x p 0) hx) hδ2)

/-- **Corner `(-1,-1)`.**  Same two-sided argument as at `(1,-1)`, with common value `1/2`. -/
private lemma contWithin_corner_c (p : E2) (hp0 : p 0 = -1) (hp1 : p 1 = -1) :
    ContinuousWithinAt uPerim {q : E2 | nrm q = 1} p := by
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  refine ⟨min 1 (8 * ε), lt_min one_pos (by linarith), ?_⟩
  intro x hxS hx
  have hδ1 : min 1 (8 * ε) ≤ 1 := min_le_left _ _
  have hδ2 : min 1 (8 * ε) ≤ 8 * ε := min_le_right _ _
  have hxmax : max |x 0| |x 1| = 1 := by simpa [nrm] using hxS
  have hx0le : |x 0| ≤ 1 := hxmax ▸ le_max_left |x 0| |x 1|
  have hx1le : |x 1| ≤ 1 := hxmax ▸ le_max_right |x 0| |x 1|
  have hdisj : x 1 = -1 ∨ x 0 = -1 := by
    by_contra hc
    rw [not_or] at hc
    obtain ⟨h1, h0⟩ := hc
    have hx1lt : |x 1| < 1 := by
      rcases lt_or_eq_of_le hx1le with hlt | heq
      · exact hlt
      · exfalso
        have hone : x 1 = 1 := by
          rcases abs_eq_one heq with h | h
          · exact h
          · exact absurd h h1
        have hc1 := abs_coord_sub_le_dist x p 1
        rw [hone, hp1] at hc1
        norm_num at hc1
        linarith [hx, hδ1]
    have hx0lt : |x 0| < 1 := by
      rcases lt_or_eq_of_le hx0le with hlt | heq
      · exact hlt
      · exfalso
        have hone : x 0 = 1 := by
          rcases abs_eq_one heq with h | h
          · exact h
          · exact absurd h h0
        have hc0 := abs_coord_sub_le_dist x p 0
        rw [hone, hp0] at hc0
        norm_num at hc0
        linarith [hx, hδ1]
    have : max |x 0| |x 1| < 1 := max_lt hx0lt hx1lt
    rw [hxmax] at this
    exact lt_irrefl 1 this
  rcases hdisj with hx1 | hx0
  · rw [uPerim_bottom hx1, uPerim_bottom hp1, Real.dist_eq]
    exact bound_sub (i := 0) (s := 3)
      (lt_of_lt_of_le (lt_of_le_of_lt (abs_coord_sub_le_dist x p 0) hx) hδ2)
  · rw [uPerim_left hx0, uPerim_left hp0, Real.dist_eq]
    exact bound_add (i := 1) (s := 5)
      (lt_of_lt_of_le (lt_of_le_of_lt (abs_coord_sub_le_dist x p 1) hx) hδ2)

/-- **Corner `(-1,1)`.**  The adjacent edges are `q 0 = -1` and `q 1 = 1`; the common value is
`3/4`. -/
private lemma contWithin_corner_d (p : E2) (hp0 : p 0 = -1) (hp1 : p 1 = 1) :
    ContinuousWithinAt uPerim {q : E2 | nrm q = 1} p := by
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  refine ⟨min 1 (8 * ε), lt_min one_pos (by linarith), ?_⟩
  intro x hxS hx
  have hδ1 : min 1 (8 * ε) ≤ 1 := min_le_left _ _
  have hδ2 : min 1 (8 * ε) ≤ 8 * ε := min_le_right _ _
  have hxmax : max |x 0| |x 1| = 1 := by simpa [nrm] using hxS
  have hx0le : |x 0| ≤ 1 := hxmax ▸ le_max_left |x 0| |x 1|
  have hx1le : |x 1| ≤ 1 := hxmax ▸ le_max_right |x 0| |x 1|
  have hdisj : x 0 = -1 ∨ x 1 = 1 := by
    by_contra hc
    rw [not_or] at hc
    obtain ⟨h0, h1⟩ := hc
    have hx0lt : |x 0| < 1 := by
      rcases lt_or_eq_of_le hx0le with hlt | heq
      · exact hlt
      · exfalso
        have hone : x 0 = 1 := by
          rcases abs_eq_one heq with h | h
          · exact h
          · exact absurd h h0
        have hc0 := abs_coord_sub_le_dist x p 0
        rw [hone, hp0] at hc0
        norm_num at hc0
        linarith [hx, hδ1]
    have hx1lt : |x 1| < 1 := by
      rcases lt_or_eq_of_le hx1le with hlt | heq
      · exact hlt
      · exfalso
        have hone : x 1 = -1 := by
          rcases abs_eq_one heq with h | h
          · exact absurd h h1
          · exact h
        have hc1 := abs_coord_sub_le_dist x p 1
        rw [hone, hp1] at hc1
        norm_num at hc1
        linarith [hx, hδ1]
    have : max |x 0| |x 1| < 1 := max_lt hx0lt hx1lt
    rw [hxmax] at this
    exact lt_irrefl 1 this
  rcases hdisj with hx0 | hx1
  · rw [uPerim_left hx0, uPerim_left hp0, Real.dist_eq]
    exact bound_add (i := 1) (s := 5)
      (lt_of_lt_of_le (lt_of_le_of_lt (abs_coord_sub_le_dist x p 1) hx) hδ2)
  · have hx0ne : x 0 ≠ 1 := by
      intro hx0one
      have hc0 := abs_coord_sub_le_dist x p 0
      rw [hx0one, hp0] at hc0
      norm_num at hc0
      linarith [hx, hδ1]
    have hp0ne : p 0 ≠ 1 := by rw [hp0]; norm_num
    rw [uPerim_top hx0ne hx1, uPerim_top hp0ne hp1, Real.dist_eq]
    exact bound_add (i := 0) (s := 7)
      (lt_of_lt_of_le (lt_of_le_of_lt (abs_coord_sub_le_dist x p 0) hx) hδ2)

/-- **`uPerim` is continuous on `∂Sq` away from the corner `(1,1)`.**  A boundary point of sup norm
`1` lies on one of the four closed edges; each edge is covered by the cases above. -/
private lemma uPerim_continuousWithinAt {p : E2} (hpS : nrm p = 1)
    (hne : p ≠ (!₂[(1 : ℝ), (1 : ℝ)] : E2)) :
    ContinuousWithinAt uPerim {q : E2 | nrm q = 1} p := by
  have hmax : max |p 0| |p 1| = 1 := by simpa [nrm] using hpS
  have hp0le : |p 0| ≤ 1 := hmax ▸ le_max_left |p 0| |p 1|
  have hp1le : |p 1| ≤ 1 := hmax ▸ le_max_right |p 0| |p 1|
  by_cases hpA : p 0 = 1
  · have hp1ne : p 1 ≠ 1 := by
      intro h
      exact hne (by ext i; fin_cases i <;> simp [hpA, h])
    by_cases hpB : p 1 = -1
    · exact contWithin_corner_b p hpA hpB
    · exact contWithin_right p hpA (by
        have h := abs_le.mp hp1le
        exact abs_lt.mpr ⟨lt_of_le_of_ne h.1 (Ne.symm hpB), lt_of_le_of_ne h.2 hp1ne⟩)
  · by_cases hpB : p 1 = -1
    · by_cases hpC : p 0 = -1
      · exact contWithin_corner_c p hpC hpB
      · exact contWithin_bottom p hpA hpB (by
          have h := abs_le.mp hp0le
          exact abs_lt.mpr ⟨lt_of_le_of_ne h.1 (Ne.symm hpC), lt_of_le_of_ne h.2 hpA⟩)
    · by_cases hpC : p 0 = -1
      · by_cases hpD : p 1 = 1
        · exact contWithin_corner_d p hpC hpD
        · exact contWithin_left p hpC (by
            have h := abs_le.mp hp1le
            exact abs_lt.mpr ⟨lt_of_le_of_ne h.1 (Ne.symm hpB), lt_of_le_of_ne h.2 hpD⟩)
      · have hpD : p 1 = 1 := by
          have hp0lt : |p 0| < 1 := by
            have h := abs_le.mp hp0le
            exact abs_lt.mpr ⟨lt_of_le_of_ne h.1 (Ne.symm hpC), lt_of_le_of_ne h.2 hpA⟩
          have h1 : |p 1| = 1 := by
            rcases lt_or_eq_of_le hp1le with hlt | heq
            · exfalso
              have : max |p 0| |p 1| < 1 := max_lt hp0lt hlt
              rw [hmax] at this
              exact lt_irrefl 1 this
            · exact heq
          rcases abs_eq_one h1 with h | h
          · exact h
          · exact absurd h hpB
        exact contWithin_top p hpD (by
          have h := abs_le.mp hp0le
          exact abs_lt.mpr ⟨lt_of_le_of_ne h.1 (Ne.symm hpC), lt_of_le_of_ne h.2 hpA⟩)

/-! ### The requested lemma -/

/-- **`u` is continuous at every ray off the corner `(1,1)`.**  Write `u = uPerim ∘ bnd`.  For
`0 < nrm p` the map `bnd q = (nrm q)⁻¹ • q` is continuous at `p` and, near `p`, lands in the
boundary `∂Sq = {q | nrm q = 1}` (`nrm_bnd`); on that boundary `uPerim` is continuous at `bnd p`
provided `bnd p ≠ (1,1)` (`uPerim_continuousWithinAt`).  Composing the two limits gives the
result. -/
theorem u_continuousAt_off_corner {p : E2} (hp : 0 < nrm p)
    (hne : bnd p ≠ !₂[(1 : ℝ), (1 : ℝ)]) : ContinuousAt u p := by
  have hpne : p ≠ 0 := by intro h; rw [h] at hp; simp [nrm] at hp
  have hS : bnd p ∈ {q : E2 | nrm q = 1} := by simpa using nrm_bnd hpne
  have hrat : ContinuousWithinAt uPerim {q : E2 | nrm q = 1} (bnd p) :=
    uPerim_continuousWithinAt hS hne
  have hbnd_cont : ContinuousAt bnd p := by
    have h1 : ContinuousAt (fun q : E2 => (nrm q)⁻¹) p :=
      nrm_continuous.continuousAt.inv₀ (ne_of_gt hp)
    have h2 : ContinuousAt (fun q : E2 => q) p := continuousAt_id
    have hmul : ContinuousAt (fun q : E2 => (nrm q)⁻¹ • q) p := h1.smul h2
    exact hmul
  have hev : ∀ᶠ q in 𝓝 p, bnd q ∈ {r : E2 | nrm r = 1} := by
    filter_upwards [nrm_continuous.continuousAt.eventually (isOpen_Ioi.mem_nhds hp)] with q hq
    have hq0 : q ≠ 0 := fun h => by rw [h] at hq; simp [nrm] at hq
    simpa using nrm_bnd hq0
  have htend : Tendsto bnd (𝓝 p) (𝓝[{r : E2 | nrm r = 1}] (bnd p)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hbnd_cont, hev⟩
  have hcomp : Tendsto (fun q : E2 => uPerim (bnd q)) (𝓝 p) (𝓝 (uPerim (bnd p))) :=
    Filter.Tendsto.comp hrat htend
  change ContinuousAt (fun q : E2 => uPerim (bnd q)) p
  exact hcomp

end Work.Cusp
