import Mathlib
import Submission.Work.Polygon.DiscreteConvex
import Submission.Work.Polygon.AngularRanks

/-!
# Data tightness of the largest convex minorant at its angular vertices

The P2-general program needs, at every **angular rank** of the Grayson polygon, a
subgroup realising the polygon value (within `O(1)`; exactly when the data is tight).
The first input is a pure-function fact about the polygon itself: the largest convex
minorant `c = largestConvexMinorant d g` of an arbitrary data function `g : {0,…,d} → ℝ`
is **tight against `g` at every angular vertex** of `c`:

    `largestConvexMinorant_tight_at_angular` :
        for `1 ≤ s < numBlocks d c`, with `j := blockStart d c s`:
        `c j = g j`.

**Proof (point perturbation).**  At an angular vertex `j` of a discrete-convex `c` the
slope strictly increases there (`dslope c (j−1) < dslope c j`,
`AngularRanks.dslope_strict_of_blockStart`), so the convexity three-term inequality at
`j` has positive slack:

    `slack := c(j−1) + c(j+1) − 2·c(j) = dslope c j − dslope c (j−1) > 0`.

If `c j < g j` (so `a := g j − c j > 0`), raise `c` at the single point `j` by a small
`ε := min a slack / 2 > 0` (the function `raiseAt c j ε`).  This stays convex (only the
three-term inequality with middle point `j` is affected — it needs `2ε ≤ slack`; all
others are preserved or only helped since the raise only increases values) and stays
below `g` (`ε ≤ a` keeps the constraint at `j`, the other points are untouched), giving a
convex minorant strictly larger than `c` at `j` — contradicting the maximality of the
largest convex minorant (`DiscreteConvex.convexMinorant_le_largest`).  Hence `c j = g j`.

The lattice-level consumer (`Submission/Work/Lattice/AngularTightness.lean`) instantiates
this with `g := rankData Λ` to get `rankData = polygon` at the angular ranks, and
`Submission.DataAttainment` then realises the value by a subgroup.

All declarations here are Mathlib + `DiscreteConvex`/`AngularRanks` only (candidates for
the shared commons once the downstream P2 module fixes the API shape).
-/

open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

noncomputable section

namespace Submission.DataTightness

open Submission.Polygon
open Submission.AngularRanks

/-- Raise the function `c` at the single point `j` by `ε` (used for the angular-vertex
perturbation). -/
def raiseAt (c : ℕ → ℝ) (j : ℕ) (ε : ℝ) : ℕ → ℝ :=
  fun i => if i = j then c i + ε else c i

/-- Raising at `j` by `ε ≥ 0` increases every value. -/
lemma raiseAt_ge {c : ℕ → ℝ} {j : ℕ} {ε : ℝ} (hε : 0 ≤ ε) (i : ℕ) :
    c i ≤ raiseAt c j ε i := by
  dsimp [raiseAt]
  by_cases hij : i = j
  · simp [hij, hε]
  · simp [hij]

/-- A small raise at an interior vertex of a convex minorant keeps it a convex minorant:
if `c ∈ MinorantSet d g`, `1 ≤ j`, `j + 1 ≤ d`, `0 ≤ ε`, `c j + ε ≤ g j` (minorant at
`j`) and `2ε ≤ c(j−1) + c(j+1) − 2c j` (convexity slack at `j`), then
`raiseAt c j ε ∈ MinorantSet d g`. -/
lemma raiseAt_mem_minorant {d : ℕ} {g c : ℕ → ℝ} (hc : c ∈ MinorantSet d g) {j : ℕ}
    (hj1 : 1 ≤ j) (_hjd : j + 1 ≤ d) {ε : ℝ} (hε0 : 0 ≤ ε) (hεg : c j + ε ≤ g j)
    (hεslack : 2 * ε ≤ c (j - 1) + c (j + 1) - 2 * c j) :
    raiseAt c j ε ∈ MinorantSet d g := by
  constructor
  · -- convexity: only the three-term inequality with middle point j is affected
    apply convex_of_three_term
    intro i hi  -- hi : i + 2 ≤ d
    have hthree : c i + c (i + 2) ≥ 2 * c (i + 1) := three_term_of_convex hc.1 hi
    by_cases hij : i + 1 = j
    · -- middle point is j: use the slack bound (2ε ≤ slack)
      have hne1 : i ≠ j := by omega
      have hne2 : i + 2 ≠ j := by omega
      have hci : raiseAt c j ε i = c i := by
        dsimp [raiseAt]
        simp [hne1]
      have hci2 : raiseAt c j ε (i + 2) = c (i + 2) := by
        dsimp [raiseAt]
        simp [hne2]
      have hcj : raiseAt c j ε (i + 1) = c (i + 1) + ε := by
        dsimp [raiseAt]
        simp [hij]
      have hεs : 2 * ε ≤ c i + c (i + 2) - 2 * c (i + 1) := by
        have hb := hεslack
        have h1 : j - 1 = i := by omega
        have h2 : j + 1 = i + 2 := by omega
        rw [h1, h2, ← hij] at hb
        simpa using hb
      nlinarith
    · -- middle point is not raised: c'(middle) = c(middle) and the outer points only grow
      have hmid : raiseAt c j ε (i + 1) = c (i + 1) := by
        dsimp [raiseAt]
        simp [hij]
      have hgi : c i ≤ raiseAt c j ε i := raiseAt_ge hε0 i
      have hgi2 : c (i + 2) ≤ raiseAt c j ε (i + 2) := raiseAt_ge hε0 (i + 2)
      nlinarith
  · -- minorant: unchanged away from j; at j use c j + ε ≤ g j
    intro i hi
    by_cases hij : i = j
    · subst i
      simpa [raiseAt] using hεg
    · have hci : raiseAt c j ε i = c i := by
        dsimp [raiseAt]
        simp [hij]
      rw [hci]
      exact hc.2 i hi

/-- **Data tightness at angular vertices**: for any `g : ℕ → ℝ`, the largest convex
minorant `c := largestConvexMinorant d g` equals `g` at every angular vertex
`j = blockStart d c s` (`1 ≤ s < numBlocks d c`). -/
theorem largestConvexMinorant_tight_at_angular (d : ℕ) (g : ℕ → ℝ) {s : ℕ}
    (hs1 : 1 ≤ s) (hsN : s < numBlocks d (largestConvexMinorant d g)) :
    largestConvexMinorant d g (blockStart d (largestConvexMinorant d g) s) =
      g (blockStart d (largestConvexMinorant d g) s) := by
  classical
  let c : ℕ → ℝ := largestConvexMinorant d g
  let j : ℕ := blockStart d c s
  have hcvx : DiscreteConvexOn c d := by
    dsimp [c]
    exact largestConvexMinorant_convex d g
  have hc_mem : c ∈ MinorantSet d g := by
    dsimp [c]
    exact largestConvexMinorant_mem d g
  have hjle : j ≤ d := by
    dsimp [j]
    exact blockStart_le_d d c s
  have hcle : c j ≤ g j := hc_mem.2 j hjle
  have hnumle : numBlocks d c ≤ d := by
    have hd_wit : blockStart d c d = d := blockStart_d_eq_d d c
    exact Nat.find_min' (show ∃ n : ℕ, blockStart d c n = d from ⟨d, hd_wit⟩) hd_wit
  have hsle : s ≤ d := le_trans (Nat.le_of_lt hsN) hnumle
  have hjge : 1 ≤ j := by
    have h₁ : s ≤ blockStart d c s := blockStart_n_ge d c s hsle
    dsimp [j] at h₁ ⊢
    omega
  have hjlt : j < d := by
    dsimp [j]
    exact blockStart_lt_numBlocks d c hsN
  have hj1 : j + 1 ≤ d := by omega
  -- the slope strictly increases at the angular vertex j
  have hsl : dslope c (j - 1) < dslope c j := by
    dsimp [j]
    exact dslope_strict_of_blockStart hcvx hs1 hsN
  -- contradiction if strict
  by_contra hne
  have hlt : c j < g j := lt_of_le_of_ne hcle hne
  have hslack : 0 < c (j - 1) + c (j + 1) - 2 * c j := by
    unfold Submission.Polygon.dslope at hsl
    have hjl : j - 1 + 1 = j := by omega
    rw [hjl] at hsl
    nlinarith
  let a : ℝ := g j - c j
  let slack : ℝ := c (j - 1) + c (j + 1) - 2 * c j
  have ha0 : 0 < a := by
    dsimp [a]
    linarith
  have hslack0 : 0 < slack := by
    dsimp [slack]
    exact hslack
  let ε : ℝ := min a slack / 2
  have hεpos : 0 < ε := by
    dsimp [ε]
    have hmin : 0 < min a slack := lt_min ha0 hslack0
    positivity
  have hεg : c j + ε ≤ g j := by
    dsimp [ε, a]
    have h₁ : min (g j - c j) slack / 2 ≤ g j - c j := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
      have hm : min (g j - c j) slack ≤ g j - c j := min_le_left _ _
      nlinarith [hm, hlt]
    linarith
  have hεslack' : 2 * ε ≤ slack := by
    dsimp [ε]
    have h₂ : 2 * (min a slack / 2) = min a slack := by
      field_simp
    rw [h₂]
    exact min_le_right a slack
  have hc'mem : raiseAt c j ε ∈ MinorantSet d g :=
    raiseAt_mem_minorant hc_mem hjge hj1 (le_of_lt hεpos) hεg hεslack'
  -- c' is a strictly larger convex minorant at j than the largest one — contradiction
  have hc'le : raiseAt c j ε j ≤ largestConvexMinorant d g j := by
    exact convexMinorant_le_largest d g hc'mem hjle
  have hbig : c j < raiseAt c j ε j := by
    dsimp [raiseAt]
    have : c j < c j + ε := by linarith
    simpa using this
  dsimp [c] at hc'le hbig
  nlinarith

/-- A small raise at a point that is not the middle of any constrained three-term triple
keeps a convex minorant convex: if `j = 0` or `j = d`, no three-term inequality
(`i + 2 ≤ d`, middle `i + 1 ∈ {1,…,d−1}`) has `j` as its middle, so only the value at
`j` changes (upwards) and convexity is preserved; the minorant constraint at `j` needs
`c j + ε ≤ g j`. -/
lemma raiseAt_mem_minorant_of_not_middle {d : ℕ} {g c : ℕ → ℝ} (hc : c ∈ MinorantSet d g)
    {j : ℕ} (hj : j = 0 ∨ d ≤ j) (_hjd : j ≤ d) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hεg : c j + ε ≤ g j) :
    raiseAt c j ε ∈ MinorantSet d g := by
  constructor
  · apply convex_of_three_term
    intro i hi  -- i + 2 ≤ d; middle i+1 ∈ {1,…,d−1}
    have hthree : c i + c (i + 2) ≥ 2 * c (i + 1) := three_term_of_convex hc.1 hi
    -- j is not the middle point i+1 (the middle lies strictly between 0 and d)
    have hmid_ne : j ≠ i + 1 := by
      intro heq
      have hi1 : 1 ≤ i + 1 := by omega
      have hlt : i + 1 < d := by omega
      rcases hj with hj0 | hjge
      · have hz : i + 1 = 0 := by omega
        omega
      · omega
    have hmid : raiseAt c j ε (i + 1) = c (i + 1) := by
      dsimp [raiseAt]
      rw [if_neg (show i + 1 ≠ j from fun h => hmid_ne h.symm)]
    have hgi : c i ≤ raiseAt c j ε i := raiseAt_ge hε0 i
    have hgi2 : c (i + 2) ≤ raiseAt c j ε (i + 2) := raiseAt_ge hε0 (i + 2)
    nlinarith
  · intro i hi
    by_cases hij : i = j
    · subst i
      simpa [raiseAt] using hεg
    · have hci : raiseAt c j ε i = c i := by
        dsimp [raiseAt]
        simp [hij]
      rw [hci]
      exact hc.2 i hi

/-- **Endpoint tightness (left)**: the largest convex minorant of `g` equals `g` at `0`
(raising the endpoint only helps convexity, so a strict gap would contradict
maximality). -/
theorem largestConvexMinorant_left_tight (d : ℕ) (g : ℕ → ℝ) :
    largestConvexMinorant d g 0 = g 0 := by
  classical
  let c : ℕ → ℝ := largestConvexMinorant d g
  have hc_mem : c ∈ MinorantSet d g := by
    dsimp [c]
    exact largestConvexMinorant_mem d g
  have hcle : c 0 ≤ g 0 := hc_mem.2 0 (by omega)
  by_contra hne
  have hlt : c 0 < g 0 := lt_of_le_of_ne hcle hne
  let a : ℝ := g 0 - c 0
  let ε : ℝ := a / 2
  have hεpos : 0 < ε := by
    dsimp [ε, a]
    linarith
  have hεg : c 0 + ε ≤ g 0 := by
    dsimp [ε, a]
    linarith
  have hc'mem : raiseAt c 0 ε ∈ MinorantSet d g :=
    raiseAt_mem_minorant_of_not_middle hc_mem (Or.inl rfl) (by omega) (le_of_lt hεpos) hεg
  have hc'le : raiseAt c 0 ε 0 ≤ largestConvexMinorant d g 0 :=
    convexMinorant_le_largest d g hc'mem (by omega)
  have hbig : c 0 < raiseAt c 0 ε 0 := by
    dsimp [raiseAt]
    have : c 0 < c 0 + ε := by linarith
    simpa using this
  dsimp [c] at hc'le hbig
  nlinarith

/-- **Endpoint tightness (right)**: the largest convex minorant of `g` equals `g` at `d`
(raising the endpoint only helps convexity, so a strict gap would contradict
maximality). -/
theorem largestConvexMinorant_right_tight (d : ℕ) (g : ℕ → ℝ) :
    largestConvexMinorant d g d = g d := by
  classical
  let c : ℕ → ℝ := largestConvexMinorant d g
  have hc_mem : c ∈ MinorantSet d g := by
    dsimp [c]
    exact largestConvexMinorant_mem d g
  have hcle : c d ≤ g d := hc_mem.2 d (le_rfl)
  by_contra hne
  have hlt : c d < g d := lt_of_le_of_ne hcle hne
  let a : ℝ := g d - c d
  let ε : ℝ := a / 2
  have hεpos : 0 < ε := by
    dsimp [ε, a]
    linarith
  have hεg : c d + ε ≤ g d := by
    dsimp [ε, a]
    linarith
  have hc'mem : raiseAt c d ε ∈ MinorantSet d g :=
    raiseAt_mem_minorant_of_not_middle hc_mem (Or.inr le_rfl) (le_rfl) (le_of_lt hεpos) hεg
  have hc'le : raiseAt c d ε d ≤ largestConvexMinorant d g d :=
    convexMinorant_le_largest d g hc'mem (le_rfl)
  have hbig : c d < raiseAt c d ε d := by
    dsimp [raiseAt]
    have : c d < c d + ε := by linarith
    simpa using this
  dsimp [c] at hc'le hbig
  nlinarith

end Submission.DataTightness

end
