import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import ChallengeDeps
import Submission.CellGrid
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Corridor geometry of the cell cutoffs

The cutoffs `ξ_j(t) := rhoProfile (t/ℓ + 1 − j)` (`axisFam` of
`Submission.CellCutoffs` with the concrete profile of `Submission.Profile`)
are supported in the *extended cell* of their index `j`:

    supp ξ_j ⊆ ((j−1)·ℓ, (j+1)·ℓ)            (an interval of length 2ℓ),

so neighbouring windows overlap on intervals of length `ℓ`, and at any point
`t ∈ [0, m·ℓ]` at most *two* windows are active, with consecutive indices.
This module makes that geometry explicit (turning the "overlap ~2ℓ" heuristic
into statements about supports):

  * `axisExt` / `axisExtCl` — the open/closed extended cell of an axis index;
  * `axisFam_support_ext` — `ξ_j` vanishes outside its extended cell;
  * `axis_overlap` — two windows active at the same point have indices within
    `1` of each other;
  * `axis_active_pair` — the active indices at a point are consecutive
    (hence at most two of them);
  * `axisOf` / `extCell3` — the axis component of a 3D cell per coordinate and
    the 3D extended cell (a product of axis extended cells);
  * `cellCut_support_ext` — the 3D cell cutoff is supported in its extended
    cell.

These are the geometric facts behind the corridor correction of the bracket:
an assignment piece `χ_a·Ψ` confines particle `i` to the extended cell of
`a_i` (length `2ℓ` per axis), so the per-cell Neumann energy must be evaluated
on cells of side `2ℓ` (or on the length-`ℓ` core cells plus a corridor
correction that the extended side absorbs).
-/

namespace Submission

open _root_.BoseGases
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The open extended cell of the axis index `j`: the interval where the
cutoff `ξ_j` can be nonzero. -/
def axisExt {m : ℕ} (ℓ : ℝ) (j : Fin (m + 2)) : Set ℝ :=
  {t : ℝ | ((j.val : ℝ) - 1) * ℓ < t ∧ t < ((j.val : ℝ) + 1) * ℓ}

/-- The closed extended cell of the axis index `j`. -/
def axisExtCl {m : ℕ} (ℓ : ℝ) (j : Fin (m + 2)) : Set ℝ :=
  {t : ℝ | ((j.val : ℝ) - 1) * ℓ ≤ t ∧ t ≤ ((j.val : ℝ) + 1) * ℓ}

/-- Converting `(a : ℝ) < (b : ℝ) + 2` (two shifted natural casts) into the
equivalent integer inequality. -/
private lemma int_le_of_real_lt {a b : ℕ} (h : (a : ℝ) < (b : ℝ) + 2) :
    (a : ℤ) ≤ (b : ℤ) + 1 := by
  have h' : (a : ℝ) < ((b + 2 : ℕ) : ℝ) := by
    calc
      (a : ℝ) < (b : ℝ) + 2 := h
      _ = ((b + 2 : ℕ) : ℝ) := by norm_num
  have hlt : a < b + 2 := by exact_mod_cast h'
  have hn : a ≤ b + 1 := by omega
  omega

/-- The axis cutoff `ξ_j` vanishes outside its (open) extended cell. -/
lemma axisFam_support_ext {ℓ : ℝ} (hℓ : 0 < ℓ) (m : ℕ) (j : Fin (m + 2)) {t : ℝ}
    (ht : axisFam rhoProfile ℓ m j t ≠ 0) : t ∈ axisExt ℓ j := by
  have hnz : rhoProfile (t / ℓ + 1 - (j.val : ℝ)) ≠ 0 := by
    simpa [axisFam] using ht
  have hpos : 0 < t / ℓ + 1 - (j.val : ℝ) := by
    by_contra h
    exact hnz (profile_supp _ (Or.inl (le_of_not_gt h)))
  have hlt2 : t / ℓ + 1 - (j.val : ℝ) < 2 := by
    by_contra h
    exact hnz (profile_supp _ (Or.inr (le_of_not_gt h)))
  unfold axisExt
  constructor
  · have h : (j.val : ℝ) - 1 < t / ℓ := by linarith
    exact (lt_div_iff₀ hℓ).mp h
  · have h : t / ℓ < (j.val : ℝ) + 1 := by linarith
    exact (div_lt_iff₀ hℓ).mp h

/-- Two axis windows active at the same point have indices within `1` of each
other. -/
lemma axis_overlap {ℓ : ℝ} (hℓ : 0 < ℓ) (m : ℕ) (j j' : Fin (m + 2)) {t : ℝ}
    (hj : axisFam rhoProfile ℓ m j t ≠ 0) (hj' : axisFam rhoProfile ℓ m j' t ≠ 0) :
    ((j'.val : ℤ) ≤ (j.val : ℤ) + 1) ∧ ((j.val : ℤ) ≤ (j'.val : ℤ) + 1) := by
  have hjb : ((j.val : ℝ) - 1) * ℓ < t ∧ t < ((j.val : ℝ) + 1) * ℓ :=
    axisFam_support_ext hℓ m j hj
  have hjb' : ((j'.val : ℝ) - 1) * ℓ < t ∧ t < ((j'.val : ℝ) + 1) * ℓ :=
    axisFam_support_ext hℓ m j' hj'
  have hdiv1 : (j'.val : ℝ) - 1 < t / ℓ := (lt_div_iff₀ hℓ).mpr hjb'.1
  have hdiv2 : t / ℓ < (j.val : ℝ) + 1 := (div_lt_iff₀ hℓ).mpr hjb.2
  have hlt : (j'.val : ℝ) < (j.val : ℝ) + 2 := by linarith
  have hdiv3 : (j.val : ℝ) - 1 < t / ℓ := (lt_div_iff₀ hℓ).mpr hjb.1
  have hdiv4 : t / ℓ < (j'.val : ℝ) + 1 := (div_lt_iff₀ hℓ).mpr hjb'.2
  have hlt' : (j.val : ℝ) < (j'.val : ℝ) + 2 := by linarith
  constructor
  · exact int_le_of_real_lt hlt
  · exact int_le_of_real_lt hlt'

/-- The active axis indices at a point are consecutive: two distinct active
indices differ by exactly one. -/
lemma axis_active_pair {ℓ : ℝ} (hℓ : 0 < ℓ) (m : ℕ) (j j' : Fin (m + 2)) {t : ℝ}
    (hj : axisFam rhoProfile ℓ m j t ≠ 0) (hj' : axisFam rhoProfile ℓ m j' t ≠ 0)
    (hne : j ≠ j') : j'.val = j.val + 1 ∨ j.val = j'.val + 1 := by
  have hmem : ((j'.val : ℤ) ≤ (j.val : ℤ) + 1) ∧ ((j.val : ℤ) ≤ (j'.val : ℤ) + 1) :=
    axis_overlap hℓ m j j' hj hj'
  have hvalne : j'.val ≠ j.val := by
    intro h
    exact hne (Fin.ext h.symm)
  have h1 : j'.val ≤ j.val + 1 := by
    have hz : (j'.val : ℤ) ≤ (j.val : ℤ) + 1 := hmem.1
    omega
  have h2 : j.val ≤ j'.val + 1 := by
    have hz : (j.val : ℤ) ≤ (j'.val : ℤ) + 1 := hmem.2
    omega
  by_cases hlt : j.val < j'.val
  · left
    omega
  · right
    have hle : j'.val ≤ j.val := le_of_not_gt hlt
    have hlt' : j'.val < j.val := lt_of_le_of_ne hle hvalne
    omega

/-- The axis index of the 3D cell `c` in the coordinate direction `k`. -/
def axisOf {m : ℕ} (c : CellIdx m) (k : Fin 3) : Fin (m + 2) :=
  match k.val with
  | 0 => c.1
  | 1 => c.2.1
  | _ => c.2.2

/-- The open extended cell of the 3D cell `c` (a product of axis extended
cells). -/
def extCell3 {m : ℕ} (ℓ : ℝ) (c : CellIdx m) : Set ℝ³ :=
  {y : ℝ³ | ∀ k : Fin 3, y k ∈ axisExt ℓ (axisOf c k)}

/-- The 3D cell cutoff vanishes outside its extended cell. -/
lemma cellCut_support_ext {ℓ : ℝ} (hℓ : 0 < ℓ) (m : ℕ) (c : CellIdx m) {y : ℝ³}
    (hy : cellCut ℓ m c y ≠ 0) : y ∈ extCell3 ℓ c := by
  intro k
  fin_cases k
  · apply axisFam_support_ext hℓ m c.1
    have hprod : axisFam rhoProfile ℓ m c.1 (y 0) *
        (axisFam rhoProfile ℓ m c.2.1 (y 1) * axisFam rhoProfile ℓ m c.2.2 (y 2)) ≠ 0 := by
      simpa [cellCut, mul_assoc] using hy
    exact (mul_ne_zero_iff.mp hprod).1
  · apply axisFam_support_ext hℓ m c.2.1
    have hprod : axisFam rhoProfile ℓ m c.1 (y 0) *
        (axisFam rhoProfile ℓ m c.2.1 (y 1) * axisFam rhoProfile ℓ m c.2.2 (y 2)) ≠ 0 := by
      simpa [cellCut, mul_assoc] using hy
    exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hprod).2).1
  · apply axisFam_support_ext hℓ m c.2.2
    have hprod : axisFam rhoProfile ℓ m c.1 (y 0) *
        (axisFam rhoProfile ℓ m c.2.1 (y 1) * axisFam rhoProfile ℓ m c.2.2 (y 2)) ≠ 0 := by
      simpa [cellCut, mul_assoc] using hy
    exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hprod).2).2

/-- A particle whose coordinate lies outside the extended cell of `j` cannot
be cut off by `ξ_j`. -/
lemma axisFam_eq_zero_of_not_ext {ℓ : ℝ} (hℓ : 0 < ℓ) (m : ℕ) (j : Fin (m + 2))
    {t : ℝ} (ht : t ∉ axisExt ℓ j) : axisFam rhoProfile ℓ m j t = 0 := by
  by_contra h
  exact ht (axisFam_support_ext hℓ m j h)

end BoseGases

end Submission
