import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Star
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Algebra.Order.Ring.Cast
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.BoseRowsL.LatticeCoulomb.maxAbsDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsL.LatticeCoulomb.card_filter_maxAbs_le`

The number of lattice vectors of `ℤ³` with `ℓ^∞`-norm at most `j` is `(2j+1)^3`:
the condition `maxAbs n ≤ j` says exactly that every coordinate of `n` lies in the
integer interval `[-j, j]`, which has `2j+1` elements.  Hence any `Finset` of such
vectors is bounded by `(2j+1)^3`.

This is the counting input for the dyadic slicing of the lattice sum
`∑_{n ≠ 0} 1/(1 + ‖nvec n‖^4)` used in `latticeCoulomb_approx`.
-/

namespace Work.BoseRowsL.LatticeCoulomb

set_option autoImplicit false

/-- The `ℓ^∞`-ball of radius `j` in `ℤ³` is contained in the box `[-j,j]³`, which is a
product of three `(2j+1)`-element interval finsets. -/
lemma maxAbs_filter_subset_box (T : Finset (Fin 3 → ℤ)) (j : ℕ) :
    T.filter (fun n => maxAbs n ≤ j) ⊆
      Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-(j : ℤ)) (j : ℤ)) := by
  intro n hn
  rw [Finset.mem_filter] at hn
  rw [Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  have h : (n i).natAbs ≤ j := (maxAbs_le_iff n j).mp hn.2 i
  have hz : (((n i).natAbs : ℤ)) ≤ (j : ℤ) := by exact_mod_cast h
  constructor
  · have h2 : -(n i) ≤ ((n i).natAbs : ℤ) := by
      simpa using Int.le_natAbs (a := -(n i))
    linarith
  · exact le_trans Int.le_natAbs hz

/-- The box `[-j,j]³` of `ℤ³` has exactly `(2j+1)^3` elements. -/
lemma card_box (j : ℕ) :
    (Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-(j : ℤ)) (j : ℤ))).card
      = (2 * j + 1) ^ 3 := by
  rw [Fintype.card_piFinset]
  simp [Finset.prod_const, Finset.card_univ]
  omega

theorem card_filter_maxAbs_le (T : Finset (Fin 3 → ℤ)) (j : ℕ) :
    (T.filter fun n => Work.BoseRowsL.LatticeCoulomb.maxAbs n ≤ j).card ≤ (2 * j + 1) ^ 3 := by
  calc (T.filter fun n => Work.BoseRowsL.LatticeCoulomb.maxAbs n ≤ j).card
      ≤ (Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-(j : ℤ)) (j : ℤ))).card :=
        Finset.card_le_card (maxAbs_filter_subset_box T j)
    _ = (2 * j + 1) ^ 3 := card_box j

end Work.BoseRowsL.LatticeCoulomb
