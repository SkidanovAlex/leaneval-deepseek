/-
Parity invariants of the Apollonian orbit of (-3, 5, 8, 8).

Each S-move replaces one coordinate x by -x + 2*(sum of the others), which
preserves the parity of every coordinate.  Since the base quadruple has odd
coordinates at indices 0,1 and even coordinates at indices 2,3, this index
parity pattern holds throughout the orbit.
-/
import Submission.Apollo.Mod24
import Mathlib.Tactic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
set_option autoImplicit false
open scoped Pointwise
open LocalGlobalApollonianCirclePackings

namespace Apollo

/-- Moving at index i preserves divisibility by 2 of the coordinate at i. -/
lemma dvd2_move_iff (w : Fin 4 → ℤ) (i : Fin 4) : 2 ∣ (gen i • w) i ↔ 2 ∣ w i := by
  rw [gen_smul_apply]
  simp

/-- Moving at index i does not change the coordinates at the other indices. -/
lemma other_coord_eq (w : Fin 4 → ℤ) (i j : Fin 4) (h : j ≠ i) : (gen i • w) j = w j := by
  rw [gen_smul_apply, if_neg h]

/-- An odd coordinate stays odd under any move. -/
lemma odd_preserved (w : Fin 4 → ℤ) (i j : Fin 4) (h : ¬ 2 ∣ w j) : ¬ 2 ∣ (gen i • w) j := by
  intro h2
  by_cases hji : j = i
  · subst j
    exact h ((dvd2_move_iff w i).1 h2)
  · have hw := other_coord_eq w i j hji
    rw [hw] at h2
    exact h h2

/-- An even coordinate stays even under any move. -/
lemma even_preserved (w : Fin 4 → ℤ) (i j : Fin 4) (h : 2 ∣ w j) : 2 ∣ (gen i • w) j := by
  by_cases hji : j = i
  · subst j
    exact (dvd2_move_iff w i).2 h
  · rw [other_coord_eq w i j hji]
    exact h

/-- Coordinates at every index keep their parity through the whole orbit. -/
theorem orbit_parity_pattern (v : Fin 4 → ℤ) (hv : v ∈ apOrbit) :
    ¬ 2 ∣ v 0 ∧ ¬ 2 ∣ v 1 ∧ 2 ∣ v 2 ∧ 2 ∣ v 3 := by
  refine of_closure_apply (P := fun w => ¬ 2 ∣ w 0 ∧ ¬ 2 ∣ w 1 ∧ 2 ∣ w 2 ∧ 2 ∣ w 3) ?hP ?hS v hv
  · -- base
    decide
  · intro i w hw
    exact ⟨odd_preserved w i 0 hw.1, odd_preserved w i 1 hw.2.1,
      even_preserved w i 2 hw.2.2.1, even_preserved w i 3 hw.2.2.2⟩

/-- Indices 0 and 1 are odd throughout the orbit. -/
lemma orbit_odd_zero (v : Fin 4 → ℤ) (hv : v ∈ apOrbit) : ¬ 2 ∣ v 0 :=
  (orbit_parity_pattern v hv).1
lemma orbit_odd_one (v : Fin 4 → ℤ) (hv : v ∈ apOrbit) : ¬ 2 ∣ v 1 :=
  (orbit_parity_pattern v hv).2.1

/-- Indices 2 and 3 are even throughout the orbit. -/
lemma orbit_even_two (v : Fin 4 → ℤ) (hv : v ∈ apOrbit) : 2 ∣ v 2 :=
  (orbit_parity_pattern v hv).2.2.1
lemma orbit_even_three (v : Fin 4 → ℤ) (hv : v ∈ apOrbit) : 2 ∣ v 3 :=
  (orbit_parity_pattern v hv).2.2.2

/-- coordinates at indices 0 and 1 are congruent to 5 mod 8. -/
theorem orbit_odd_coord_eq_five_mod8 (v : Fin 4 → ℤ) (hv : v ∈ apOrbit) (i : Fin 4)
    (hi : i = 0 ∨ i = 1) : v i % 8 = 5 := by
  rcases hi with rfl | rfl
  · have ho : ¬ 2 ∣ v 0 := orbit_odd_zero v hv
    rcases odd_value_eq_five_mod8 v hv 0 ho with ⟨k, hk⟩
    omega
  · have ho : ¬ 2 ∣ v 1 := orbit_odd_one v hv
    rcases odd_value_eq_five_mod8 v hv 1 ho with ⟨k, hk⟩
    omega

/-- coordinates at indices 2 and 3 are congruent to 0 mod 4. -/
theorem orbit_even_coord_eq_zero_mod4 (v : Fin 4 → ℤ) (hv : v ∈ apOrbit) (i : Fin 4)
    (hi : i = 2 ∨ i = 3) : v i % 4 = 0 := by
  rcases hi with rfl | rfl
  · have he : 2 ∣ v 2 := orbit_even_two v hv
    rcases even_value_eq_zero_mod4 v hv 2 he with ⟨k, hk⟩
    omega
  · have he : 2 ∣ v 3 := orbit_even_three v hv
    rcases even_value_eq_zero_mod4 v hv 3 he with ⟨k, hk⟩
    omega

/-- an even coordinate has an even absolute value. -/
lemma even_natAbs_of_even {x : ℤ} (h : 2 ∣ x) : 2 ∣ x.natAbs := by
  rcases h with ⟨t, ht⟩
  rw [ht]
  simp [Int.natAbs_mul]


/-- a coordinate of an orbit quadruple is odd iff its index is 0 or 1. -/
theorem coord_odd_iff (w : Fin 4 → ℤ) (hw : w ∈ apOrbit) (m : Fin 4) :
    (¬ 2 ∣ w m) ↔ m = 0 ∨ m = 1 := by
  fin_cases m <;> simp [orbit_odd_zero w hw, orbit_odd_one w hw,
    orbit_even_two w hw, orbit_even_three w hw]

end Apollo
