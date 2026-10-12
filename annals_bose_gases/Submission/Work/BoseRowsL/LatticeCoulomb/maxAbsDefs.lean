import Mathlib.Order.Lattice.Nat
import Mathlib.Algebra.Ring.Int.Defs
import Submission.Work.BoseRowsL.LatticeCoulomb.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsL.LatticeCoulomb.maxAbsDefs` — the `ℓ^∞` lattice norm of `ℤ³`

The `ℓ^∞`-norm `maxAbs n = max_i |n_i|` of an integer vector `n : Fin 3 → ℤ`, together
with its elementary API.  It is the tool used to bound the lattice sum
`∑_{n ≠ 0} 1/(1 + ‖nvec n‖^4)`: for a nonzero lattice vector `‖nvec n‖ ≥ maxAbs n ≥ 1`, so
that the sum can be sliced into the dyadic blocks `{2^k ≤ maxAbs n < 2^{k+1}}`; the `k`-th
block contains at most `(2^{k+2})³` points of `ℤ³` while each of them carries weight at most
`(1/2)^{4k}`, giving the geometric bound `∑_k 2^{6-k} = 128`.
-/

namespace Work.BoseRowsL.LatticeCoulomb

set_option autoImplicit false

/-- The `ℓ^∞`-norm of a lattice vector: the maximum of the absolute values of its coordinates. -/
def maxAbs (n : Fin 3 → ℤ) : ℕ := (Finset.univ : Finset (Fin 3)).sup fun i => (n i).natAbs

lemma maxAbs_le_iff (n : Fin 3 → ℤ) (j : ℕ) :
    maxAbs n ≤ j ↔ ∀ i : Fin 3, (n i).natAbs ≤ j := by
  simp [maxAbs, Finset.sup_le_iff]

lemma le_maxAbs (n : Fin 3 → ℤ) (i : Fin 3) : (n i).natAbs ≤ maxAbs n := by
  rw [maxAbs]
  exact Finset.le_sup (f := fun i => (n i).natAbs) (Finset.mem_univ i)

lemma maxAbs_eq_zero_iff (n : Fin 3 → ℤ) : maxAbs n = 0 ↔ n = 0 := by
  constructor
  · intro h
    funext i
    have h0 : (n i).natAbs ≤ 0 := (maxAbs_le_iff n 0).mp (by rw [h]) i
    exact Int.natAbs_eq_zero.mp (Nat.le_zero.mp h0)
  · rintro rfl
    refine Finset.sup_eq_bot_iff _ _ |>.mpr ?_
    intro i _
    simp

lemma maxAbs_nonneg (n : Fin 3 → ℤ) : 0 ≤ maxAbs n := Nat.zero_le _

end Work.BoseRowsL.LatticeCoulomb
