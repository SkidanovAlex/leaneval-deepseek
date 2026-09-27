import Mathlib

/-!
# The number of `k`-th roots of a nonzero complex number

For `k > 0`, a nonzero `κ : ℂ`, and distinct `u₁ ≠ u`, the set of nonzero solutions
`ζ` of `u₁ + κ * ζ ^ k = u` has exactly `k` elements.  After the substitution
`ζ ^ k = (u - u₁) / κ`, this is the classical fact that a nonzero complex number has
exactly `k` `k`-th roots, which is Mathlib's `nthRootsFinset` together with the
separability of `X ^ k - C c` for `c ≠ 0`.
-/

open Polynomial

namespace Work.EQ

theorem rootSet_ncard {k : ℕ} (hk : 0 < k) {κ : ℂ} (hκ : κ ≠ 0) {u₁ u : ℂ} (hu : u ≠ u₁) :
    {ζ : ℂ | ζ ≠ 0 ∧ u₁ + κ * ζ ^ k = u}.ncard = k := by
  classical
  set c : ℂ := (u - u₁) / κ with hcdef
  have hc : c ≠ 0 := by
    rw [hcdef]
    exact div_ne_zero (sub_ne_zero.mpr hu) hκ
  have hset : {ζ : ℂ | ζ ≠ 0 ∧ u₁ + κ * ζ ^ k = u} = ↑(nthRootsFinset k c) := by
    ext ζ
    simp only [Set.mem_ofPred_eq, Finset.mem_coe]
    rw [mem_nthRootsFinset hk]
    constructor
    · rintro ⟨-, h⟩
      rw [hcdef, eq_div_iff hκ]
      have h' : κ * ζ ^ k = u - u₁ := by rw [← h]; ring
      rw [mul_comm] at h'
      exact h'
    · intro hζ
      refine ⟨?_, ?_⟩
      · intro hz
        rw [hz, zero_pow hk.ne'] at hζ
        exact hc hζ.symm
      · rw [hζ, hcdef, mul_div_cancel₀ _ hκ]
        ring
  rw [hset, Set.ncard_coe_finset]
  have hnodup : (nthRoots k c).Nodup := (Complex.isPrimitiveRoot_exp k hk.ne').nthRoots_nodup hc
  rw [nthRootsFinset_def, Multiset.toFinset_card_of_nodup hnodup]
  rw [nthRoots, IsAlgClosed.card_roots_eq_natDegree, natDegree_X_pow_sub_C]

end Work.EQ
