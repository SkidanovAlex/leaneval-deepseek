import Mathlib
import Submission.NK.LocalAnabelian.Basic

namespace NK.LocalAnabelian.GaloisCorrespondence

open IntermediateField

/-- **The Galois correspondence of infinite Galois theory preserves the index**:
a closed subgroup of `Gal(K'/k)` has index `p` if and only if the corresponding
intermediate field has degree `p` over `k`.  Consequently the closed subgroups of
index `p` are in bijection with the intermediate fields of degree `p`. -/
theorem numIndexClosedSubgroups_eq_natCard_finrank_eq {k K' : Type*} [Field k] [Field K']
    [Algebra k K'] [IsGalois k K'] (p : ℕ) :
    Nat.card {H : ClosedSubgroup (Gal(K'/k)) // (H : Subgroup Gal(K'/k)).index = p} =
      Nat.card {L : IntermediateField k K' // Module.finrank k L = p} := by
  -- The order-reversing Galois correspondence `L ↦ Gal(K'/L)`, with inverse
  -- `H ↦ (K')^H`, gives a bijection of the two underlying types.
  let Φ := InfiniteGalois.IntermediateFieldEquivClosedSubgroup (k := k) (K := K')
  let e : ClosedSubgroup (Gal(K'/k)) ≃ IntermediateField k K' :=
    { toFun := fun H => Φ.symm (OrderDual.toDual H)
      invFun := fun L => OrderDual.ofDual (Φ L)
      left_inv := by intro H; simp
      right_inv := by intro L; simp }
  refine Nat.card_congr (Equiv.subtypeEquiv e ?_)
  -- The key point: for `L` an intermediate field, `[L : k] = (Gal(K'/L) : Gal(K'/k))`.
  intro H
  have h1 : e H = IntermediateField.fixedField (H : Subgroup Gal(K'/k)) := rfl
  have hfix : Module.finrank k (e H) = (H : Subgroup Gal(K'/k)).index := by
    rw [h1, IntermediateField.finrank_eq_fixingSubgroup_index,
      InfiniteGalois.fixingSubgroup_fixedField H]
  simp only [hfix]

end NK.LocalAnabelian.GaloisCorrespondence
