import Mathlib
import Submission.NK.LocalStructure.Defs

namespace NK.LocalStructure.Tower

/-- **The `p`-tower rank is unbounded when the finite `p`-power extensions have
unboundedly many degree-`p` extensions.**

`HasUnboundedTowerRank p Gal(K'/κ)` asks for finite-index subgroups `V ≤ Gal(K'/κ)` of
`p`-power index with unboundedly many index-`p` subgroups.  Given `htower`, take `V` to be
the fixing subgroup of an intermediate field `M` of `p`-power degree — it has index
`[M : κ] = p ^ e` — and identify the index-`p` subgroups of `V` with those of
`Gal(K'/M)` through the Galois correspondence (`IntermediateField.fixingSubgroupEquiv`). -/
theorem hasUnboundedTowerRank_of_numIndexSubgroups_tower {κ K' : Type*} [Field κ]
    [Field K'] [Algebra κ K'] [IsGalois κ K'] {p : ℕ} (hp : p.Prime)
    (htower : ∀ N : ℕ, ∃ (M : IntermediateField κ K') (e : ℕ),
      Module.finrank κ M = p ^ e ∧
      N < Nat.card {H : Subgroup (Gal(K'/↥M)) // H.index = p}) :
    NK.LocalAnabelian.HasUnboundedTowerRank p (Gal(K'/κ)) := by
  intro N
  obtain ⟨M, e, hdeg, hN⟩ := htower N
  have hindex := IntermediateField.finrank_eq_fixingSubgroup_index (F := κ) (E' := K') M
  refine ⟨M.fixingSubgroup, ?_, ⟨e, hindex.symm.trans hdeg⟩, ?_⟩
  · rw [Subgroup.finiteIndex_iff, hindex.symm.trans hdeg]
    exact pow_ne_zero e hp.ne_zero
  · rw [NK.LocalAnabelian.numIndexSubgroups_congr
      (IntermediateField.fixingSubgroupEquiv M) p]
    exact hN

end NK.LocalStructure.Tower
