/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Monotonicity of the number of index-`ℓ` subgroups

For a commutative group `G` and a finite index subgroup `V ≤ G`, the number of subgroups of
`V` of index `ℓ` is at most the number of subgroups of `G` of index `ℓ`.

The proof reduces to the additive statement
`NK.LocalCFT.Units.EllRank.natCard_projectivization_ellDual_le_of_finiteIndex` via the
translation between `numIndexSubgroups` and `nIdx` and the identification of the index-`ℓ`
subgroups with the points of the projectivization of the dual of `A ⧸ ℓA`
(`NK.LocalCFT.Units.EllRank.nIdx_eq_natCard_projectivization`).
-/
import Mathlib
import Submission.NK.LocalAnabelian.Basic
import Submission.NK.LocalCFT.Units.EllRank.Defs
import Submission.NK.LocalCFT.Units.EllRank.nIdx_eq_natCard_projectivization
import Submission.NK.LocalCFT.Units.EllRank.natCard_projectivization_ellDual_le_of_finiteIndex
import Submission.NK.LocalCFT.Units.numIndexSubgroups_eq_nIdx
import Submission.NK.LocalCFT.Units.numIndexSubgroups_eq_nIdx_subtype

open scoped LinearAlgebra.Projectivization

namespace NK.LocalCFT.Units

theorem numIndexSubgroups_le_of_commutative {G : Type*} [Group G]
    (hcomm : ∀ x y : G, x * y = y * x) (V : Subgroup G) (hV : V.FiniteIndex)
    (ℓ : ℕ) (hℓ : ℓ.Prime) :
    NK.LocalAnabelian.numIndexSubgroups ℓ V ≤ NK.LocalAnabelian.numIndexSubgroups ℓ G := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  letI : CommGroup G := { ‹Group G› with mul_comm := hcomm }
  have hV' : V.toAddSubgroup.FiniteIndex := Subgroup.finiteIndex_toAddSubgroup_iff.mpr hV
  rw [numIndexSubgroups_eq_nIdx_subtype ℓ G V, numIndexSubgroups_eq_nIdx ℓ G]
  rw [EllRank.nIdx_eq_natCard_projectivization (ℓ := ℓ) ↥(V.toAddSubgroup),
    EllRank.nIdx_eq_natCard_projectivization (ℓ := ℓ) (Additive G)]
  exact EllRank.natCard_projectivization_ellDual_le_of_finiteIndex (ℓ := ℓ) V.toAddSubgroup hV'

end NK.LocalCFT.Units
