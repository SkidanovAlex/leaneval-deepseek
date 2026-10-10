import Mathlib.FieldTheory.KrullTopology
import Submission.NK.LocalTame.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.TameStructure.ProfiniteAux

open scoped Pointwise

/-- For an integral field extension `K'/κ` (so in particular algebraic, hence every element of
`K'` is integral over `κ`), the subgroup of `Gal(K'/κ)` fixing an intermediate field `F` pointwise
is closed for the Krull topology.

Indeed `Gal(K'/F)` is the intersection, over the elements `x ∈ F`, of the stabilizers of `x`;
each stabilizer is *open* since `x` is integral over `κ`
(`InfiniteGalois.stabilizer_isOpen_of_isIntegral`), hence closed because it is a subgroup. -/
theorem fixingSubgroup_isClosed_of_isIntegral {κ K' : Type*} [Field κ] [Field K'] [Algebra κ K']
    [Algebra.IsIntegral κ K'] (F : IntermediateField κ K') :
    IsClosed (F.fixingSubgroup : Set (Gal(K'/κ))) := by
  have h : (F.fixingSubgroup : Set Gal(K'/κ)) =
      ⋂ x : F, (MulAction.stabilizer Gal(K'/κ) (x : K') : Set Gal(K'/κ)) := by
    ext σ
    simp only [Set.mem_iInter, SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff,
      MulAction.mem_stabilizer_iff]
    constructor
    · intro hσ x
      simpa using hσ x x.2
    · intro hσ x hx
      exact hσ ⟨x, hx⟩
  rw [h]
  exact isClosed_iInter fun x =>
    Subgroup.isClosed_of_isOpen _ (stabilizer_isOpen_of_isIntegral (x : K'))

end NK.TameStructure.ProfiniteAux
