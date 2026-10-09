import Mathlib
import Submission.Work.SSGRoute.NKExistenceImport
import Submission.Work.SSGRoute.NKGlobalImport
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataMup

set_option linter.style.haveILetI false

/-- **The global Artin reciprocity law in idèle-class-group form, for abelian extensions.**

`NK.GlobalCFT.ArtinReciprocity K L` is the structure whose single field is the reciprocity
isomorphism `C_K ⧸ N_{L/K} C_L ≃* Gal(L/K)`.  It is the *idèle-theoretic* form of the reciprocity
law; the workspace's proved `NK.CFTLib.artinReciprocityIdeal_proved` is the *ideal-theoretic* form
(Lang's `ArtinReciprocityIdeal`), and what is asked here is the passage between them for abelian
`L/K` (equivalently: the well-definedness of the Artin map on the idèle class group, with kernel the
norm class subgroup).  It is a short corollary of
`NK.NUV2.artinFrobeniusInputFree_of_artinReciprocityIdeal` (proved) instantiated with
`NK.CFTLib.artinReciprocityIdeal_proved`, or of
`NK.GlobalCFTdeep.artinReciprocity_of_fundamentalClassElement`. -/
theorem nonempty_artinReciprocity_of_abelian (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a) :
    Nonempty (NK.GlobalCFT.ArtinReciprocity K L) := by
  -- commutativity of `Gal(L/K)` as a typeclass instance
  haveI : IsMulCommutative (L ≃ₐ[K] L) := IsMulCommutative.of_comm hcomm
  -- the idèle-theoretic reciprocity datum produced by the ideal-theoretic reciprocity law
  obtain ⟨h, -⟩ := NK.NUV2.artinFrobeniusInputFree_of_artinReciprocityIdeal
    NK.CFTLib.artinReciprocityIdeal_proved K L
  exact ⟨h⟩

end Work.SSGRoute.ZDataMup
