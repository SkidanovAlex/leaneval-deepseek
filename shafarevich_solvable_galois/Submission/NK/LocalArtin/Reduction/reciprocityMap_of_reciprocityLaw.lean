import Mathlib.FieldTheory.Galois.Basic
import Submission.NK.LocalArtin.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalArtin.Reduction

/-- **The single-map form of the reciprocity law from the compatible-family form.**

`NK.LocalCFT.ReciprocityLaw F F'` supplies, at every finite abelian Galois level `L ≤ F^{ab}`, an
isomorphism `Fˣ ⧸ N_{L/F} Lˣ ≃* Gal(L/F)`, compatibly with the restriction maps between levels.
Because `Gal(F^{ab}/F)` is the inverse limit of the finite levels
(`InfiniteGalois.mulEquivToLimit`), a compatible family of level maps *is* a single homomorphism
`artin : Fˣ →* Gal(F^{ab}/F)`; this is the Artin map
`NK.LocalCFT.Reduction.artinMap` constructed in `NK.LocalCFT`, and its level restrictions are
the given level isomorphisms (`NK.LocalCFT.Reduction.artinMap_restrict`).  Hence a reciprocity law
gives a `ReciprocityMap`. -/
theorem reciprocityMap_of_reciprocityLaw {F : Type*} {F' : Type*} [Field F] [Field F']
    [Algebra F F'] [IsGalois F F'] (hlaw : NK.LocalCFT.ReciprocityLaw F F') :
    Nonempty (NK.LocalArtin.ReciprocityMap F F') := by
  refine ⟨{ artin := NK.LocalCFT.Reduction.artinMap hlaw, isLevelIso := ?_ }⟩
  intro L hfd hnorm hcomm
  have heq : (NK.LocalArtin.levelRestrict L).comp
        (NK.LocalCFT.Reduction.artinMap hlaw) =
      (hlaw.levelEquiv L hcomm).toMonoidHom.comp
        (QuotientGroup.mk' (NK.LocalArtin.normGroup F ↥L)) := by
    refine MonoidHom.ext fun x => ?_
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    exact NK.LocalCFT.Reduction.artinMap_restrict hlaw x L hcomm
  constructor
  · rw [heq]
    exact (hlaw.levelEquiv L hcomm).surjective.comp (QuotientGroup.mk'_surjective _)
  · rw [heq, MonoidHom.ker_comp_of_injective _ _ (hlaw.levelEquiv L hcomm).injective,
      QuotientGroup.ker_mk']

end NK.LocalArtin.Reduction
