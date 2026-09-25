import Mathlib
import Submission.NK.LocalCFT.Basic
import Submission.NK.LocalCFT.Functoriality.levelMulEquiv_restrict
import Submission.NK.LocalCFT.Reduction.Defs

/-!
# The reciprocity law from the Artin reciprocity datum

Given the canonical Artin reciprocity datum `D : NK.LocalCFT.ArtinReciprocity F F'`
(the Artin map `Fˣ →* Gal(F^{ab}/F)` together with the level-wise reciprocity isomorphisms
and the existence theorem), we build the *canonical (compatible) form* of the reciprocity
law `NK.LocalCFT.ReciprocityLaw F F'`: the level-wise isomorphisms are simply the ones
induced by `D.artin` (`NK.LocalCFT.ArtinReciprocity.artinLevelMulEquiv`), and the
compatibility with restriction between levels is the functoriality statement
`NK.LocalCFT.Functoriality.levelMulEquiv_restrict`, whose mathematical content is the
transitivity of `AlgEquiv.restrictNormalHom`.
-/

open scoped Classical

namespace NK.LocalCFT.Reduction

universe u v

theorem reciprocityLaw_of_artinReciprocity {F : Type u} {F' : Type v} [Field F] [Field F']
    [Algebra F F'] [IsGalois F F'] (D : NK.LocalCFT.ArtinReciprocity F F') :
    Nonempty (NK.LocalCFT.ReciprocityLaw F F') := by
  refine ⟨{ levelEquiv := fun L _ _ hcomm => D.artinLevelMulEquiv L hcomm, compat := ?_ }⟩
  intro L₁ L₂ _ _ _ _ h₁ h₂ h x
  -- The norm-group quotient map sends the class of `x` to the class of `x`.
  have hmap : ∀ (hle : NK.LocalReciprocity.normGroup F ↥L₁ ≤
      NK.LocalReciprocity.normGroup F ↥L₂),
      QuotientGroup.map (NK.LocalReciprocity.normGroup F ↥L₁)
        (NK.LocalReciprocity.normGroup F ↥L₂) (MonoidHom.id Fˣ) hle (QuotientGroup.mk x) =
        QuotientGroup.mk x := by
    intro hle
    exact QuotientGroup.map_mk _ _ _ hle x
  rw [hmap (NK.LocalCFT.normGroup_le_of_le h)]
  -- Both sides are the image of `x` under `artin`, restricted to `L₁` resp. `L₂`.
  rw [NK.LocalCFT.ArtinReciprocity.artinLevelMulEquiv_mk,
    NK.LocalCFT.ArtinReciprocity.artinLevelMulEquiv_mk]
  exact NK.LocalCFT.Functoriality.levelRestrictLe_comp_levelRestrict h (D.artin x)

end NK.LocalCFT.Reduction
