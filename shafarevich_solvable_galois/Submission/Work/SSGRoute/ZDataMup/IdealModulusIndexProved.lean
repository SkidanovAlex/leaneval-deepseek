import Mathlib
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.Defs
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.NKImports
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.ThetaRange
import Submission.Work.SSGRoute.ZDataMup.MupAux.ThetaKerId
import Submission.NK.GlobalCFTdeep.SecondInequality.index_normClassSubgroup_eq_card_rayClassGroup
import Submission.NK.GlobalCFTdeep.SecondInequalitySolvable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Lang's cyclic norm index inequality for an *ideal* modulus (the index half)

For a finite cyclic extension `L/K` of number fields and an ideal modulus `𝔪`,
`[L:K] ≤ [I(𝔪) : P(𝔪)·𝔑(𝔪)]`.

The proof is the idèlic one.  Write `θ : 𝕀 K →* Frac K ⧸ P(𝔪)·𝔑(𝔪)` for the map of
`…/IdealModulus/AdjustId.lean`.  Its kernel is `Kˣ · N_{L/K} 𝕀 L`: the inclusion `⊇` is
`NK.CFTLib.ArtinReciprocityIdeal.principalSubgroup_sup_normImage_le_ker_thetaId`
(`…/IdealModulus/ThetaRange.lean`) and the inclusion `⊆` is
`Work.SSGRoute.ZDataMup.MupAux.thetaId_ker_le_mup` (`…/MupAux/ThetaKerId.lean`, the local–global
argument using the admissibility of `𝔪` and Hasse's norm theorem).  Hence

  `[I(𝔪) : P(𝔪)·𝔑(𝔪)] = [𝕀 K : Kˣ·N 𝕀 L] = [C_K : N C_L] = [L:K]`

by `index_rayNormId_eq_ker_index` (`…/IdealModulus/ThetaRange.lean`),
`index_principalSubgroup_sup_normImage_zdm` and
`NK.GlobalCFTdeep.index_eq_finrank_of_isCyclic`.  Note that the containment
`P(𝔪)·𝔑(𝔪) ≤ I(𝔪)` is *not* needed.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace Work.SSGRoute.ZDataMup

open NK.GlobalCFT

/-- **The index of `Kˣ · N_{L/K} 𝕀 L` in `𝕀 K` is the index of the idèlic norm class subgroup.**
Both are the cardinality of the ray class group `C_K ⧸ N_{L/K} C_L`: by definition the ray class
group `𝕀 K ⧸ (Kˣ ⊔ N_{L/K} 𝕀 L)` is the quotient of `C_K = 𝕀 K ⧸ Kˣ` by `N_{L/K} C_L`. -/
lemma index_principalSubgroup_sup_normImage_zdm {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] :
    (NK.GlobalCFT.Idele.principalSubgroup K ⊔ NK.GlobalCFT.Idele.normImage K L).index =
      (NK.GlobalCFT.Idele.normClassSubgroup K L).index := by
  rw [Subgroup.index_eq_card]
  exact (NK.GlobalCFTdeep.SecondInequality.index_normClassSubgroup_eq_card_rayClassGroup
    (K := K) (L := L)).symm

/-- **Lang's cyclic norm index inequality for an *ideal* modulus (the index half).**

For a finite **cyclic** extension `L/K` of number fields and an ideal modulus
`𝔪 : Ideal (𝓞 K)`, `𝔪 ≠ ⊥`, containing all the primes ramified in `L/K` (`ContainsRamified`) and
admissible (`IsAdmissibleId`):

  `[L:K] ≤ [I(𝔪) : P(𝔪)·𝔑(𝔪)]`.

This is the index inequality half of `…/IdealModulus/langCyclicRelIndexId.lean` (and the ideal-modulus
form of `NK.NUV2.ARL.Gap.langCyclicRelIndex`).  The proof is the idèlic one, and it does *not* need
the containment `P(𝔪)·𝔑(𝔪) ≤ I(𝔪)`: the map `θ : 𝕀 K →* Frac K ⧸ P(𝔪)·𝔑(𝔪)` of
`…/IdealModulus/AdjustId.lean` has kernel `Kˣ · N_{L/K}𝕀 L` (the inclusion `⊆` is
`NK.CFTLib.ArtinReciprocityIdeal.thetaId_ker_le`, `…/IdealModulus/ThetaKer.lean`; the inclusion `⊇`
is `principalSubgroup_sup_normImage_le_ker_thetaId`), so
`[I(𝔪) : P(𝔪)·𝔑(𝔪)] = [𝕀 K : Kˣ·N𝕀 L] = [C_K : N C_L] = [L:K]` by
`index_rayNormId_eq_ker_index` (`…/IdealModulus/ThetaRange.lean`),
`NK.CFTLib.ArtinReciprocityIdeal.index_principalSubgroup_sup_normImage` and
`NK.GlobalCFTdeep.index_eq_finrank_of_isCyclic`. -/
theorem IdealModulusIndexProved
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (𝔪 : Ideal (NumberField.RingOfIntegers K)) (h𝔪 : 𝔪 ≠ ⊥)
    (hram : NK.CFTLib.ArtinReciprocityIdeal.ContainsRamified (K := K) (L := L) 𝔪)
    (hadm : NK.CFTLib.ArtinReciprocityIdeal.IsAdmissibleId (K := K) (L := L) 𝔪) :
    Module.finrank K L ≤
      (NK.CFTLib.ArtinReciprocityIdeal.principalRayId 𝔪 ⊔
        NK.CFTLib.ArtinReciprocityIdeal.normRayId (K := K) (L := L) 𝔪).relIndex
        (NK.CFTLib.ArtinReciprocityIdeal.idealCoprimeGroupId 𝔪) := by
  -- The two inclusions computing the kernel of `θ`: the easy one (`⊇`) and the local–global one
  -- (`⊆`, admissibility of `𝔪` plus Hasse's norm theorem, in the `MupAux` lane).
  have hker_le := MupAux.thetaId_ker_le_mup (K := K) (L := L) h𝔪 hram hadm
  have hker_ge := NK.CFTLib.ArtinReciprocityIdeal.principalSubgroup_sup_normImage_le_ker_thetaId
    (K := K) (L := L) h𝔪
  have hker_eq : (NK.CFTLib.ArtinReciprocityIdeal.thetaId K L 𝔪 h𝔪).ker =
      NK.GlobalCFT.Idele.principalSubgroup K ⊔ NK.GlobalCFT.Idele.normImage K L :=
    le_antisymm hker_le hker_ge
  -- `[L:K] = [𝕀 K : Kˣ·N 𝕀 L] = [𝕀 K : ker θ] = [rayNormClId.subgroupOf I(𝔪) : I(𝔪)]`
  -- `= [I(𝔪) : P(𝔪)·𝔑(𝔪)]`.
  calc Module.finrank K L
      = (NK.GlobalCFT.Idele.normClassSubgroup K L).index :=
        (NK.GlobalCFTdeep.index_eq_finrank_of_isCyclic (K := K) (L := L)).symm
    _ = (NK.GlobalCFT.Idele.principalSubgroup K ⊔ NK.GlobalCFT.Idele.normImage K L).index :=
        (index_principalSubgroup_sup_normImage_zdm (K := K) (L := L)).symm
    _ = (NK.CFTLib.ArtinReciprocityIdeal.thetaId K L 𝔪 h𝔪).ker.index := by rw [hker_eq]
    _ = ((NK.CFTLib.ArtinReciprocityIdeal.rayNormClId K L 𝔪).subgroupOf
          (NK.CFTLib.ArtinReciprocityIdeal.idealCoprimeGroupId 𝔪)).index :=
        (NK.CFTLib.ArtinReciprocityIdeal.index_rayNormId_eq_ker_index
          (K := K) (L := L) h𝔪).symm
    _ = (((NK.CFTLib.ArtinReciprocityIdeal.principalRayId 𝔪 ⊔
          NK.CFTLib.ArtinReciprocityIdeal.normRayId (K := K) (L := L) 𝔪).subgroupOf
          (NK.CFTLib.ArtinReciprocityIdeal.idealCoprimeGroupId 𝔪))).index := by
        rw [NK.CFTLib.ArtinReciprocityIdeal.rayNormClId,
          NK.CFTLib.ArtinReciprocityIdeal.principalRayClId_eq_principalRayId h𝔪]
    _ ≤ (NK.CFTLib.ArtinReciprocityIdeal.principalRayId 𝔪 ⊔
          NK.CFTLib.ArtinReciprocityIdeal.normRayId (K := K) (L := L) 𝔪).relIndex
          (NK.CFTLib.ArtinReciprocityIdeal.idealCoprimeGroupId 𝔪) := le_of_eq rfl

end Work.SSGRoute.ZDataMup
