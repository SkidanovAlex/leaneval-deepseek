import Mathlib
import Submission.Work.Cohomology.cohomologyPairVk
import Submission.Work.Cohomology.RelCapHTransfer
import Submission.Work.Cohomology.sphere3DiscPairDefs
import Submission.Work.Cohomology.Crux.Transgression
import Submission.Work.Cohomology.RelMVLes
import Submission.Work.Cohomology.relMV_shortExact
import Submission.Work.Cohomology.RelCap
import Submission.Work.Cohomology.cap_natural
import Submission.Work.Cohomology.Crux.vk_chartPair_group
import Submission.Work.Milnor.homology_Vk
import Submission.Work.Cohomology.relChainsProjective
import Submission.Work.Cohomology.localHomology
import Submission.Work.Cohomology.relChainsMapOf_isIso
import Submission.Work.Cohomology.exists_relComplexMap

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

namespace Work.Cohomology.Crux

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial
open Work.Cohomology

noncomputable section

/-- The first chart image `U` of `Vk (-2)`. -/
abbrev vkU : Set vkPairX := Set.range (Submission.Milnor.vData (-2)).ιX

/-- The second chart image `V` of `Vk (-2)`. -/
abbrev vkV : Set vkPairX := Set.range (Submission.Milnor.vData (-2)).ιY

theorem vkU_isOpen : IsOpen vkU := (Submission.Milnor.vData (-2)).isOpenEmbedding_ιX.isOpen_range

theorem vkV_isOpen : IsOpen vkV := (Submission.Milnor.vData (-2)).isOpenEmbedding_ιY.isOpen_range

theorem vkU_union_vkV : vkU ∪ vkV = Set.univ :=
  (Submission.Milnor.vData (-2)).range_ιX_union_range_ιY

/-- The overlap `U ∩ V` of the two chart images of `Vk (-2)`, as a topological space. -/
abbrev vkOvl : TopCat := TopCat.of ↥(vkU ∩ vkV)

/-- The trace of the sphere bundle `Mk (-2)` on the overlap. -/
abbrev vkOvlA : Set ↥(vkU ∩ vkV) := {y | (y : vkPairX) ∈ vkPairA}

/-- The canonical relative Mayer--Vietoris short complex of the two-chart cover of `Vk (-2)`. -/
abbrev vkSrel : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  cruxShort vkPairX vkPairA vkU vkV

/-- The small Mayer--Vietoris short complex of the two-chart cover of `Vk (-2)`. -/
abbrev vkSabs : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk (mvLeftSmall vkU vkV) (mvRightSmall vkU vkV) (mvCompSmall vkU vkV)

theorem vkSrel_shortExact : vkSrel.ShortExact :=
  cruxShort_shortExact vkPairX vkPairA vkU vkV

theorem vkSabs_shortExact : vkSabs.ShortExact := mvSmall_shortExact vkU vkV

/-- The homology of the middle term of `vkSabs` vanishes in positive degrees. -/
theorem vkSabs_X₂_homology_isZero (n : ℕ) (hn : 1 ≤ n) :
    IsZero ((smallInChains vkU vkV vkU ⊞ smallInChains vkU vkV vkV).homology n) := by
  apply isZero_homology_biprod
  · haveI h := isIso_smallInToSingA vkU vkV vkU vkU_isOpen vkV_isOpen vkU_union_vkV n
    haveI : ContractibleSpace ↥vkU := Work.Milnor.contractibleSpace_range_ιX (-2)
    exact IsZero.of_iso (homologyContractible n (by omega))
      (asIso (HomologicalComplex.homologyMap (smallInToSingA vkU vkV vkU) n))
  · haveI h := isIso_smallInToSingA vkU vkV vkV vkU_isOpen vkV_isOpen vkU_union_vkV n
    haveI : ContractibleSpace ↥vkV := Work.Milnor.contractibleSpace_range_ιY (-2)
    exact IsZero.of_iso (homologyContractible n (by omega))
      (asIso (HomologicalComplex.homologyMap (smallInToSingA vkU vkV vkV) n))

/-- The absolute Mayer--Vietoris connecting map of the cover is an isomorphism in the degree
needed for the transgression. -/
theorem vkδabs_isIso :
    IsIso (ShortComplex.ShortExact.δ vkSabs_shortExact 4 3 (by simp [ComplexShape.down])) :=
  ShortComplex.ShortExact.isIso_δ vkSabs_shortExact 4 3 (by simp [ComplexShape.down])
    (vkSabs_X₂_homology_isZero 4 (by norm_num))
    (vkSabs_X₂_homology_isZero 3 (by norm_num))

end

end Work.Cohomology.Crux
