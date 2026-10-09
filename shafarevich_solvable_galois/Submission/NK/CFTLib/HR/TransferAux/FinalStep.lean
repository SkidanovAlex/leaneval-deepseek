import Mathlib
import Submission.NK.CFTLib.IdeleHasse.localNormSubgroup
import Submission.NK.CFTLib.IdeleHasse.localFaithfulDefs
import Submission.NK.CFTLib.IdeleHasse.Descent.transferLevels
import Submission.NK.CFTLib.IdeleHasse.Descent.localNormSubgroup_iff_cycClass_finite
import Submission.NK.CFTLib.IdeleHasse.Descent.localNormSubgroup_iff_cycClass_infinite
import Submission.NK.GlobalCFTdeep.NormIndex.localNormAt
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

open scoped NumberField
open NumberField IsDedekindDomain NK.GlobalCFT

namespace NK.CFTLib.HR.TransferAux

/-- **The elementary final step of the Brauer transfer**: if the cyclic class of `x` at the cyclic
level `L/K` vanishes, then `x` is a local norm at `v₀`.

Proof: the localisation dictionary at any place `w` of `L` above `v₀` (finite or archimedean)
turns the vanishing of the localisation of the cyclic class into membership of `localImageAt v₀ x`
in the local norm subgroup; the localisation of the zero class is zero. -/
theorem finalStep {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (hcycL : IsCyclic (L ≃ₐ[K] L)) (x : Kˣ) (v₀ : NK.GlobalCFT.Place K)
    (hclass : ∀ (g : L ≃ₐ[K] L) (hg : ∀ σ : L ≃ₐ[K] L, σ ∈ Subgroup.zpowers g),
      NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := K) (F := L) g hg x = 0) :
    NK.CFTLib.IdeleHasse.localImageAt v₀ x ∈
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v₀ := by
  obtain ⟨g, hg⟩ := hcycL.exists_generator
  obtain ⟨w, hw⟩ := NK.GlobalCFTdeep.NormIndex.exists_place_liesOver (K := K) (L := L) v₀
  have h0 : (NK.HassePrinciple.locUnits K L (w : NK.GlobalCFT.Place L)).hom
      (NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := K) (F := L) g hg x) = 0 := by
    rw [hclass g hg]
    exact map_zero _
  rcases hw with ⟨w', v', rfl, rfl, hw'⟩ | ⟨q, Q, rfl, rfl, hq⟩
  · exact (NK.CFTLib.IdeleHasse.Descent.localNormSubgroup_iff_cycClass_infinite
      (K := K) (F := L) g hg v' w' hw' x).mp h0
  · exact (NK.CFTLib.IdeleHasse.Descent.localNormSubgroup_iff_cycClass_finite
      (K := K) (F := L) g hg Q q hq x).mp h0

end NK.CFTLib.HR.TransferAux
