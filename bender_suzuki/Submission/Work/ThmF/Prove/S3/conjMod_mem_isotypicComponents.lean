import Mathlib
import Submission.Work.ThmF.Prove.S3.clifford_setup
import Submission.Work.ThmF.Prove.S3.conjModBase

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.Prove.S3

theorem conjMod_mem_isotypicComponents {L : Type*} [Group L] {F : Type*} [Field F]
    {K : Subgroup L} {V : Type*} [AddCommGroup V] [Module F V]
    (hKn : K.Normal) (ρ : Representation F L V) (e : L)
    {C : Submodule (MonoidAlgebra F K) (resRep (K := K) ρ).asModule}
    (hC : C ∈ isotypicComponents (MonoidAlgebra F K) (resRep (K := K) ρ).asModule) :
    conjMod hKn ρ e C ∈ isotypicComponents (MonoidAlgebra F K)
      (resRep (K := K) ρ).asModule := by
  obtain ⟨S, hS, hCeq⟩ := hC
  refine ⟨conjMod hKn ρ e S, (isSimpleModule_conjMod_iff hKn ρ e S).mpr hS, ?_⟩
  rw [hCeq, conjMod_isotypicComponent]

end Work.ThmF.Prove.S3
