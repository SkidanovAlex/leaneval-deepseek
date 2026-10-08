import Mathlib
import Submission.Work.Models.Abstract.ModelData
import Submission.Work.Models.Abstract.exists_conj_eq
import Submission.Work.Models.Abstract.modelData_mapEquiv
import Submission.Work.Models.ModelData.psu3ModelData_data
import Submission.Work.Models.ModelData.szModelData
import Submission.Work.Models.ModelData.pSL2ModelData

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageA

/-- **Every strongly embedded subgroup of a simple Bender group is the Borel of some
`ModelData`.**

Let `Y` be a finite group isomorphic to one of `PSL(2, 2ⁿ)`, `Sz(2^(2n+1))`, `PSU(3, 2ⁿ)`
(`IsSimpleBenderGroup Y`), and let `B ≤ Y` be strongly embedded.  Each of the three model
families carries a `ModelData` (`pSL2ModelData`, `szModelData`, `psu3ModelData_data`), and
`modelData_mapEquiv` transports it along the isomorphism `Y ≃*` model, producing some
`ModelData` `P₀` on `Y`.  In a Bender group every strongly embedded subgroup is a conjugate
of the Borel (`exists_conj_eq`), so `B = g P₀.B g⁻¹`; transporting `P₀` along the inner
automorphism `conj g` (`modelData_mapEquiv` applied to `MulAut.conj g`) gives a `ModelData`
whose Borel is exactly `B`. -/
theorem modelDataBorel {Y : Type} [Group Y] [Finite Y]
    (hY : LeanEval.GroupTheory.Defs.IsSimpleBenderGroup Y) {B : Subgroup Y}
    (hB : LeanEval.GroupTheory.Defs.IsStronglyEmbedded B) :
    ∃ P : Work.Models.ModelData Y, P.B = B := by
  -- One `ModelData` on `Y`, obtained by transporting the model data of the family `Y` lies in.
  obtain ⟨P₀⟩ : Nonempty (Work.Models.ModelData Y) := by
    cases hY with
    | isPSL2 n hn e =>
      obtain ⟨P⟩ := Work.Models.ModelData.pSL2ModelData n hn
      obtain ⟨P'⟩ := Work.Models.Abstract.modelData_mapEquiv P e.symm
      exact ⟨P'⟩
    | isSuzuki n hn e =>
      obtain ⟨P⟩ := Work.Models.ModelData.szModelData n hn
      obtain ⟨P'⟩ := Work.Models.Abstract.modelData_mapEquiv P e.symm
      exact ⟨P'⟩
    | isPSU3 n hn e =>
      obtain ⟨P⟩ := Work.Models.ModelData.psu3ModelData_data n hn
      obtain ⟨P'⟩ := Work.Models.Abstract.modelData_mapEquiv P e.symm
      exact ⟨P'⟩
  -- Every strongly embedded subgroup is a conjugate of the Borel of `P₀`.
  obtain ⟨g, hg⟩ := Work.Models.Abstract.exists_conj_eq P₀.toBenderPair hB
  -- Transport `P₀` along the inner automorphism `conj g`; its Borel becomes `B`.
  obtain ⟨P₁, hB₁, _⟩ := Work.Models.Abstract.modelData_mapEquiv P₀ (MulAut.conj g)
  exact ⟨P₁, hB₁.trans hg.symm⟩

end Work.PSU3.StageA
