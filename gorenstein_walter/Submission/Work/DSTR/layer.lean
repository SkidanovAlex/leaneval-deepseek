import Mathlib
import Submission.Work.DSTR.Defs

namespace Work.DSTR

/-- **LayerProp** (`Work.GW2.LayerProp`): `E(X)` is the unique normal quasisimple subgroup, `Z(E)` is odd, and `E/Z(E)` is `A_7` or `L_2(q)`, `q >= 5`.  Assembled from `DS2`, `DS5`, `DS6`, `DS7` and the `AutL2`/`AutA7` Props. -/
theorem layer (h2 : Work.GW2.OddCoreQuotProp) (h5 : Work.GW2.LayerUniqueProp)
    (h6 : Work.GW2.QuasisimpleCenterOddProp) (h7 : Work.GW2.LayerShapeProp)
    (hautL2 : Work.GW2.AutL2Prop) (hautA7 : Work.GW2.AutA7Prop) :
    Work.GW2.LayerProp := by
  intro X _ _ hFT hSyl hD E hEnorm hEqs
  refine ⟨?_, h6 X hSyl E hEqs, h7 X hFT hSyl hD E hEnorm hEqs⟩
  -- Uniqueness: `E(X)` is the join of the normal quasisimple subgroups of `X`, and by `h5`
  -- every normal quasisimple subgroup of `X` equals `E`.
  show Work.GW2.layer X = E
  rw [Work.GW2.layer]
  apply le_antisymm
  · apply sSup_le
    rintro F ⟨hFnorm, hFqs⟩
    exact le_of_eq (h5 X hFT hSyl F E hFnorm hEnorm hFqs hEqs)
  · exact le_sSup ⟨hEnorm, hEqs⟩

end Work.DSTR
