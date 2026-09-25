import Mathlib
import Submission.NK.CFTLib.HR.TransferAux.Defs
import Submission.NK.CFTLib.HR.transferAt
import Submission.NK.CFTLib.IdeleHasse.Descent.transferLevels
import Submission.NK.CFTLib.IdeleHasse.Descent.localNormSubgroup_iff_cycClass_finite
import Submission.NK.CFTLib.IdeleHasse.Descent.localNormSubgroup_iff_cycClass_infinite
import Submission.NK.GlobalCFTdeep.HasseNormTheorem
import Submission.NK.GlobalCFTdeep.NormIndex.localNormAt
import Submission.NK.NUV2.ARL.HR.TransferSupport

/-!
# Definitions for the Brauer transfer at one pair of cyclic levels

The transfer `cycClassOf_eq_zero_of_transfer` uses the following vocabulary.

* `NK.NUV2.ChebAux.Transfer.resToGal`: the restriction `H²(Gal(E/K), Eˣ) → H²(Gal(E/M), Eˣ)`
  along the inclusion `Gal(E/M) ↪ Gal(E/K)`, in the `unitsRep`-vocabulary so that it composes
  with the localisations `NK.HassePrinciple.locUnits`.
* `NK.NUV2.ARL.HR.inflation` (imported): the level inflation
  `H²(Gal(L/K), Lˣ) → H²(Gal(E/K), Eˣ)`.
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open NK.GlobalCFT CategoryTheory

namespace NK.NUV2.ChebAux.Transfer

/-- **The restriction `H²(Gal(E/K), Eˣ) → H²(Gal(E/M), Eˣ)`** along the inclusion of the subgroup
`Gal(E/M) ↪ Gal(E/K)`. -/
noncomputable def resToGal (K M E : Type) [Field K] [Field M] [Field E] [Algebra K M]
    [Algebra K E] [Algebra M E] [IsScalarTower K M E] :
    groupCohomology (NK.HassePrinciple.unitsRep K E) 2 ⟶
      groupCohomology (NK.HassePrinciple.unitsRep M E) 2 :=
  (groupCohomology.resNatTrans NK.HassePrinciple.CoeffInt
    (NK.NUV2.ARL.HR.inclMK (K := K) (M := M) (E := E)) 2).app
      (NK.HassePrinciple.unitsRep K E)

end NK.NUV2.ChebAux.Transfer
