/-
# `Work.PSU3.PSU3DatumProp` is proved

Design node D1 (`psu3_datum`, the `frel` half of which comes from
`Work.PSU3.Model.weylConj_matFun`, its split datum from
`Work.PSU3.Model.psu3_isSplitRankOne`, and its coordination from
`Work.PSU3.pglHom_injective`) gives the area's `PSU3DatumProp` for every `n ≥ 2`.
-/
import Submission.Work.PSU3.psu3Prop_of
import Submission.Work.PSU3.Model.psu3_datum

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

namespace Work.PSU3

/-- **Design node D1 for all `n`:** `PSU3Model n` carries a `ModelRankOneDatum` with
coordinates `(SZ (E n), fMapTot)`. -/
theorem psu3DatumProp_holds : PSU3DatumProp := fun n hn => Model.psu3_datum n hn

/-- **`PSU3Prop` from Stage A–C alone.**  The Stage D half is now proved
(`Work.PSU3.psu3DatumProp_holds`), so the area theorem needs only the coordinatisation
`PSU3CoordsProp` (`psu3_coords`) besides the two external Props. -/
theorem psu3Prop_of_coords (hC4 : Submission.Blueprint.ChIIFourProp)
    (hHig : Submission.Blueprint.HigmanProp) (hCoords : PSU3CoordsProp) :
    Submission.Blueprint.PSU3Prop :=
  psu3Prop_of hC4 hHig hCoords psu3DatumProp_holds

end Work.PSU3
