import Mathlib
import Submission.NK.GlobalCFTdeep.Herbrand.SIdeles
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.GlobalCFTdeep.Herbrand

open NK.GlobalCFT
open scoped NumberField RestrictedProduct

/-- Every idèle which is a local unit at every finite place is a `T`-idèle: outside `T` a place
is either finite, where integrality supplies the required unit, or archimedean, where the local
units are everything. -/
theorem integralIdeles_le_TIdeles {L : Type} [Field L] [NumberField L] (T : Set (NK.GlobalCFT.Place L)) :
    NK.GlobalCFT.Idele.integralIdeles L ≤ TIdeles T := by
  intro x hx w hw
  by_cases h : Place.IsFinite w
  · exact Idele.mem_integralIdeles.mp hx w h
  · obtain ⟨w', rfl⟩ := Place.isInfinite_iff.mp (not_not.mp h)
    exact Place.mem_localUnits_ofInfinite

end NK.GlobalCFTdeep.Herbrand
