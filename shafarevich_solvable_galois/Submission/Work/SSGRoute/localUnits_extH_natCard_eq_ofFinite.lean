import Mathlib
import Submission.Work.SSGRoute.ext_localUnits_pTorsion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

theorem localUnits_extH_natCard_eq_ofFinite (k L : Type) [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    Nat.card (SSGRoute.PTExt.extH (SSGRoute.PTExt.localUnitsK (k := k) (NK.GlobalCFT.Place.ofFinite q)) 2)
      = Nat.card (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) := by
  obtain ⟨hcard, -⟩ := eb_loc_card k k L q
  have e := Work.SSGRoute.Bridge.E 2 (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))
    (SSGRoute.PTExt.localUnitsK (k := k) (NK.GlobalCFT.Place.ofFinite q))
  rw [← Nat.card_congr e.toEquiv]
  exact hcard

end Work.SSGRoute
