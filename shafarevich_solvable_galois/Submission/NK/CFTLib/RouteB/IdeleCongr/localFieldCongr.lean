import Mathlib
import Submission.NK.CFTLib.RouteB.IdeleCongr.PlaceCongr
import Submission.NK.GlobalCFTdeep.Transport.NormTransportAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.CFTLib.RouteB.IdeleCongr

open NK.GlobalCFT

/-- **Transport of the local fields along an isomorphism of number fields.**

The canonical transport of local fields along the ring equivalence underlying `e : L ≃ₐ[K] L'`
(`NK.GlobalCFTdeep.Transport.NormTransport.localFieldIso`) is compatible with the structure
maps `algebraMap L L_v`, carries the local units at `v` onto the local units at
`Place.congr e v`, and is continuous. -/
theorem localFieldCongr {K L L' : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Field L'] [NumberField L'] [Algebra K L] [Algebra K L'] (e : L ≃ₐ[K] L') :
    ∃ Φ : (v : NK.GlobalCFT.Place L) →
        NK.GlobalCFT.Place.localField L v ≃+*
          NK.GlobalCFT.Place.localField L' (NK.GlobalCFT.Place.congr e v),
      (∀ (v : NK.GlobalCFT.Place L) (x : L),
        Φ v (algebraMap L (NK.GlobalCFT.Place.localField L v) x) =
          algebraMap L'
            (NK.GlobalCFT.Place.localField L' (NK.GlobalCFT.Place.congr e v)) (e x)) ∧
      (∀ (v : NK.GlobalCFT.Place L) (u : (NK.GlobalCFT.Place.localField L v)ˣ),
        u ∈ NK.GlobalCFT.Place.localUnits L v ↔
          Units.map (Φ v).toMonoidHom u ∈
            NK.GlobalCFT.Place.localUnits L' (NK.GlobalCFT.Place.congr e v)) ∧
      (∀ v : NK.GlobalCFT.Place L, Continuous (Φ v)) := by
  refine ⟨fun v =>
    NK.GlobalCFTdeep.Transport.NormTransport.localFieldIso e.toRingEquiv v, ?_, ?_, ?_⟩
  · intro v x
    exact NK.GlobalCFTdeep.Transport.NormTransport.localFieldIso_algebraMap
      e.toRingEquiv v x
  · intro v u
    exact NK.GlobalCFTdeep.Transport.NormTransport.localFieldIso_localUnits
      e.toRingEquiv v u
  · intro v
    exact NK.GlobalCFTdeep.Transport.NormTransport.localFieldIso_continuous
      e.toRingEquiv v

end NK.CFTLib.RouteB.IdeleCongr
