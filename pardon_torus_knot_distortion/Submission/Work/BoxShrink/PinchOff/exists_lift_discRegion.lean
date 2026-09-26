import Mathlib
import Submission.Work.BoxShrink.PinchOff.PlaneCover
import Submission.Work.SurgeryInvariance.All
import Submission.Work.Smooth.Jordan.Defs

namespace Work.BoxShrink.PinchOff

/-- **The embedded disc of the surface lifts to the parameter plane.**

The parametrisation `planePsi P : ℂ → R3` is a covering map of the plane onto the surface
`P.carrier` (`isCoveringMap_planeCover`).  The model disc `𝔻` is contractible
(`instContractibleSpaceDisc`), hence simply connected, and locally path connected
(`instLocallyPathConnectedSpaceDisc`).  Therefore every continuous map of `𝔻` into the surface
lifts continuously through the covering, and the lift can be prescribed at one point: the
embedding `D.e : 𝔻 → F` of an embedded disc `D` of the surface has a continuous lift `s` to the
parameter plane with `s w₀ = z₀`, provided `z₀` maps to `D.e w₀`. -/
theorem exists_lift_discRegion
    (P : Work.CoreTopology.ParamTorus) (D : Work.SurgeryInvariance.DiscRegion P)
    (z₀ : ℂ) (w₀ : Work.Smooth.Jordan.Disc)
    (hz : Work.BoxShrink.PinchOff.planePsi P z₀ = D.e w₀) :
    ∃ s : Work.Smooth.Jordan.Disc → ℂ, Continuous s ∧ s w₀ = z₀ ∧
      ∀ w : Work.Smooth.Jordan.Disc, Work.BoxShrink.PinchOff.planePsi P (s w) = D.e w := by
  -- the embedding of the disc, viewed as a continuous map into the surface `P.carrier`
  let f : C(Work.Smooth.Jordan.Disc, P.carrier) :=
    ⟨fun w => ⟨D.e w, D.mem w⟩, D.e.continuous.subtype_mk fun w => D.mem w⟩
  -- the prescribed point `z₀` is a lift of `f w₀`
  have he : planeCover P z₀ = f w₀ := Subtype.ext hz
  -- covering-space lifting theorem, `𝔻` simply connected and locally path connected
  obtain ⟨F, ⟨hF0, hFlift⟩, _⟩ :=
    (isCoveringMap_planeCover P).existsUnique_continuousMap_lifts f w₀ z₀ he
  refine ⟨fun w => F w, F.continuous, hF0, ?_⟩
  intro w
  have h : planeCover P (F w) = f w := congrFun hFlift w
  exact congrArg Subtype.val h

end Work.BoxShrink.PinchOff
