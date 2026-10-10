import Mathlib
import Submission.Work.Twist.Defs
import Submission.Work.Twist.ExtIsoTransport

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Twist

open CategoryTheory AlgebraicGeometry
open Work.Twist

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

open Work.Twist.ExtIsoTransport

/-- **The transport of a curve model.**  A `TwistCurveModel` of the twist at `L` is one at `L'`:
the *scheme* `C` and the five geometric fields of the model do not involve the extension at all,
and the two descent bridges are rewritten by `hasPoint_iff_of_extIso` and
`divisorOfDegree_iff_of_extIso` (`Submission/Work/Twist/ExtIsoTransport.lean`). -/
def realizationTransport (𝕜 : Type) [Field 𝕜] [DecidableEq 𝕜]
    (C₅ : FiveTorsionCurve 𝕜) {L L' : CyclicExtension 𝕜 5} (e : ExtIso L L')
    (M : TwistCurveModel (quinticTwistOf C₅ L)) : TwistCurveModel (quinticTwistOf C₅ L') where
  C := M.C
  variety := M.variety
  isProper := M.isProper
  isSmooth := M.isSmooth
  isGeomIntegral := M.isGeomIntegral
  dim_eq_one := M.dim_eq_one
  hasPoint_iff := M.hasPoint_iff.trans (hasPoint_iff_of_extIso e)
  divisorOfDegree_iff := fun n =>
    (M.divisorOfDegree_iff n).trans (divisorOfDegree_iff_of_extIso e n)

/-- **The realization of a quintic twist does not depend on the model of the cyclic extension.**
With `ExtIso L L'` as in `Submission/Work/Twist/Defs.lean`, the twist of a fixed `FiveTorsionCurve`
by `L` is realized by a curve model if and only if the twist by `L'` is.

`RealizationOf C₅ L` is `Nonempty (TwistCurveModel (quinticTwistOf C₅ L))` — a *scheme* `C` together
with the two descent bridges; the geometry fields of the model mention only the scheme (which does
not depend on `L`), while the bridges only mention the class of the twist in
`H¹(ℤ/5, E(L)) = ker N/(σ - 1)E(L)`, which is carried to the class of the twist of `L'` by
`Point.map e : E(L) ≃+ E(L')` (`Point.map_map` with `ExtIso.gen_eq`, and `Point.map_baseChange` for
the marked point `PL`).  So a model for one twist gives one for the other, with the bridge
conditions rewritten by that transport.

This is the well-posedness of the geometric residual with respect to the *choice of the
extension*; for the choice of generator inside a fixed extension see `twistCurveModelOfPow`. -/
theorem realizationOf_iff_of_extIso {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (C₅ : FiveTorsionCurve 𝕜) {L L' : CyclicExtension 𝕜 5} (e : ExtIso L L') :
    RealizationOf C₅ L ↔ RealizationOf C₅ L' := by
  constructor
  · rintro ⟨M⟩
    exact ⟨realizationTransport 𝕜 C₅ e M⟩
  · rintro ⟨M⟩
    exact ⟨realizationTransport 𝕜 C₅ e.symm M⟩

end

end Work.Twist
