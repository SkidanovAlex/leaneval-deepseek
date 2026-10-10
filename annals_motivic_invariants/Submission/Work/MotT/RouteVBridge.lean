import Submission.Work.MotT.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# The bridge to route V (`Submission/Work/MotV`)

Route V works with `K = RatFunc 𝕜`, `D : Work.MotV.KleinData 𝕜`, the twist field
`Work.MotV.twistFieldT D h ⊆ Work.MotV.Om D`, and the fifth root `Work.MotV.root5 h`.  This area
works generically in `(K, h)` with `Work.MotT.twistFieldTK D h ⊆ Work.MotT.OmK D` and
`Work.MotT.root5K h`.

The two constructions are *definitionally* the same at `K = RatFunc 𝕜`, with the base-changed Klein
data `Work.MotT.kleinDataBaseChange D (RatFunc 𝕜)`: the identities below are `rfl`.  Consequently the
generic nodes `Work.MotT.twistFieldTK_descent` (T2), `Work.MotT.twistFieldTK_regular` (T3),
`Work.MotT.twist_iso_pointK` (T4) and `Work.MotT.kleinDataBaseChange_good` (B1) instantiate at route
V with no transport at all.

Everything here is proved outright (no node of this area is needed except `Defs`).
-/

namespace Work.MotT

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine
open scoped WithZero

/-- The chosen fifth roots of route V and of this area agree. -/
theorem root5_eq_root5K {𝕜 : Type} [Field 𝕜] (h : RatFunc 𝕜) :
    Work.MotV.root5 h = root5K h := rfl

/-- The twisted Klein coordinates of route V and of this area agree. -/
theorem twCoord_eq_twCoordK {𝕜 : Type} [Field 𝕜] (D : Work.MotV.KleinData 𝕜) (h : RatFunc 𝕜)
    (i : Fin 5) :
    Work.MotV.twCoord D h i = twCoordK (kleinDataBaseChange D (RatFunc 𝕜)) h i := rfl

/-- **The T-twist fields of route V and of this area agree.**  This is the bridge through which
route V consumes the generic nodes T2/T3/T4. -/
theorem twistFieldT_eq_twistFieldTK {𝕜 : Type} [Field 𝕜] (D : Work.MotV.KleinData 𝕜)
    (h : RatFunc 𝕜) :
    Work.MotV.twistFieldT D h = twistFieldTK (kleinDataBaseChange D (RatFunc 𝕜)) h := rfl

/-- The `AlgEquiv` form of the bridge (for callers who want to transport maps rather than
subfields). -/
theorem twistFieldT_algEquiv {𝕜 : Type} [Field 𝕜] (D : Work.MotV.KleinData 𝕜) (h : RatFunc 𝕜) :
    Nonempty (Work.MotV.twistFieldT D h ≃ₐ[RatFunc 𝕜]
      twistFieldTK (kleinDataBaseChange D (RatFunc 𝕜)) h) :=
  ⟨IntermediateField.equivOfEq (twistFieldT_eq_twistFieldTK D h)⟩

end

end Work.MotT
