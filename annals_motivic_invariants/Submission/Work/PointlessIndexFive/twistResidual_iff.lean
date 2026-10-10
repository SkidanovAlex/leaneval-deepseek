import Mathlib
import Submission.Work.PointlessIndexFive.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.PointlessIndexFive

/-! ## The `DecidableEq` artefact is proof-irrelevant

`HasPointlessTwist 𝕜` and `TwistRealization 𝕜` both take a `DecidableEq 𝕜` instance, purely
because Mathlib's group law on affine points of a Weierstrass curve needs one
(`WeierstrassCurve.Affine.Point.instAddCommGroup`).  Since `Decidable` is a subsingleton, so is
`DecidableEq 𝕜`, and therefore the two halves are the same `Prop` for every choice of instance.
The two lemmas below record this; they are what lets `TwistResidual` — which existentially
quantifies the artefact — be replaced by the two halves at a *fixed* instance. -/

/-- A `DecidableEq 𝕜` instance is unique. -/
theorem subsingleton_decidableEq (𝕜 : Type) : Subsingleton (DecidableEq 𝕜) := inferInstance

/-- The geometric half does not depend on the `DecidableEq 𝕜` instance. -/
theorem twistRealization_decEq_irrel {𝕜 : Type} [Field 𝕜] (d e : DecidableEq 𝕜) :
    @TwistRealization 𝕜 _ d = @TwistRealization 𝕜 _ e :=
  congrArg (fun x => @TwistRealization 𝕜 _ x) (Subsingleton.elim d e)

/-- The arithmetic half does not depend on the `DecidableEq 𝕜` instance. -/
theorem hasPointlessTwist_decEq_irrel {𝕜 : Type} [Field 𝕜] (d e : DecidableEq 𝕜) :
    @HasPointlessTwist 𝕜 _ d = @HasPointlessTwist 𝕜 _ e :=
  congrArg (fun x => @HasPointlessTwist 𝕜 _ x) (Subsingleton.elim d e)

/-- `TwistResidual` at an arbitrary *named* instance `inst`, unfolded.  This is the form in which
the quantified artefact can be removed, because `inst` can be referred to explicitly. -/
theorem twistResidual_iff_aux {𝕜 : Type} [Field 𝕜] (inst : DecidableEq 𝕜) :
    TwistResidual 𝕜 ↔ @TwistRealization 𝕜 _ inst ∧ @HasPointlessTwist 𝕜 _ inst := by
  unfold TwistResidual
  constructor
  · rintro ⟨d, hT, hR⟩
    exact ⟨Eq.mp (twistRealization_decEq_irrel d inst) hR,
      Eq.mp (hasPointlessTwist_decEq_irrel d inst) hT⟩
  · rintro ⟨hR, hT⟩
    exact ⟨inst, hT, hR⟩

/-- The `DecidableEq`-free residual `TwistResidual 𝕜` is, for any fixed `DecidableEq 𝕜`, exactly
the conjunction of the geometric half `TwistRealization 𝕜` and the arithmetic half
`HasPointlessTwist 𝕜`.  (This is how a caller supplies the residual: from the two halves of
`Defs.lean`.) -/
theorem twistResidual_iff {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] :
    TwistResidual 𝕜 ↔ TwistRealization 𝕜 ∧ HasPointlessTwist 𝕜 :=
  twistResidual_iff_aux (inferInstance : DecidableEq 𝕜)

end Work.PointlessIndexFive
