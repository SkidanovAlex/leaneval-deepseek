import Mathlib
import Submission.Work.K3Inputs.Defs

set_option linter.unusedVariables false -- v435-speed

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

namespace Work.K3Inputs

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

/-- **The clause (F1) is invariant under isomorphisms of the cylinder field.**

`Work.K3Inputs.IsP1BundleOver 𝕜 p X` says that the residue field `κ(p)` of the point `p` is the
cylinder field `κ(X)(t)`.  If `κ(X)(t) ≅ κ(X')(t)` as `𝕜`-extensions, then the same point
witnesses (F1) for `X'` as well.  This is what makes (F1) usable for the *paper's* statement
"the exceptional divisor is birational to `S₀ × ℙ¹`, hence to `S × ℙ¹`": the model `X` may be
replaced by any birational model. -/
theorem IsP1BundleOver_congr (𝕜 : Type) [Field 𝕜] {P X X' : Scheme.{0}}
    [P.Over (Spec (.of 𝕜))] [IsIntegral X] [IsIntegral X']
    [X.Over (Spec (.of 𝕜))] [X'.Over (Spec (.of 𝕜))] {p : P}
    (h : Work.K3Inputs.IsP1BundleOver 𝕜 p X)
    (e : Work.K3Inputs.cylField 𝕜 X ≃+* Work.K3Inputs.cylField 𝕜 X')
    (he : e.toRingHom.comp (Work.K3Inputs.cylResMap 𝕜 X) = Work.K3Inputs.cylResMap 𝕜 X') :
    Work.K3Inputs.IsP1BundleOver 𝕜 p X' := by
  -- Unfold (F1) for `X`: some `𝕜`-isomorphism `κ(p) ≅ κ(X)(t)`.
  obtain ⟨e', he'⟩ := h
  -- Compose it with the given isomorphism `κ(X)(t) ≅ κ(X')(t)` of cylinder fields.
  refine ⟨e'.trans e, ?_⟩
  -- The composite is compatible with the structure maps because both factors are.
  rw [RingEquiv.toRingHom_trans', RingHom.comp_assoc, he', he]

end Work.K3Inputs
