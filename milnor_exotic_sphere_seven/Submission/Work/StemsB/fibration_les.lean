import Mathlib
import Submission.Work.StemsB.PiMap
import Submission.Work.StemsB.Fibrations
import Submission.Work.StemsB.LESExact

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.StemsB

/-- **The long exact homotopy sequence of a Serre fibration.**  If `p : E → B` has the relative
homotopy lifting property (for the standard pairs `(I^k × I, I^k × {0} ∪ ∂I^k × I)`, equivalently
`p` is a Serre fibration), then for every `k` there is a connecting homomorphism
`∂ : π_{k+2}(B) →* π_{k+1}(F)` (with `F = p ⁻¹' {p e₀}`) making the sequence
`π_{k+2}(F) → π_{k+2}(E) → π_{k+2}(B) → π_{k+1}(F) → π_{k+1}(E)` exact. -/
theorem fibration_les {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hrel : ∀ k, HasHLPRel p k) (e₀ : E) : FibrationLES p e₀ := by
  intro k
  exact ⟨dMap p e₀ hrel k, les_exact_E p e₀ hrel k, les_exact_B p e₀ hrel k,
    les_exact_F p e₀ hrel k⟩

end Work.StemsB
