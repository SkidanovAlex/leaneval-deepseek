import Mathlib
import Submission.Work.StemsB.fibration_les
import Submission.Work.StemsB.exists_lift_rel
import Submission.Work.StemsB.HurewiczFibration

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The long exact homotopy sequence of a Serre fibration, unconditionally

`Work.StemsB.fibration_les` (`Submission/Work/StemsB/fibration_les.lean`) proves the long exact
homotopy sequence of a map `p : E → B` from the *relative* homotopy lifting property
`∀ k, HasHLPRel p k`, and `Work.StemsB.exists_lift_rel` (proved in
`Submission/Work/StemsB/exists_lift_rel.lean`) produces that property from the Serre fibration
condition — the classical cell-by-cell argument, via the cube homeomorphism that carries
`I^k × {0} ∪ ∂I^k × I` to the bottom face.

Composing the two closes the fibration chapter: **every Serre fibration has a long exact homotopy
sequence**, and in particular so does the path–loop fibration `ΩX → PX → X`
(`fibrationLES_evalOne`), the fibration whose Serre spectral sequence is the refined route to
`Work.StemsB.RatHurewiczRange` (`CONTRACTS.md` §D).
-/

open scoped Topology unitInterval

namespace Work.StemsB

noncomputable section

/-- **Every Serre fibration has a long exact homotopy sequence.** -/
theorem fibrationLES_of_isSerreFibration {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : IsSerreFibration p) (e₀ : E) : FibrationLES p e₀ :=
  fibration_les p (fun k => exists_lift_rel p hp k) e₀

/-- **The long exact homotopy sequence of the path–loop fibration** `ΩX → PX → X`. -/
theorem fibrationLES_evalOne (X : Type) [TopologicalSpace X] (x₀ : X) (e : PathSpace X x₀) :
    FibrationLES (evalOne X x₀) e :=
  fibrationLES_of_isSerreFibration (evalOne X x₀) (isSerreFibration_evalOne X x₀) e

/-- **Every Hurewicz fibration has a long exact homotopy sequence** (in the universe of small test
spaces). -/
theorem fibrationLES_of_isHurewiczFibration {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (hp : IsHurewiczFibration p) (e₀ : E) :
    FibrationLES p e₀ :=
  fibrationLES_of_isSerreFibration p (IsHurewiczFibration.isSerreFibration hp) e₀

end

end Work.StemsB
