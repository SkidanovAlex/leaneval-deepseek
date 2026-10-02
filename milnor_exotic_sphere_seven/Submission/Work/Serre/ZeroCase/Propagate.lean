import Mathlib
import Submission.Work.Serre.SPC.B1Propagate
import Submission.Work.Serre.SPC.goodN_attachCells

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The propagation of `GoodN` across a cell attachment

`Work.Serre.SPC.Propagate b₀ p r` is the statement that `GoodN b₀ p r` is preserved when the base
`Γ` is replaced by `Γ' = attachCells (D-2) Γ ι fr` and the structure map `g` by `attachG …`, provided
the cell step map is an isomorphism in degrees `≤ r`.  It is exactly the content of the proved
lemma `Work.Serre.SPC.goodN_attachCells`, packaged as a `Prop` so that the assembly of the `b = 1`
case (`Work.Serre.SPC.b1Comparison_of`) can take it as an explicit hypothesis.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre.SPC

noncomputable section

/-- **The propagation of `GoodN` across a cell attachment.** -/
theorem propagate {B : Type} [TopologicalSpace B] {E : Type} [TopologicalSpace E]
    (b₀ : B) (p : C(E, B)) (r : ℕ) : Work.Serre.SPC.Propagate b₀ p r :=
  fun γ₀ g hGood D hD ι fr G hG hstep =>
    Work.Serre.SPC.goodN_attachCells b₀ p γ₀ g hGood hD ι fr G hG hstep

end

end Work.Serre.SPC
