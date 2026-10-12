import Mathlib.Analysis.InnerProductSpace.PiL2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.LatVec` — the integer lattice vector

This tiny module isolates the definition of the lattice vector `latVec m = (m i : ℝ)_i : ℝ³`,
which is the only ingredient of the far-kernel development that came from `AliasDefs`.  Keeping it
in a Mathlib-only module means the `farKernel_*` files do not depend on the (heavy) aliasing
chapter.
-/

namespace Work.BoseBoxFock

open scoped BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The **integer lattice vector** `m ↦ (m i : ℝ)_i`. -/
noncomputable def latVec (m : Fin 3 → ℤ) : E3 := WithLp.toLp 2 (fun i => (m i : ℝ))

@[simp] lemma latVec_apply (m : Fin 3 → ℤ) (i : Fin 3) : latVec m i = (m i : ℝ) := rfl

end Work.BoseBoxFock
