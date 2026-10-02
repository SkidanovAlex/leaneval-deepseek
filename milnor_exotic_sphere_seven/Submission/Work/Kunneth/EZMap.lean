import Mathlib
import Submission.Work.Kunneth.EZ
import Submission.Work.Kunneth.ezHom_d

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The Eilenberg–Zilber chain map

`Work.Kunneth.ezMap X Y : C_*(X) ⊗_ℤ C_*(Y) ⟶ C_*(X ⊗ Y)` is the chain map whose `n`-th
component is the shuffle map `Work.Kunneth.ezHom X Y n` of `Submission/Work/Kunneth/EZ.lean`.
Together with `Work.Kunneth.awMap` (the Alexander–Whitney map in the other direction) it is the
chain-level content of the Eilenberg–Zilber theorem; the two are inverse up to chain homotopy.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- **The Eilenberg–Zilber shuffle chain map** `C_*(X) ⊗_ℤ C_*(Y) ⟶ C_*(X ⊗ Y)`. -/
def ezMap (X Y : SSet) : tChain X Y ⟶ sChain (sProd X Y) where
  f n := ezHom X Y n
  comm' := by
    rintro i j (h : j + 1 = i)
    subst h
    exact ezHom_d X Y j

@[simp]
theorem ezMap_f (X Y : SSet) (n : ℕ) : (ezMap X Y).f n = ezHom X Y n := rfl

end

end Work.Kunneth
