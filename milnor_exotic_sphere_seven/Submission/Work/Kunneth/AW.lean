import Mathlib
import Submission.Work.Kunneth.Basic
import Submission.Work.Kunneth.awHom_d

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The Alexander–Whitney chain map

`Work.Kunneth.awMap X Y : C_*(X ⊗ Y) ⟶ C_*(X) ⊗_ℤ C_*(Y)` is the chain map whose `n`-th
component is `Work.Kunneth.awHom X Y n`, the Alexander–Whitney map
`(σ,τ) ↦ Σ_{p+q=n} σ_front_p ⊗ τ_back_q` of `Submission/Work/Kunneth/Basic.lean`.  Its chain-map
property is the companion lemma `Work.Kunneth.awHom_d`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- **The Alexander–Whitney chain map** `C_*(X ⊗ Y) ⟶ C_*(X) ⊗_ℤ C_*(Y)`. -/
def awMap (X Y : SSet) : sChain (sProd X Y) ⟶ tChain X Y where
  f n := awHom X Y n
  comm' := by
    rintro i j (h : j + 1 = i)
    subst h
    exact awHom_d X Y j

@[simp]
theorem awMap_f (X Y : SSet) (n : ℕ) : (awMap X Y).f n = awHom X Y n := rfl

end

end Work.Kunneth
