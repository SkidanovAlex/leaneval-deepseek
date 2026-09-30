import Mathlib
import Submission.Work.Kunneth.EzawWDefs
import Submission.Work.Kunneth.H_comm_gen
import Submission.Work.Kunneth.homotopy_of_gen_identity

/-!
# The chain homotopy `ezMap ≫ awMap ≃ 𝟙` from the model chains `W`

Acyclic-models assembly of the second Eilenberg–Zilber chain homotopy: given a family of model
chains `W p q ∈ (tMod p q).X (p+1+q)` satisfying the recursion `d (W p q) = dfc W p q`
(`Submission/Work/Kunneth/EzawWDefs.lean`, `EZAWDefs.lean`), the homotopy `H` built from `W` is a
chain homotopy between `ezMap ≫ awMap` and the identity on `C_*(X) ⊗_ℤ C_*(Y)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

theorem ezaw_homotopy_of_W (W : (p q : ℕ) → ↥((Work.Kunneth.tMod p q).X (p + q + 1)))
    (hW : ∀ p q, (Work.Kunneth.tMod p q).d (p + q + 1) (p + q) (W p q)
      = Work.Kunneth.dfc W p q)
    (X Y : SSet) :
    Nonempty (Homotopy
      (CategoryTheory.CategoryStruct.comp (Work.Kunneth.ezMap X Y) (Work.Kunneth.awMap X Y))
      (CategoryTheory.CategoryStruct.id (Work.Kunneth.tChain X Y))) := by
  obtain ⟨hs⟩ := exists_HsumData X Y W
  exact homotopy_of_gen_identity X Y W hs (fun p q σ τ => H_comm_gen X Y W hs hW p q σ τ)

end

end Work.Kunneth
