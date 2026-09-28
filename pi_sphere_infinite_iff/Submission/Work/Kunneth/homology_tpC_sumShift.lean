import Mathlib
import Submission.Work.Kunneth.Tensor
import Submission.Work.Kunneth.Algebra
import Submission.Work.Kunneth.HomProd

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct

namespace Work.Kunneth

noncomputable section

theorem homology_tpC_sumShift (C : ChainComplex (ModuleCat ℤ) ℕ) (M : ℕ → ModuleCat ℤ)
    (hM : ∀ q, Module.Flat ℤ ↥(M q)) (n : ℕ) :
    Nonempty (CategoryTheory.Iso ((Work.Kunneth.tpC C (Work.Kunneth.sumShift M)).homology n)
      ((Work.Kunneth.tpC (Work.Kunneth.sumShift (fun p => C.homology p))
        (Work.Kunneth.sumShift M)).X n)) := by
  exact ⟨(homology_iso_hCycQuot C M n).some.trans
    ((hCycQuot_iso_prod C M n).some.trans
      ((hHTensProd_iso_hQuotProd C M n hM).some.trans
        (hHTensProd_iso_X C M n).some))⟩

end

end Work.Kunneth
