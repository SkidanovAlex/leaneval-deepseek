import Mathlib
import Submission.Work.SymQuot.DivOf.Complete.RhoData
import Submission.Work.SymQuot.DivOf.Complete.EBasis.exists_tensorQuotEquiv_bcSec
import Submission.Work.SymQuot.DivOf.C1Defs
import Submission.Work.CurveBasics.Curve.BCSquare.SectionsTensor
import Submission.Work.SpecLin.Alt.isLocalization_chartTensorSectionsMap

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
universe u

open CategoryTheory Limits AlgebraicGeometry in
theorem tensorQuotEquiv_bcSec {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {F : Type u} [Field F] [Algebra K F] {L : Type u} [Field L] [Algebra K L] [Algebra F L]
    [IsScalarTower K F L] {V : C.left.Opens} [Nonempty V] (hV : IsAffineOpen V)
    (I : Ideal Γ((C.baseChange F).left, C.bcOpens F V)) :
    Nonempty (TensorProduct F L (Γ((C.baseChange F).left, C.bcOpens F V) ⧸ I) ≃ₐ[L]
      (Γ((C.baseChange L).left, C.bcOpens L V) ⧸
        I.map (Work.SymQuot.DivOf.bcSec F L V))) :=
  ⟨Classical.choose (Work.SymQuot.DivOf.Complete.EBasis.exists_tensorQuotEquiv_bcSec
    (C := C) (F := F) (L := L) hV I)⟩
