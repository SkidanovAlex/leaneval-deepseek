import Mathlib
import Submission.Work.CurveBasics.BCSquare
import Submission.Work.CurveBasics.Curve.BCSquare.fieldMapTensor
import Submission.Work.CurveBasics.Curve.BCSquare.tensorLift_injective
import Submission.Work.CurveBasics.Curve.BCSquare.L_divMap

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.CurveBasics.Curve.BCSquare

open scoped TensorProduct

open Work.CurveBasics CategoryTheory Limits AlgebraicGeometry in
universe u in
theorem span_iInf {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F]
    {C : Curve k} {C' : Curve F} (S : Curve.BCSquare C C') {ι : Type u} [Nonempty ι]
    (M : ι → Submodule k C.functionField) :
    Submodule.span F (S.fieldMap.hom '' ↑(⨅ j, M j)) =
      ⨅ j, Submodule.span F (S.fieldMap.hom '' ↑(M j)) := by
  let tL := Work.CurveBasics.Curve.BCSquare.tensorLift S
  let Φ : F ⊗[k] C.functionField →ₗ[F] C'.functionField :=
    { toFun := tL
      map_add' := tL.map_add
      map_smul' := fun c z => Work.CurveBasics.Curve.BCSquare.tensorLift_smul S c z }
  have hφ : ∀ (c : F) (v : C.functionField), Φ (c ⊗ₜ[k] v) = c • S.fieldMap.hom v := by
    intro c v
    show tL (c ⊗ₜ[k] v) = c • S.fieldMap.hom v
    rw [Work.CurveBasics.Curve.BCSquare.tensorLift_tmul, Algebra.smul_def]
  exact Work.CurveBasics.Curve.BCSquare.span_iInf_tmul_one Φ
    (Work.CurveBasics.Curve.BCSquare.tensorLift_injective S) S.fieldMap.hom hφ M

end Work.CurveBasics.Curve.BCSquare
