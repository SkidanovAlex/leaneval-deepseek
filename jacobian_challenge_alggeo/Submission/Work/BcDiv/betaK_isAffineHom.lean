import Mathlib
import Submission.Work.BcDiv.SymPts

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

open Work.CurveBasics CategoryTheory Limits AlgebraicGeometry
open scoped Classical

namespace Work.BcDiv

universe u

/-- **B5, affineness of the comparison.** `Work.BcDiv.βK n` is the composite of the underlying
morphism of area SY's comparison isomorphism `SymQuot.BaseChange.symBaseChangeIso` (an iso, hence
affine) with the pullback projection `pullback.fst (Sym C n).hom (specMap K L)`, which is the
base change of the affine morphism `specMap K L : Spec L ⟶ Spec K`.

Reusable in-repo facts: `Work.CurveBasics.BaseChange.isAffineHom_specMap` and
`isAffineHom_baseChangeFst` (`Submission/Work/CurveBasics/BaseChange/isAffineOpen_bcOpens.lean`),
`Work.Charts.isAffineHom_bcFst` (`Submission/Work/Charts/FinBC.lean`).

Namespace `Work.BcDiv`; file `Submission/Work/BcDiv/betaK_isAffineHom.lean`; imports
`Submission.Work.BcDiv.SymPts`. -/
theorem betaK_isAffineHom {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {L : Type u}
    [Field L] [Algebra K L] (n : ℕ) [Work.SymQuot.CurveAffineCover C]
    [Work.SymQuot.CurveAffineCover (C.baseChange L)] :
    AlgebraicGeometry.IsAffineHom (Work.BcDiv.βK (K := K) (L := L) (C := C) n) := by
  -- `symβ K L C n` is an isomorphism of `L`-schemes, so its underlying morphism is affine.
  haveI : IsIso (Work.SymQuot.BaseChange.symβ K L C n) :=
    (Work.SymQuot.BaseChange.symBaseChangeIso K L C n).isIso_hom
  haveI : IsIso ((Work.SymQuot.BaseChange.symβ K L C n).left) :=
    Functor.map_isIso (Over.forget (Spec (CommRingCat.of L))) _
  -- `pullback.fst (Sym C n).hom (specMap K L)` is the base change of the affine
  -- `specMap K L : Spec L ⟶ Spec K` (a morphism of affine schemes).
  have hfst : IsAffineHom (pullback.fst (Work.SymQuot.Sym C n).hom
      (Work.CurveBasics.Curve.specMap K L)) :=
    MorphismProperty.pullback_fst _ _ (inferInstance : IsAffineHom (Curve.specMap K L))
  haveI := hfst
  show IsAffineHom ((Work.SymQuot.BaseChange.symβ K L C n).left ≫
    pullback.fst (Work.SymQuot.Sym C n).hom (Work.CurveBasics.Curve.specMap K L))
  infer_instance

end Work.BcDiv
