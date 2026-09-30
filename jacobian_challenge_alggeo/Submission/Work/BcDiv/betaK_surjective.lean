import Mathlib
import Submission.Work.BcDiv.SymPts

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option linter.style.haveILetI false

open Work.CurveBasics CategoryTheory Limits AlgebraicGeometry
open scoped Classical

namespace Work.BcDiv

universe u

noncomputable section

/-- **B5, surjectivity of the comparison.** `Work.BcDiv.βK n` is surjective on underlying
topological spaces: it is the composite of the underlying map of an isomorphism of schemes (a
bijection) with the pullback projection `pullback.fst (Sym C n).hom (specMap K L)`, which is the
base change of the surjective morphism `specMap K L : Spec L ⟶ Spec K`.

Namespace `Work.BcDiv`; file `Submission/Work/BcDiv/betaK_surjective.lean`; imports
`Submission.Work.BcDiv.SymPts`. -/
theorem betaK_surjective {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {L : Type u}
    [Field L] [Algebra K L] (n : ℕ) [Work.SymQuot.CurveAffineCover C]
    [Work.SymQuot.CurveAffineCover (C.baseChange L)] :
    Function.Surjective (Work.BcDiv.βK (K := K) (L := L) (C := C) n).base := by
  -- `specMap K L : Spec L ⟶ Spec K` is surjective (both spectra are one-point spaces).
  haveI : Surjective (Curve.specMap K L) := inferInstance
  -- `symβ K L C n` is an isomorphism of `L`-schemes, hence its underlying map is a bijection.
  haveI : IsIso (SymQuot.BaseChange.symβ K L C n) :=
    (SymQuot.BaseChange.symBaseChangeIso K L C n).isIso_hom
  haveI : IsIso ((SymQuot.BaseChange.symβ K L C n).left) :=
    Functor.map_isIso (Over.forget (Spec (CommRingCat.of L))) _
  -- Hence `βK n = (symβ K L C n).left ≫ pullback.fst _ _` is a composite of surjections.
  haveI : Surjective (βK (K := K) (L := L) (C := C) n) := by
    show Surjective ((SymQuot.BaseChange.symβ K L C n).left ≫
      pullback.fst (SymQuot.Sym C n).hom (Curve.specMap K L))
    infer_instance
  exact Scheme.Hom.surjective _

end

end Work.BcDiv
