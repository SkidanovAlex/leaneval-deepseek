import Mathlib
import Submission.Work.BcDiv.symBCBundle

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.BcDiv

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical MonoidalCategory

universe u

/-- **The quotient map of `Symⁿ(C_L)` followed by `βK`** is the comparison `symfL` of the quotient
maps, followed by the projection of the base change `(Symⁿ C)_L ⟶ Symⁿ C`: this is the defining
property `symβ_spec_left` of the comparison `symβ`, together with the definition of `βK`. -/
theorem quot_comp_betaK {K : Type u} [Field K] {L : Type u} [Field L] [Algebra K L]
    {C : Work.CurveBasics.Curve K} [Work.SymQuot.CurveAffineCover C]
    [Work.SymQuot.CurveAffineCover (C.baseChange L)] (n : ℕ) :
    (Work.SymQuot.Sym.quot (C.baseChange L) n).left ≫ βK (K := K) (L := L) (C := C) n
      = (Work.SymQuot.BaseChange.symfL K L C n).left
          ≫ pullback.fst (Work.SymQuot.Sym C n).hom (Work.CurveBasics.Curve.specMap K L) := by
  rw [βK, ← Category.assoc, Work.SymQuot.BaseChange.symβ_spec_left]

/-- **The projection of the base change commutes with the pullback functor**: for `u : X ⟶ Y` in
`Over S` and `f : S' ⟶ S`, the underlying morphism of `(Over.pullback f).map u` followed by the
projection `(Y ×_S S') ⟶ Y` is the projection `(X ×_S S') ⟶ X` followed by `u`. -/
theorem pullback_map_left_comp_fst {C' : Type*} [Category C'] {S S' : C'} (f : S' ⟶ S)
    [HasPullbacksAlong f] {X Y : Over S} (u : X ⟶ Y) :
    ((Over.pullback f).map u).left ≫ pullback.fst Y.hom f
      = pullback.fst X.hom f ≫ u.left := by
  simp only [Over.pullback_map_left]
  exact pullback.lift_fst _ _ _

theorem symquot_comp_betaK {K : Type u} [Field K] {L : Type u} [Field L] [Algebra K L]
    {C : Work.CurveBasics.Curve K} [Work.SymQuot.CurveAffineCover C]
    [Work.SymQuot.CurveAffineCover (C.baseChange L)] (n : ℕ) :
    (Work.SymQuot.Sym.quot (C.baseChange L) n).left ≫ βK (K := K) (L := L) (C := C) n
      = ((Work.SymQuot.BaseChange.symPiIso K L C n).inv.left
          ≫ pullback.fst (Work.SymQuot.prod C.toOver n).hom
              (Work.CurveBasics.Curve.specMap K L))
        ≫ (Work.SymQuot.Sym.quot C n).left := by
  rw [quot_comp_betaK (K := K) (L := L) (C := C) n,
    Work.SymQuot.BaseChange.symfL_left, Work.SymQuot.BaseChange.symqL_left]
  simp only [pullback_map_left_comp_fst, Category.assoc]

end Work.BcDiv
