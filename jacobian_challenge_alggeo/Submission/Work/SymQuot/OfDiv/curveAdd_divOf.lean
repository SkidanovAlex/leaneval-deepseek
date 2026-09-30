import Mathlib
import Submission.Work.SymQuot.OfDiv
import Submission.Work.SymQuot.OfDiv.addMap_divOf
import Submission.Work.SymQuot.OfDiv.constMap_divOf
import Submission.Work.SymQuot.Sym.curveIso_divOf

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


universe u

set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped MonoidalCategory

namespace Work.SymQuot.OfDiv

/-- **`divOf` is insensitive to the transport of a point of `Symⁿ C` along an equality of the
exponents.**  If `h : m = n`, the morphism `congrArg (Sym C) h ▸ 𝟙 (Sym C m)` is the
`eqToHom` identifying `Sym C m` with `Sym C n`; postcomposing a point with it does not change
its divisor (the two `divOf`'s are the same function after `cases h`). -/
lemma divOf_comp_cast {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    [Work.SymQuot.CurveAffineCover C] {m n : ℕ} [NeZero m] [NeZero n] (h : m = n)
    {F : Type u} [Field F] [Algebra K F] (p : Work.SpecLin.FPt (Work.SymQuot.Sym C m) F) :
    Work.SymQuot.DivOf.divOf F
        (p ≫ (congrArg (Work.SymQuot.Sym C) h ▸ 𝟙 (Work.SymQuot.Sym C m) :
          Work.SymQuot.Sym C m ⟶ Work.SymQuot.Sym C n))
      = Work.SymQuot.DivOf.divOf F p := by
  cases h
  simp

open CategoryTheory Limits AlgebraicGeometry in
theorem curveAdd_divOf {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    [Work.SymQuot.CurveAffineCover C] {g : ℕ} [NeZero g] (hg : 1 ≤ g) (E : Work.SpecLin.Dv C K)
    (hE : E.IsEffective) (hd : (C.baseChange K).deg E = (g : ℤ) - 1)
    {F : Type u} [Field F] [Algebra K F] (x : Work.SpecLin.CurveFPt C F) :
    Work.SymQuot.DivOf.divOf F (x ≫ Work.SymQuot.Sym.curveAdd C g hg E hE hd)
      = Work.SpecLin.ptDiv x + Work.SpecLin.DivBase.bc (IsScalarTower.toAlgHom K K F) E := by
  classical
  rw [Work.SymQuot.Sym.curveAdd]
  split_ifs with h1
  · -- `g = 1`: `curveAdd` is the identification `C ≅ Sym¹ C` and `E` has degree `0`,
    -- hence is `0` (it is effective).
    subst h1
    rw [Work.SymQuot.Sym.curveIso_divOf]
    have hE0 : E = 0 := by
      refine (Work.CurveBasics.Divisor.deg_eq_zero_iff (C := C.baseChange K) hE).mp ?_
      simpa using hd
    rw [hE0, Work.SpecLin.DivBase.bc_zero, add_zero]
  · -- `g ≠ 1`: `curveAdd` is `lift curveIso (constMap (g-1) E) ≫ addMap 1 (g-1)`,
    -- followed by the transport `Sym C (1 + (g-1)) → Sym C g`.
    haveI hNe : NeZero (g - 1) := ⟨by omega⟩
    haveI hNe1 : NeZero (1 + (g - 1)) := ⟨by omega⟩
    -- On a point of `Sym¹ C ⊗ Sym^{g-1} C`, the transport does not change the divisor …
    simp only [← Category.assoc]
    rw [Work.SymQuot.OfDiv.divOf_comp_cast (C := C) (m := 1 + (g - 1)) (n := g) (by omega)]
    -- … and `addMap_divOf` computes the divisor of a sum of points.
    rw [show CartesianMonoidalCategory.lift (Work.SymQuot.Sym.curveIso C)
          (Work.SymQuot.Sym.constMap C (g - 1) E hE (by rw [hd, Nat.cast_sub hg]; norm_num) C.toOver)
        = CartesianMonoidalCategory.liftEquiv
          (Work.SymQuot.Sym.curveIso C,
           Work.SymQuot.Sym.constMap C (g - 1) E hE (by rw [hd, Nat.cast_sub hg]; norm_num) C.toOver)
        from by rw [CartesianMonoidalCategory.liftEquiv_apply]]
    rw [Work.SymQuot.OfDiv.addMap_divOf, Work.SymQuot.Sym.curveIso_divOf,
      Work.SymQuot.OfDiv.constMap_divOf]

end Work.SymQuot.OfDiv
