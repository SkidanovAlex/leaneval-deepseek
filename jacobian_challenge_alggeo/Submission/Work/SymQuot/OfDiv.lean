/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The constant map at an effective divisor (area SY)

For an effective `K`-divisor `E` of degree `n`, the completeness half of the point/divisor
dictionary (`DivOf.Complete.divOf_complete`) produces a `K`-point `Sym.ofDiv C n E …` of `Symⁿ C`
with divisor `E`; `Sym.constMap C n E …` is the constant map `X ⟶ Symⁿ C` at that point.  They
are the `GroupChunk.Input.constMap`/`constMap_divOf` fields.
-/
import Submission.Work.SymQuot.SymGeomInst
import Submission.Work.SymQuot.DivOf.Complete.divOf_complete
import Submission.Work.GCBasics.All
import Submission.Work.SymQuot.AddMap
import Submission.Work.SymQuot.CurveIso

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical MonoidalCategory

universe u

namespace Work.SymQuot

/-- **The `K`-point of `Symⁿ C` with divisor `E`**, for an effective `K`-divisor of degree `n`. -/
noncomputable def Sym.ofDiv {K : Type u} [Field K] (C : Work.CurveBasics.Curve K)
    [CurveAffineCover C] (n : ℕ) [NeZero n] (E : Work.SpecLin.Dv C K) (hE : E.IsEffective)
    (hd : (C.baseChange K).deg E = n) : Work.SpecLin.FPt (Sym C n) K :=
  Classical.choose (Work.SymQuot.DivOf.Complete.divOf_complete (C := C) (n := n) E hE hd)

/-- The defining property of `Sym.ofDiv`. -/
theorem Sym.divOf_ofDiv {K : Type u} [Field K] (C : Work.CurveBasics.Curve K)
    [CurveAffineCover C] (n : ℕ) [NeZero n] (E : Work.SpecLin.Dv C K) (hE : E.IsEffective)
    (hd : (C.baseChange K).deg E = n) :
    Work.SymQuot.DivOf.divOf K (Sym.ofDiv C n E hE hd) = E :=
  Classical.choose_spec (Work.SymQuot.DivOf.Complete.divOf_complete (C := C) (n := n) E hE hd)

/-- **The constant map at the effective divisor `E`**: the composite `X ⟶ Spec K ⟶ Symⁿ C`. -/
noncomputable def Sym.constMap {K : Type u} [Field K] (C : Work.CurveBasics.Curve K)
    [CurveAffineCover C] (n : ℕ) [NeZero n] (E : Work.SpecLin.Dv C K) (hE : E.IsEffective)
    (hd : (C.baseChange K).deg E = n) (X : Work.SpecLin.Sch K) : X ⟶ Sym C n :=
  Over.homMk X.hom (by simp) ≫ Sym.ofDiv C n E hE hd

/-- **The map `x ↦ x + E`** for `E` an effective `K`-divisor of degree `g - 1`
(with `g ≥ 1`): the point `x` of `C`, together with the constant divisor `E`, added in
`Sym^g C`.  It is the `GroupChunk.Input.curveAdd` field. -/
noncomputable def Sym.curveAdd {K : Type u} [Field K] (C : Work.CurveBasics.Curve K)
    [CurveAffineCover C] (g : ℕ) (hg : 1 ≤ g) (E : Work.SpecLin.Dv C K) (hE : E.IsEffective)
    (hd : (C.baseChange K).deg E = (g : ℤ) - 1) : C.toOver ⟶ Sym C g :=
  if h1 : g = 1 then h1.symm ▸ Sym.curveIso C
  else
    haveI : NeZero (g - 1) := ⟨by omega⟩
    CartesianMonoidalCategory.lift (Sym.curveIso C)
        (Sym.constMap C (g - 1) E hE (by rw [hd, Nat.cast_sub hg]; norm_num) C.toOver)
      ≫ addMap C 1 (g - 1)
      ≫ (congrArg (Sym C) (by omega : 1 + (g - 1) = g) ▸ 𝟙 (Sym C (1 + (g - 1))))

end Work.SymQuot
