/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The identification `C ≅ Sym¹ C` (area SY)

`Work.SymQuot.Sym.curveIso C : C.toOver ⟶ Sym C 1` is the inverse of the isomorphism
`Sym C 1 ≅ C` of `Work.SymQuot.Sym.sym_one`; it is the `GroupChunk.Input.curveIso` field
(contract item 9, `Sym¹ C ≅ C`).
-/
import Submission.Work.SymQuot.Sym.sym_one

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot

/-- **The identification `C ⟶ Sym¹ C`**: the sum map of the single point `x`.  Written
explicitly (rather than as `Classical.choice (Sym.sym_one C)`, which would be an unnamed witness
of a `Nonempty` and hence useless for computation) as `Sym.powMap C 1 (fun _ => 𝟙 C.toOver)`. -/
noncomputable def Sym.curveIso {K : Type u} [Field K] (C : Work.CurveBasics.Curve K)
    [CurveAffineCover C] : C.toOver ⟶ Sym C 1 :=
  Sym.powMap C 1 (fun _ => 𝟙 C.toOver)

/-- **`curveIso` is the inverse of the isomorphism `Sym¹ C ≅ C` of `Sym.sym_one`.** -/
theorem Sym.curveIso_eq {K : Type u} [Field K] (C : Work.CurveBasics.Curve K)
    [CurveAffineCover C] :
    Sym.curveIso C = (Work.SymQuot.Sym.prodOneIso C).hom ≫ Sym.quot C 1 :=
  rfl

end Work.SymQuot
