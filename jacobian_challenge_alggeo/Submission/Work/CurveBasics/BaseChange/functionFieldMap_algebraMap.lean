/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Compatibility of `functionFieldMap` with the algebra structures

The projection `C_F ⟶ C` induces the field homomorphism `K(C) ⟶ K(C_F)`
(`Work.CurveBasics.Curve.functionFieldMap`).  Here we show that it is compatible with the
`k`-algebra structures: the structure morphism `C ⟶ Spec k` of `C` and the structure morphism
`C_F ⟶ Spec F` of the base change sit in the pullback square

```
C_F  --baseChangeFst-->  C
 |                        |
baseChangeHom            C.hom
 v                        v
Spec F --specMap k F--> Spec k
```

and evaluating the corresponding maps on global sections, together with
`ΓSpecIso_inv_naturality` (which says exactly that `specMap k F` corresponds to
`algebraMap k F` on global sections), yields the result.
-/
import Mathlib
import Submission.Work.CurveBasics.BaseChangeFunctionField

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

namespace Work.CurveBasics.BaseChange

universe u in
open Work.CurveBasics in
theorem functionFieldMap_algebraMap {k : Type u} [Field k] (C : Curve k) (F : Type u) [Field F]
    [Algebra k F] (c : k) :
    (C.functionFieldMap F).hom (algebraMap k C.functionField c) =
      algebraMap F (C.baseChange F).functionField (algebraMap k F c) := by
  -- the two top opens needed to make sense of `germToFunctionField ⊤`
  have hCt : Nonempty (⊤ : C.left.Opens) := ⟨⟨genericPoint C.left, trivial⟩⟩
  haveI := hCt
  have hXt : Nonempty (⊤ : (C.baseChange F).left.Opens) :=
    ⟨⟨genericPoint (C.baseChange F).left, trivial⟩⟩
  haveI := hXt
  -- unwind the two algebra structures into explicit composites of ring homomorphisms
  have hkey : algebraMap k C.functionField c
      = C.left.germToFunctionField ⊤ (C.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)) := by
    simp only [RingHom.algebraMap_toAlgebra, ConcreteCategory.comp_apply]
  have hkey2 : algebraMap F (C.baseChange F).functionField (algebraMap k F c)
      = (C.baseChange F).left.germToFunctionField ⊤
          ((C.baseChange F).hom.appTop
            ((Scheme.ΓSpecIso (CommRingCat.of F)).inv (algebraMap k F c))) := by
    simp only [RingHom.algebraMap_toAlgebra, ConcreteCategory.comp_apply]
  -- the pullback square, evaluated on global sections at the argument `ΓSpecIso.inv c`
  have hpb : (C.baseChangeFst F) ≫ C.hom = (C.baseChangeHom F) ≫ (Curve.specMap k F) :=
    CategoryTheory.Limits.pullback.condition
  have happ := ConcreteCategory.congr_hom (congrArg Scheme.Hom.appTop hpb)
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)
  simp only [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply] at happ
  -- `specMap k F` corresponds to `algebraMap k F` on global sections
  have hnat := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k F))) c
  simp only [ConcreteCategory.comp_apply] at hnat
  have hAB : (C.baseChangeFst F).appTop
        (C.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c))
      = (C.baseChangeHom F).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of F)).inv (algebraMap k F c)) := by
    rw [happ, ← hnat, CommRingCat.ofHom_apply]
  rw [hkey, hkey2]
  -- now compute the induced map `functionFieldMap` on the germ of a global section
  rw [Curve.functionFieldMap]
  erw [ConcreteCategory.comp_apply]
  erw [TopCat.Presheaf.germ_stalkSpecializes_apply]
  erw [Scheme.Hom.germ_stalkMap_apply]
  erw [hAB]
  rfl

end Work.CurveBasics.BaseChange
