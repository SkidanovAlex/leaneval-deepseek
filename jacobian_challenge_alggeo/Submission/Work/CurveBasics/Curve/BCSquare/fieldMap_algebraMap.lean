import Mathlib
import Submission.Work.CurveBasics.BCSquare
import Submission.Work.CurveBasics.BaseChange.functionFieldMap_algebraMap

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.style.haveILetI false

namespace Work.CurveBasics.Curve.BCSquare

open Work.CurveBasics CategoryTheory Limits AlgebraicGeometry in
universe u in
theorem fieldMap_algebraMap {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F]
    {C : Curve k} {C' : Curve F} (S : Curve.BCSquare C C') (c : k) :
    S.fieldMap.hom (algebraMap k C.functionField c) =
      algebraMap F C'.functionField (algebraMap k F c) := by
  -- the top opens needed to make sense of `germToFunctionField ⊤`
  have hCt : Nonempty (⊤ : C.left.Opens) := ⟨⟨genericPoint C.left, trivial⟩⟩
  haveI := hCt
  have hXt : Nonempty (⊤ : C'.left.Opens) := ⟨⟨genericPoint C'.left, trivial⟩⟩
  haveI := hXt
  -- unwind the two algebra structures into explicit composites of ring homomorphisms
  have hkey : algebraMap k C.functionField c
      = C.left.germToFunctionField ⊤
          (C.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)) := by
    simp only [RingHom.algebraMap_toAlgebra, ConcreteCategory.comp_apply]
  have hkey2 : algebraMap F C'.functionField (algebraMap k F c)
      = C'.left.germToFunctionField ⊤
          (C'.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of F)).inv (algebraMap k F c))) := by
    simp only [RingHom.algebraMap_toAlgebra, ConcreteCategory.comp_apply]
  -- the pullback square, evaluated on global sections at the argument `ΓSpecIso.inv c`
  have hpb : S.π ≫ C.hom = C'.hom ≫ Curve.specMap k F := S.isPullback.w
  have happ := ConcreteCategory.congr_hom (congrArg Scheme.Hom.appTop hpb)
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)
  simp only [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply] at happ
  -- `specMap k F` corresponds to `algebraMap k F` on global sections
  have hnat := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k F))) c
  simp only [ConcreteCategory.comp_apply] at hnat
  have hAB : S.π.appTop (C.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c))
      = C'.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of F)).inv (algebraMap k F c)) := by
    rw [happ, ← hnat, CommRingCat.ofHom_apply]
  rw [hkey, hkey2]
  -- now compute the induced map on the germ of a global section
  rw [Curve.BCSquare.fieldMap]
  erw [ConcreteCategory.comp_apply]
  erw [TopCat.Presheaf.germ_stalkSpecializes_apply]
  erw [Scheme.Hom.germ_stalkMap_apply]
  erw [hAB]
  rfl

end Work.CurveBasics.Curve.BCSquare
