/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The generic point of a curve and the structure morphism

For a curve `C` over `k`, the canonical morphism `Spec K(C) ⟶ C` at the generic point is the
`k`-structure morphism of the function field, i.e. it is `Spec` of the algebra map
`k ⟶ K(C)`.
-/
import Submission.Work.CurveBasics.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.CurveBasics

namespace Curve

noncomputable section

variable {k : Type u} [Field k]

/-- The canonical morphism `Spec K(C) ⟶ C` is compatible with the structure morphism:
it is `Spec` of the `k`-algebra structure on the function field. -/
lemma fromSpecStalk_genericPoint_comp_hom (C : Curve k) :
    C.left.fromSpecStalk (genericPoint C.left) ≫ C.hom
      = Spec.map (CommRingCat.ofHom (algebraMap k C.functionField)) := by
  have hne : Nonempty (⊤ : C.left.Opens) := ⟨⟨genericPoint C.left, trivial⟩⟩
  haveI := hne
  have hL : (C.left.fromSpecStalk (genericPoint C.left)).appTop =
      C.left.germToFunctionField ⊤
        ≫ (Scheme.ΓSpecIso (C.left.presheaf.stalk (genericPoint C.left))).inv := by
    rw [Scheme.fromSpecStalk_appTop]; simp
  have hR : (Scheme.ΓSpecIso (CommRingCat.of k)).inv
        ≫ (Spec.map (CommRingCat.ofHom (algebraMap k C.functionField))).appTop =
      CommRingCat.ofHom (algebraMap k C.functionField)
        ≫ (Scheme.ΓSpecIso (CommRingCat.of C.functionField)).inv := by
    rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of C.functionField)).hom]
    simp only [Category.assoc]
    rw [Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap k C.functionField)),
      Iso.inv_hom_id_assoc (Scheme.ΓSpecIso (CommRingCat.of k)),
      Iso.inv_hom_id (Scheme.ΓSpecIso (CommRingCat.of C.functionField)), Category.comp_id]
  apply AlgebraicGeometry.ext_to_Spec
  rw [Scheme.Γ_map_op, Scheme.Γ_map_op, Scheme.Hom.comp_appTop, hL]
  erw [hR]
  rw [show (algebraMap k C.functionField) =
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ C.hom.appTop ≫
        C.left.germToFunctionField ⊤).hom from rfl]
  rw [show CommRingCat.ofHom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ C.hom.appTop ≫
        C.left.germToFunctionField ⊤).hom = (Scheme.ΓSpecIso (CommRingCat.of k)).inv
          ≫ C.hom.appTop ≫ C.left.germToFunctionField ⊤ from rfl]
  rfl

end

end Curve

end Work.CurveBasics
