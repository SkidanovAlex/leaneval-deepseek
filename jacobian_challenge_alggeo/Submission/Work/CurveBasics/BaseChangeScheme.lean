/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Base change of a curve

The base change of a curve `C` over `k` along a field extension `F/k`.  This file only
sets up the underlying scheme and its structure morphism; the proof that it is again a
curve lives in `Work.CurveBasics.BaseChange`.
-/
import Submission.Work.CurveBasics.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.CurveBasics

namespace Curve

noncomputable section

variable {k : Type u} [Field k]

/-- The structure morphism `Spec F ⟶ Spec k` of a field extension. -/
abbrev specMap (k : Type u) [Field k] (F : Type u) [Field F] [Algebra k F] :
    Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k F))

/-- The base change `C_F = C ×_k Spec F` of a curve, as an object of `Over (Spec F)`. -/
noncomputable abbrev baseChangeOver (C : Curve k) (F : Type u) [Field F] [Algebra k F] :
    Over (Spec (CommRingCat.of F)) :=
  (Over.pullback (specMap k F)).obj C.toOver

/-- The underlying scheme of the base change `C_F = C ×_k Spec F`. -/
noncomputable abbrev baseChangeLeft (C : Curve k) (F : Type u) [Field F] [Algebra k F] :
    Scheme.{u} := (baseChangeOver C F).left

/-- The structure morphism `C_F ⟶ Spec F`. -/
noncomputable abbrev baseChangeHom (C : Curve k) (F : Type u) [Field F] [Algebra k F] :
    baseChangeLeft C F ⟶ Spec (CommRingCat.of F) := (baseChangeOver C F).hom

/-- The projection `C_F ⟶ C`. -/
noncomputable abbrev baseChangeFst (C : Curve k) (F : Type u) [Field F] [Algebra k F] :
    baseChangeLeft C F ⟶ C.left := pullback.fst C.hom (specMap k F)

/-- The projection `C_F ⟶ C` is surjective. -/
instance baseChangeFst_surjective (C : Curve k) (F : Type u) [Field F] [Algebra k F] :
    Surjective (baseChangeFst C F) := by
  dsimp only [baseChangeFst, baseChangeLeft, baseChangeOver, Over.pullback_obj_left,
    Over.pullback_obj_hom, specMap]
  infer_instance

/-- `SmoothOfRelativeDimension n` is stable under base change (the instance is not
registered in Mathlib at this pin, so we record it here). -/
theorem smoothOfRelativeDimension_pullback_snd {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S)
    {n : ℕ} [SmoothOfRelativeDimension n f] :
    SmoothOfRelativeDimension n (pullback.snd f g) := by
  haveI : MorphismProperty.IsStableUnderBaseChangeAlong (@SmoothOfRelativeDimension n) g :=
    ⟨fun pb h => MorphismProperty.IsStableUnderBaseChange.of_isPullback pb h⟩
  exact MorphismProperty.pullback_snd f g inferInstance

/-- A base change of a curve is smooth of relative dimension one. -/
theorem baseChange_smoothOfRelativeDimension (C : Curve k) (F : Type u) [Field F]
    [Algebra k F] : SmoothOfRelativeDimension 1 (baseChangeHom C F) := by
  dsimp only [baseChangeHom, baseChangeOver, Over.pullback_obj_hom, specMap]
  exact smoothOfRelativeDimension_pullback_snd _ _

/-- A base change of a proper curve is proper. -/
theorem baseChange_isProper (C : Curve k) (F : Type u) [Field F] [Algebra k F] :
    IsProper (baseChangeHom C F) := by
  dsimp only [baseChangeHom, baseChangeOver, Over.pullback_obj_hom, specMap]
  infer_instance

/-- A base change of a geometrically irreducible curve is geometrically irreducible. -/
theorem baseChange_geometricallyIrreducible (C : Curve k) (F : Type u) [Field F] [Algebra k F] :
    GeometricallyIrreducible (baseChangeHom C F) := by
  dsimp only [baseChangeHom, baseChangeOver, Over.pullback_obj_hom, specMap]
  infer_instance

/-- A base change of a geometrically reduced curve is geometrically reduced. -/
theorem baseChange_geometricallyReduced (C : Curve k) (F : Type u) [Field F] [Algebra k F] :
    GeometricallyReduced (baseChangeHom C F) := by
  dsimp only [baseChangeHom, baseChangeOver, Over.pullback_obj_hom, specMap]
  infer_instance

/-- A base change of a curve is nontrivial. -/
instance baseChange_nontrivial (C : Curve k) (F : Type u) [Field F] [Algebra k F] :
    Nontrivial (baseChangeLeft C F) := by
  obtain ⟨a, b, hab⟩ := (inferInstance : Nontrivial C.left)
  obtain ⟨x, hx⟩ := (baseChangeFst C F).surjective a
  obtain ⟨y, hy⟩ := (baseChangeFst C F).surjective b
  exact ⟨x, y, fun h => hab (by rw [← hx, ← hy, h])⟩

end

end Curve

end Work.CurveBasics
