/-
Descent of morphisms along a flat, surjective and quasi-compact morphism of `k`-schemes.

If `π : W ⟶ J` is flat, surjective and quasi-compact over a field `k` and a `k`-morphism
`Φ : W ⟶ A` coequalizes the two projections of the kernel pair `W ×_J W`, then `Φ` descends
uniquely to a `k`-morphism `J ⟶ A`.

The mathematical content is that such a `π` is an *effective epimorphism* of schemes: this is
`AlgebraicGeometry.Scheme.instEffectiveEpi` (the fpqc topology is subcanonical,
`AlgebraicGeometry.Scheme`), i.e. `Mathlib/AlgebraicGeometry/Sites/Fpqc.lean`.
-/
import Mathlib
import Submission.Work.AbVar.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.AbVar.Extend

open CategoryTheory Limits AlgebraicGeometry

universe u

/-- The pullback in the over category `Over X` of a morphism with itself is computed in the base
category: the forgetful functor `Over X ⥤ C` preserves connected limits (in particular pullbacks,
the walking cospan being connected), so the projections of the pullback of `f` with itself in
`Over X` are, on underlying objects, the projections of the pullback of `f.left` with itself. -/
theorem isPullback_left_fst_snd {k : Type u} [Field k] {W J : Work.AbVar.Sch k} (π : W ⟶ J) :
    IsPullback (pullback.fst π π).left (pullback.snd π π).left π.left π.left :=
  IsPullback.of_isLimit
    (isLimitOfHasPullbackOfPreservesLimit (Over.forget (Spec (.of k))) π π)

open CategoryTheory in
theorem desc_of_flat_surjective_quasiCompact {k : Type*} [Field k]
    {W J A : Work.AbVar.Sch k} (π : W ⟶ J) [AlgebraicGeometry.Flat π.left]
    [AlgebraicGeometry.Surjective π.left] [AlgebraicGeometry.QuasiCompact π.left] (Φ : W ⟶ A)
    (h : Limits.pullback.fst π π ≫ Φ = Limits.pullback.snd π π ≫ Φ) :
    ∃! (g : J ⟶ A), π ≫ g = Φ := by
  -- `π.left` is an effective epimorphism of schemes, since it is flat, surjective and
  -- quasi-compact (`AlgebraicGeometry.Scheme.instEffectiveEpi`).
  have hpb := isPullback_left_fst_snd (k := k) π
  -- Hence `π.left` is the coequalizer of *any* kernel pair, in particular of the underlying
  -- projections of the pullback in `Over (Spec k)`.
  have hcoeq : IsColimit (Cofork.ofπ π.left hpb.w) :=
    EffectiveEpiStruct.isColimitCoforkOfIsPullback (EffectiveEpi.getStruct π.left) hpb
  -- The hypothesis `h` says exactly that `Φ.left` coequalizes those projections.
  have hcond : (pullback.fst π π).left ≫ Φ.left = (pullback.snd π π).left ≫ Φ.left :=
    congrArg Over.Hom.left h
  -- Descent in the category of schemes.
  obtain ⟨g0, hg0, huniq⟩ := Cofork.IsColimit.existsUnique hcoeq Φ.left hcond
  have hg0' : π.left ≫ g0 = Φ.left := hg0
  -- `g0` is a morphism of `k`-schemes, i.e. commutes with the structure morphisms.
  have hstruct : g0 ≫ A.hom = J.hom := by
    rw [← cancel_epi π.left, ← Category.assoc, hg0', Over.w Φ, Over.w π]
  refine ⟨Over.homMk g0 hstruct, ?_, ?_⟩
  · apply Over.OverMorphism.ext
    simpa using hg0'
  · intro y hy
    apply Over.OverMorphism.ext
    apply huniq y.left
    simpa using congrArg Over.Hom.left hy

end Work.AbVar.Extend
