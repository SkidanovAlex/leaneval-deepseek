/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area CH — base change of a `K`-scheme along a *finite* field extension

This file is the scheme-theoretic foundation of **route B** of
`Submission/Work/NOTES_LEAD_jacobian_charts3.md` §2: the base change `X_L` of a `K`-scheme `X`
along a finite field extension `L/K`, as an object of `Sch K = Over (Spec K)`, together with
its two projections `bcFst : X_L ⟶ X` and `bcSnd : X_L ⟶ Spec L`, the lifting of `F`-points
of `X` along a `K`-embedding `L ↪ F` (`bcLift`), and the two facts about `bcFst` that route B
rests on:

* `isFinite_bcFst` — `bcFst` is finite when `L/K` is finite; hence
* `isClosedMap_bcFst` — `bcFst` is a closed map, which is what makes the opens
  `Ω_E := Sym^g ∖ fst(j_E⁻¹(W′)ᶜ)` of the design open;
* `surjective_bcFst` — `bcFst` is surjective.

`Work.Charts.bcScheme` (in `Density.lean`) is the underlying scheme; `bcSch` bundles it with
its structure morphism to `Spec K`, so that it is an object of `Sch K` again.
-/
import Submission.Work.GCBasics.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 1000000

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics

set_option linter.style.haveILetI false

namespace Work.Charts

open Work.GCBasics

noncomputable section

variable {K : Type u} [Field K]

/-- **The base change of a `K`-scheme along a field extension**, as a `K`-scheme: the
pullback `X ×_{Spec K} Spec L`, with its structure morphism `X_L ⟶ Spec K` through `Spec L`.

This is `Work.Charts.bcScheme X L` bundled with its structure map; the extra `.hom` is the
composite `X_L ⟶ Spec L ⟶ Spec K`. -/
abbrev bcSch (X : Sch K) (L : Type u) [Field L] [Algebra K L] : Sch K :=
  Over.mk (pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap K L))) ≫
    Spec.map (CommRingCat.ofHom (algebraMap K L)))

/-- The projection `X_L ⟶ X`. -/
abbrev bcFst (X : Sch K) (L : Type u) [Field L] [Algebra K L] : bcSch X L ⟶ X :=
  Over.homMk (pullback.fst _ _) (by simp [pullback.condition])

/-- The projection `X_L ⟶ Spec L`, as a morphism of `K`-schemes. -/
abbrev bcSnd (X : Sch K) (L : Type u) [Field L] [Algebra K L] :
    bcSch X L ⟶ specOf K L :=
  Over.homMk (pullback.snd _ _) (by simp [bcSch])

@[simp]
theorem bcFst_left (X : Sch K) (L : Type u) [Field L] [Algebra K L] :
    (bcFst X L).left = pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
  rfl

@[simp]
theorem bcSnd_left (X : Sch K) (L : Type u) [Field L] [Algebra K L] :
    (bcSnd X L).left = pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
  rfl

/-- **Lifting an `F`-point of `X` to the base change** along a `K`-embedding `L → F`: the
universal property of the pullback, using the given embedding `Spec F ⟶ Spec L`. -/
def bcLift (X : Sch K) (L : Type u) [Field L] [Algebra K L]
    {F : Type u} [Field F] [Algebra K F] (e : L →ₐ[K] F) (p : FPt X F) :
    FPt (bcSch X L) F :=
  Over.homMk (pullback.lift p.left (Spec.map (CommRingCat.ofHom e.toRingHom)) (by
      rw [Over.w p, ← Over.w (specOfMap (K := K) e), specOf_hom, specOfMap_left]))
    (by
      rw [show Over.hom (bcSch X L) =
          Limits.pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap K L))) ≫
            Spec.map (CommRingCat.ofHom (algebraMap K L)) from rfl,
        ← Category.assoc, Limits.pullback.lift_snd, specOf_hom, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, Spec.map_inj]
      apply CommRingCat.hom_ext
      ext x
      exact e.commutes x)

/-- **The defining equation of `bcLift`**: its image under `bcFst` is the original point. -/
@[simp]
theorem bcLift_fst (X : Sch K) (L : Type u) [Field L] [Algebra K L]
    {F : Type u} [Field F] [Algebra K F] (e : L →ₐ[K] F) (p : FPt X F) :
    bcLift X L e p ≫ bcFst X L = p := by
  apply Over.OverMorphism.ext
  show pullback.lift p.left (Spec.map (CommRingCat.ofHom e.toRingHom)) _ ≫
    pullback.fst _ _ = p.left
  rw [Limits.pullback.lift_fst]

/-- **The second defining equation of `bcLift`**: its second component is `Spec e`. -/
@[simp]
theorem bcLift_snd (X : Sch K) (L : Type u) [Field L] [Algebra K L]
    {F : Type u} [Field F] [Algebra K F] (e : L →ₐ[K] F) (p : FPt X F) :
    bcLift X L e p ≫ bcSnd X L = specOfMap (K := K) e := by
  apply Over.OverMorphism.ext
  show pullback.lift p.left (Spec.map (CommRingCat.ofHom e.toRingHom)) _ ≫
    pullback.snd _ _ = Spec.map (CommRingCat.ofHom e.toRingHom)
  rw [Limits.pullback.lift_snd]

/-- **B1 (finiteness).**  The projection `X_L ⟶ X` of a base change along a finite field
extension is finite: it is the base change of the finite `Spec L ⟶ Spec K`. -/
instance isFinite_bcFst (X : Sch K) (L : Type u) [Field L] [Algebra K L]
    [FiniteDimensional K L] : IsFinite (bcFst X L).left := by
  haveI : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap K L)) :
      Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K)) := by
    rw [IsFinite.SpecMap_iff]
    change (algebraMap K L).Finite
    rw [RingHom.finite_algebraMap]
    infer_instance
  show IsFinite (Limits.pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap K L))))
  infer_instance

/-- **B1 (closedness).**  A finite morphism is a closed map, so `bcFst` is closed.  This is
the reason the sets `Ω_E` of route B are open. -/
theorem isClosedMap_bcFst (X : Sch K) (L : Type u) [Field L] [Algebra K L]
    [FiniteDimensional K L] : IsClosedMap (bcFst X L).left.base := by
  haveI := isFinite_bcFst (K := K) X L
  exact Scheme.Hom.isClosedMap (bcFst X L).left

/-- **B1 (surjectivity).**  `X_L ⟶ X` is surjective: `Spec L ⟶ Spec K` is (both are
one-point spaces) and surjectivity is stable under base change. -/
theorem surjective_bcFst (X : Sch K) (L : Type u) [Field L] [Algebra K L] :
    Function.Surjective (bcFst X L).left.base := by
  haveI : Surjective (Spec.map (CommRingCat.ofHom (algebraMap K L)) :
      Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K)) := inferInstance
  show Function.Surjective (Limits.pullback.fst X.hom _).base
  simpa using (Scheme.Hom.surjective (Limits.pullback.fst X.hom
    (Spec.map (CommRingCat.ofHom (algebraMap K L)))))

/-- **Affineness of `bcFst`.**  The projection of the base change along a finite extension is
affine (it is the base change of the affine `Spec L ⟶ Spec K`). -/
instance isAffineHom_bcFst (X : Sch K) (L : Type u) [Field L] [Algebra K L]
    [FiniteDimensional K L] : IsAffineHom (bcFst X L).left := by
  haveI : IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap K L)) :
      Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K)) := inferInstance
  show IsAffineHom (Limits.pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap K L))))
  exact MorphismProperty.pullback_fst _ _ inferInstance

/-- The base change of a scheme is irreducible when the scheme is geometrically irreducible.
(A convenience instance for route B's FIBRE-GEN step.) -/
instance irreducibleSpace_bcSch (X : Sch K) (L : Type u) [Field L] [Algebra K L]
    [GeometricallyIrreducible X.hom] : IrreducibleSpace (bcSch X L).left :=
  GeometricallyIrreducible.geometrically_irreducibleSpace (f := X.hom)
    (Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap K L))))
    (pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap K L))))
    (IsPullback.of_hasPullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap K L))))

end

end Work.Charts
