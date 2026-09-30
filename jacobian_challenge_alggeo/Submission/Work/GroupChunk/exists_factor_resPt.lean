import Mathlib
import Submission.Work.GCBasics.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


open CategoryTheory AlgebraicGeometry

namespace Work.GroupChunk

universe u

/-- A field point of a `K`-scheme factors through the canonical point of the residue field of
its image point: every `p : FPt X F` is the base change of `resPt X x` along some
`K`-algebra map `resField X x →ₐ[K] F`, where `x` is the image of the closed point of `Spec F`. -/
theorem exists_factor_resPt {K : Type u} [Field K] {X : Work.GCBasics.Sch K}
    {F : Type u} [Field F] [Algebra K F] (p : Work.GCBasics.FPt X F) :
    ∃ e : Work.GCBasics.resField X (p.left (IsLocalRing.closedPoint F)) →ₐ[K] F,
      p = Work.GCBasics.RPt.map e
        (Work.GCBasics.resPt X (p.left (IsLocalRing.closedPoint F))) := by
  let x := p.left (IsLocalRing.closedPoint F)
  -- The map on residue fields induced by `p` (a local ring map `κ(x) → F`).
  let δ : X.left.residueField x ⟶ CommRingCat.of F :=
    @Scheme.descResidueField F _ X.left x (Scheme.stalkClosedPointTo p.left)
      (Scheme.isLocalHom_stalkClosedPointTo p.left)
  -- `p` factors through the canonical point at `x` along `Spec.map δ`.
  have hfac : Spec.map δ ≫ X.left.fromSpecResidueField x = p.left :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField F X.left p.left
  -- The `K`-algebra structure on `κ(x)` is pinned down by the structure morphism of `X`.
  have h1 : Spec.map (CommRingCat.ofHom (algebraMap K (X.left.residueField x))) =
      X.left.fromSpecResidueField x ≫ X.hom := by
    rw [← Work.GCBasics.specOf_hom K (Work.GCBasics.resField X x)]
    exact Work.GCBasics.specOf_resField_hom X x
  have h2 : Spec.map (CommRingCat.ofHom (algebraMap K F)) = p.left ≫ X.hom := by
    rw [← Work.GCBasics.specOf_hom K F, (Over.w p).symm]
  -- Hence `δ` is a `K`-algebra homomorphism.
  have hcomp : CommRingCat.ofHom (algebraMap K (X.left.residueField x)) ≫ δ =
      CommRingCat.ofHom (algebraMap K F) := by
    apply Spec.map_injective
    rw [Spec.map_comp, h1, ← Category.assoc, hfac, h2]
  let e : X.left.residueField x →ₐ[K] F :=
    { toRingHom := δ.hom, commutes' := fun k => by
        have hh := congrArg CommRingCat.Hom.hom hcomp
        simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at hh
        exact DFunLike.congr_fun hh k }
  refine ⟨e, ?_⟩
  apply Over.OverMorphism.ext
  have heq : CommRingCat.ofHom e.toRingHom = δ := rfl
  show p.left = (Work.GCBasics.RPt.map e (Work.GCBasics.resPt X x)).left
  rw [Work.GCBasics.RPt.map, Over.comp_left, Work.GCBasics.specOfMap_left,
    Work.GCBasics.resPt_left, heq, hfac]

end Work.GroupChunk
