import Mathlib
import Submission.Work.Domain.Resid.Setup
import Submission.Work.Domain.Resid.fromSpecStalk_algebraMap

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.Domain.Resid

open CategoryTheory AlgebraicGeometry
open Work.GCBasics

/-- Every field-valued point `p : Spec F ⟶ X` of a `K`-scheme `X` whose underlying point is `x`
factors through the canonical point `Spec κ(x) ⟶ X`, by a `K`-algebra homomorphism
`κ(x) → F`.

Concretely: the morphism of locally ringed spaces `p.left` induces a local ring homomorphism
`O_{X,x} → F`, whose composite with the residue map is a ring homomorphism `κ(x) → F`, which is
automatically `K`-linear because `p` is a morphism of `K`-schemes. The resulting composite
`Spec F → Spec κ(x) → X` is identified with `p` by
`Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField`. -/
theorem exists_resPt_factor {K : Type _} [Field K] {X : Work.GCBasics.Sch K}
    [AlgebraicGeometry.IsIntegral X.left] (x : X.left) {F : Type _} [Field F] [Algebra K F]
    (p : Work.GCBasics.FPt X F)
    (hx : p.left (IsLocalRing.closedPoint F) = x) :
    ∃ e : Work.GCBasics.resField X x →ₐ[K] F,
      Work.GCBasics.RPt.map e (Work.GCBasics.resPt X x) = p := by
  subst hx
  -- The ring homomorphism `κ(x) → F` induced by `p`.
  have hh : IsLocalHom (CommRingCat.Hom.hom (Scheme.stalkClosedPointTo p.left)) := inferInstance
  let g : X.left.residueField (p.left (IsLocalRing.closedPoint F)) ⟶ CommRingCat.of F :=
    @Scheme.descResidueField F _ X.left _ (Scheme.stalkClosedPointTo p.left) hh
  -- `g` really does exhibit `p` as a point of `Spec κ(x)`.
  have hg : Spec.map g ≫ X.left.fromSpecResidueField (p.left (IsLocalRing.closedPoint F)) = p.left :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField F X.left p.left
  -- The `K`-algebra structure on `κ(x)` is the one induced by `Spec κ(x) → X → Spec K`.
  have hKκ :
      Spec.map (CommRingCat.ofHom (algebraMap K (resField X (p.left (IsLocalRing.closedPoint F))))) =
        X.left.fromSpecResidueField (p.left (IsLocalRing.closedPoint F)) ≫ X.hom := by
    rw [← specOf_hom K (resField X (p.left (IsLocalRing.closedPoint F)))]
    exact specOf_resField_hom X (p.left (IsLocalRing.closedPoint F))
  -- Hence `g` is `K`-linear.
  have key : CommRingCat.ofHom (algebraMap K (resField X (p.left (IsLocalRing.closedPoint F)))) ≫ g =
      CommRingCat.ofHom (algebraMap K F) := by
    rw [← Spec.map_inj, Spec.map_comp, hKκ, ← Category.assoc, hg, Over.Hom.w p, specOf_hom K F]
  have hcomm : ∀ k : K,
      g (algebraMap K (resField X (p.left (IsLocalRing.closedPoint F))) k) = algebraMap K F k := by
    intro k
    have := congrArg (fun (φ : CommRingCat.of K ⟶ CommRingCat.of F) => φ k) key
    simpa using this
  let e : resField X (p.left (IsLocalRing.closedPoint F)) →ₐ[K] F :=
    AlgHom.mk' g.hom (fun c y => by rw [Algebra.smul_def, Algebra.smul_def, map_mul, hcomm c])
  have he : e.toRingHom = g.hom := rfl
  refine ⟨e, ?_⟩
  -- The two `Over` morphisms have the same underlying morphism.
  show (specOfMap e ≫ resPt X (p.left (IsLocalRing.closedPoint F))) = p
  apply Over.OverMorphism.ext
  rw [Over.comp_left, specOfMap_left, resPt_left]
  rw [he, CommRingCat.ofHom_hom]
  exact hg

end Work.Domain.Resid
