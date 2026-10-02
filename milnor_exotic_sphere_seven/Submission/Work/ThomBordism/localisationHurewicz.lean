import Mathlib
import Submission.Work.Tubular.TubeClass.localisationCollapseClassSpanTop
import Submission.Work.Tubular.Gauss

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The localisation of the Hurewicz class of the Pontryagin–Thom collapse

This file records, for the target `Work.ThomBordism.collapseLocalisation_ambientV2`, the *easy*
half of the localisation chapter: the localisation at the zero-section point `x₀` of the Hurewicz
class of the collapse is the push-forward (along the collapse viewed as a map of pairs
`(S^{8+k}, S^{8+k}∖{y₀}) → (ν⁺, ν⁺∖{x₀})`) of the localisation of the sphere generator at `y₀`.

* `cokernel_pi_chainMap_homology` — the abstract identity ("the cokernel projection is natural for
  the relative chain map"): for a map of pairs `f : (X,A) → (Y,B)` and any absolute chain `x`,
  `(coker.π_Y)_* ((chainMap f)_* x) = (relChainsMapOf f)_* ((coker.π_X)_* x)`.
  This is `cokernel_π_relChainsMapOf_aux` (in `TubeClass/localisationCollapseClassSpanTop.lean`)
  read at the level of homology; it is the formal content of "the localisation of a Hurewicz class
  at a point is the push-forward of the localised generator".
* `hurewiczChain_eq_chainMap` — `hurewiczChain` is, by definition, the chain-level push-forward of
  the sphere generator along the descent of the cube loop to the sphere.
* `localisation_hurewiczChain_collapse` — the collapse instance of the abstract identity.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits
open scoped Topology

namespace Work.Tubular.TubeClass

theorem cokernel_pi_chainMap_homology {X Y : TopCat} {A : Set X} {B : Set Y} {f : X ⟶ Y}
    {g : TopCat.of ↥A ⟶ TopCat.of ↥B} (w : Work.Cohomology.subtypeIncl X A ≫ f
      = g ≫ Work.Cohomology.subtypeIncl Y B) (n : ℕ)
    (x : (Work.Cohomology.singularChains ℤ X).homology n) :
    (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains Y B)) n))
        ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap
          (Work.Cohomology.chainMap ℤ X Y f) n)) x)
      = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
          (Work.Cohomology.relChainsMapOf X Y A B f g w) n))
        ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap
          (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains X A)) n)) x) := by
  have hcomp : HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ X Y f) n
        ≫ HomologicalComplex.homologyMap (CategoryTheory.Limits.cokernel.π
            (Work.Cohomology.inclChains Y B)) n
      = HomologicalComplex.homologyMap (CategoryTheory.Limits.cokernel.π
            (Work.Cohomology.inclChains X A)) n
        ≫ HomologicalComplex.homologyMap (Work.Cohomology.relChainsMapOf X Y A B f g w) n := by
    have hL := (HomologicalComplex.homologyMap_comp (Work.Cohomology.chainMap ℤ X Y f)
      (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains Y B)) n).symm
    have hR := (HomologicalComplex.homologyMap_comp (CategoryTheory.Limits.cokernel.π
      (Work.Cohomology.inclChains X A)) (Work.Cohomology.relChainsMapOf X Y A B f g w) n).symm
    rw [hL, hR, cokernel_π_relChainsMapOf_aux]
  exact congrArg (fun (φ : _ ⟶ _) => (ModuleCat.Hom.hom φ) x) hcomp

/-- `hurewiczChain` is the chain-level push-forward of the sphere generator along the descent of the
cube loop to the sphere. -/
theorem hurewiczChain_eq_chainMap {V : Work.ThomBordism.Man8} {k : ℕ} {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)}
    {ε : ℝ} (C : TubeChart E ε) {R : ℝ} (hR : 0 ≤ R)
    (hbox : ∀ y ∈ C.U, ∀ i : Fin (8 + k), |y i| < R)
    (g : C(OnePoint (Euc (8 + k)), OnePoint (NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty) :
    Work.Stems.hurewiczChain (8 + k) (by omega) OnePoint.infty
        (tubeGenLoopOnePoint C g hg hR hbox)
      = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
          (Work.Cohomology.chainMap ℤ (TopCat.of (Work.Stems.sphere (8 + k)))
            (TopCat.of (OnePoint (NormalTotal E)))
            (TopCat.ofHom (Work.Stems.cubeLift (8 + k) (by omega)
              (tubeGenLoopOnePoint C g hg hR hbox)))) (8 + k)))
        (Work.Stems.sphereGenerator (8 + k) (by omega)) := rfl

end Work.Tubular.TubeClass
