import Mathlib
import Submission.Work.Thom.PairPrism

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 8000000
open scoped unitInterval
open CategoryTheory MonoidalCategory Simplicial SimplicialObject Opposite

/-!
# Homotopy invariance of relative cohomology for maps of pairs

If a homotopy `H` from `f` to `g` between continuous maps `X → Y` carries `A × I` into `B`, then the
induced maps of pairs `(X,A) → (Y,B)` agree on relative cohomology with coefficients in any
commutative ring.

The proof is the standard one, in this workspace's cochain model:

* the prism operator of `H` carries `A`-chains into `B`-chains (`Work.Thom.prism_preserves`, proved
  by comparing the inductive formula of the prism operator with the simplicial homotopy
  `TopCat.Homotopy.toSSet` of the restricted homotopy);
* hence its transpose restricts to a cochain homotopy between the relative cochain complexes
  (`Work.Thom.RelativeLiftExists`, using `Work.Thom.relKern_prism_mem`);
* a cochain homotopy induces the same map on homology (`Work.Thom.HomologyMapOfRestriction'`).
-/

namespace Work.Thom

noncomputable section

/-- **Homotopy invariance of relative cohomology for maps of pairs** (the `TopCat` version).

If a homotopy `H` from `f` to `g` carries `A × I` into `B`, then the induced maps
`H^n(Y,B;R) → H^n(X,A;R)` of the two maps of pairs agree. -/
theorem relCohMap_homotopic_top {X Y : TopCat.{0}} (A : Set X) (B : Set Y) {f g : X ⟶ Y}
    (hf : ∀ x ∈ A, f x ∈ B) (hg : ∀ x ∈ A, g x ∈ B)
    (H : TopCat.Homotopy f g) (hH : ∀ t x, x ∈ A → H (t, x) ∈ B)
    (R : Type) [CommRing R] (n : ℕ) :
    HomologicalComplex.homologyMap
        (Work.Cohomology.relComplexMap (X₁ := X) (X₂ := Y) R A B f hf) n
      = HomologicalComplex.homologyMap
        (Work.Cohomology.relComplexMap (X₁ := X) (X₂ := Y) R A B g hg) n := by
  obtain ⟨k, hk⟩ := RelativeLiftExists (X := X) (Y := Y) (f := f) (g := g) A B H hf hg hH R
  have hκ : ∀ m, Function.Injective ((Work.Cohomology.relIncl R X A).f m).hom := by
    intro m
    rw [Work.Cohomology.relIncl_f]
    intro a b hab
    exact Subtype.ext hab
  exact HomologyMapOfRestriction' (R := R)
    (C := Work.Cohomology.relComplex R Y B)
    (D := Work.Cohomology.relComplex R X A)
    (C' := Work.Cohomology.singularCochainComplex R Y)
    (D' := Work.Cohomology.singularCochainComplex R X)
    (Work.Cohomology.relIncl R Y B) (Work.Cohomology.relIncl R X A) hκ
    (α := Work.Cohomology.relComplexMap R A B f hf)
    (β := Work.Cohomology.relComplexMap R A B g hg)
    (φ := Work.Cohomology.dualChainMap R X Y f)
    (ψ := Work.Cohomology.dualChainMap R X Y g)
    (fun i => relIncl_dualChainMap_apply (f := f) A B hf R i)
    (fun i => relIncl_dualChainMap_apply (f := g) A B hg R i)
    (transposed_prism H R) k hk n

/-- **Relative cohomology is homotopy invariant for maps of pairs.**

If a homotopy `H` from `f` to `g` carries `A × I` into `B`, then the induced maps
`H^n(Y,B;R) → H^n(X,A;R)` of the two maps of pairs agree. -/
theorem relCohMap_homotopic {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) {f g : C(X, Y)}
    (hf : ∀ x ∈ A, f x ∈ B) (hg : ∀ x ∈ A, g x ∈ B)
    (H : ContinuousMap.Homotopy f g) (hH : ∀ t x, x ∈ A → H (t, x) ∈ B)
    (R : Type) [CommRing R] (n : ℕ) :
    relCohMap f A B hf R n = relCohMap g A B hg R n :=
  relCohMap_homotopic_top (X := TopCat.of X) (Y := TopCat.of Y)
    (f := TopCat.ofHom f) (g := TopCat.ofHom g) A B hf hg H hH R n

end

end Work.Thom
