import Mathlib
import Submission.Work.ThomBordism.Interface
import Submission.Work.ThomBordism.sigmaSigmaTypeSum
import Submission.Work.ThomBordism.sigmaHomeomorph
import Submission.Work.ThomBordism.man8Finiteness

/-!
# The signature of the boundary class is the sum of the pieces' signatures

For a finite family `F : ι → Man8` of closed oriented `8`-manifolds occurring as the boundary of a
compact oriented `9`-manifold `W` (with relative fundamental class `w`), the middle signature of the
boundary class `∂w ∈ H₈(∂W;ℤ)`, computed on `∂W`, is the sum of the signatures of the pieces:

`Work.ThomBordism.sigmaBoundarySum`.

The proof is the functoriality of the homology pushforward, combined with

* `Work.ThomBordism.sigmaHomeomorph` — `σ` is invariant under the homeomorphism
  `W.bdry : ∂W ≃ₜ Σ i, (F i).pt`;
* `W.hw` — the boundary of the relative fundamental class is the sum of the pieces' fundamental
  classes;
* `Work.ThomBordism.sigmaSigmaTypeSum` — additivity of `σ` over a finite disjoint union (with the
  finiteness instances of `Work.ThomBordism.man8Finiteness`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology
open scoped Manifold ContDiff

namespace Work.ThomBordism

/-- **Functoriality of the pushforward on homology along a composite of continuous maps, applied to
an element.**  For `f : X ⟶ Y`, `g : Y ⟶ Z` and `c ∈ H_n(X;ℤ)`, pushing `c` forward along `g` after
pushing it forward along `f` is the same as pushing it forward along `f ≫ g`. -/
theorem homologyMap_chainMap_comp_apply {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ)
    (c : (Work.Cohomology.singularChains ℤ X).homology n) :
    (CategoryTheory.ConcreteCategory.hom
        (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ Y Z g) n))
      ((CategoryTheory.ConcreteCategory.hom
        (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ X Y f) n)) c)
    = (CategoryTheory.ConcreteCategory.hom
        (HomologicalComplex.homologyMap
          (Work.Cohomology.chainMap ℤ X Z (CategoryTheory.CategoryStruct.comp f g)) n)) c := by
  rw [← CategoryTheory.ConcreteCategory.comp_apply]
  rw [← HomologicalComplex.homologyMap_comp, ← Work.Cohomology.chainMap_comp']

theorem sigmaBoundarySum {ι : Type} [Fintype ι] {F : ι → Man8} (W : NullBordismFamily ι F) :
    Work.SignatureBordism.sigma 4
        (TopCat.toSSet.obj (TopCat.of ((modelWithCornersEuclideanHalfSpace 9).boundary W.W)))
        (Work.Cohomology.hPairδ (TopCat.of W.W)
          ((modelWithCornersEuclideanHalfSpace 9).boundary W.W) 8 W.w)
      = ∑ i, (F i).sigma := by
  classical
  set A : Set W.W := (modelWithCornersEuclideanHalfSpace 9).boundary W.W with hA
  let XD : TopCat := TopCat.of A
  let Z : TopCat := TopCat.of (Σ i : ι, (F i).pt)
  let e : XD ≅ Z := TopCat.isoOfHomeo W.bdry
  let gf : (i : ι) → ((F i).X ⟶ XD) :=
    fun i => TopCat.ofHom ⟨fun y => W.bdry.symm (⟨i, y⟩ : Σ i, (F i).pt),
      W.bdry.continuous_invFun.comp continuous_sigmaMk⟩
  let incl : (i : ι) → ((F i).X ⟶ Z) :=
    fun i => TopCat.ofHom ⟨fun y => (⟨i, y⟩ : Σ i, (F i).pt),
      by exact continuous_sigmaMk (σ := fun i => (F i).pt) (i := i)⟩
  -- the composite `gf i ≫ e.hom` is the coproduct inclusion
  have hmor : ∀ i, CategoryTheory.CategoryStruct.comp (gf i) (e.hom) = incl i := by
    intro i
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro y
    show e.hom (W.bdry.symm (⟨i, y⟩ : Σ i, (F i).pt)) = (⟨i, y⟩ : Σ i, (F i).pt)
    show W.bdry (W.bdry.symm (⟨i, y⟩ : Σ i, (F i).pt)) = _
    simp
  -- the boundary class is the sum of the pieces' fundamental classes
  have hdelta : (CategoryTheory.ConcreteCategory.hom
        (Work.Cohomology.hPairδ (TopCat.of W.W) A 8)) W.w
      = ∑ i, (CategoryTheory.ConcreteCategory.hom
          (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (F i).X XD (gf i)) 8))
          ((F i).c) :=
    W.hw
  -- transporting along `W.bdry` and using functoriality of the pushforward
  have hstep : (CategoryTheory.ConcreteCategory.hom
        (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ XD Z e.hom) (4 + 4)))
        ((CategoryTheory.ConcreteCategory.hom (Work.Cohomology.hPairδ (TopCat.of W.W) A 8)) W.w)
      = ∑ i, (CategoryTheory.ConcreteCategory.hom
          (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (F i).X Z (incl i))
            (4 + 4))) ((F i).c) := by
    rw [hdelta, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hii := homologyMap_chainMap_comp_apply (gf i) (e.hom) 8 ((F i).c)
    rw [hmor i] at hii
    exact hii
  have h1 := Work.ThomBordism.sigmaHomeomorph (k := 4) XD Z e
    ((CategoryTheory.ConcreteCategory.hom (Work.Cohomology.hPairδ (TopCat.of W.W) A 8)) W.w)
  rw [← h1]
  rw [hstep]
  exact Work.ThomBordism.sigmaSigmaTypeSum (k := 4) ι (fun i => (F i).pt) (fun i => (F i).c)

end Work.ThomBordism
