import Mathlib
import Submission.Work.Cohomology.Sd_isSmallChain

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Whitney.tcmSuspAux

open CategoryTheory
open scoped Simplicial

/-- A singular simplex of `A` that is small for `(U, ∅)` is pushed by `f` to a simplex of `X` that
is small for `(U', ∅)`, provided `f` maps `U` into `U'`. -/
lemma isSmall_map_of_mapsTo {A X : TopCat} (f : A ⟶ X) {U : Set A} {U' : Set X}
    (h : ∀ a ∈ U, (CategoryTheory.ConcreteCategory.hom f) a ∈ U') {n : ℕ}
    {σ : Work.Cohomology.Simplex A n}
    (hσ : Work.Cohomology.IsSmall U (∅ : Set A) σ) :
    Work.Cohomology.IsSmall U' (∅ : Set X)
      ((TopCat.toSSet.map f).app (Opposite.op ⦋n⦌) σ) := by
  rw [Work.Cohomology.isSmall_iff] at hσ ⊢
  have hfun : (fun z : (Work.Cohomology.Delta n : TopCat) =>
        (ConcreteCategory.hom (Work.Cohomology.sdMap n
          ((TopCat.toSSet.map f).app (Opposite.op ⦋n⦌) σ))) z)
      = fun z => (ConcreteCategory.hom f) ((ConcreteCategory.hom (Work.Cohomology.sdMap n σ)) z) := by
    funext z
    rw [Work.Cohomology.sdMap_map, ConcreteCategory.comp_apply]
  rw [hfun]
  left
  rintro y ⟨z, rfl⟩
  rcases hσ with hU | hV
  · exact h _ (hU ⟨z, rfl⟩)
  · exact absurd (hV ⟨z, rfl⟩) (Set.notMem_empty _)

theorem pushChain_isSmallChain_of_subset {A X : TopCat} (f : A ⟶ X) (U : Set A) (U' : Set X)
    (h : ∀ a ∈ U, (CategoryTheory.ConcreteCategory.hom f) a ∈ U') {n : ℕ}
    (c : (Work.Cohomology.singularChains ℤ A).X n)
    (hc : Work.Cohomology.IsSmallChain U (∅ : Set A) c) :
    Work.Cohomology.IsSmallChain U' (∅ : Set X) (Work.Cohomology.pushChain A X f n c) := by
  obtain ⟨a, ha⟩ := hc
  rw [← ha]
  refine Work.Cohomology.isSmallChain_of_gen (X := X) (U := U') (V := (∅ : Set X))
    (Y := Work.Cohomology.smallSSet U (∅ : Set A)) (n := n)
    ((Work.Cohomology.smallToSing U (∅ : Set A)).f n ≫
      Work.Cohomology.pushChainHom A X f n) ?_ a
  intro σ'
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, Work.Cohomology.smallToSing_gen]
  change Work.Cohomology.IsSmallChain U' (∅ : Set X)
    (Work.Cohomology.pushChain A X f n (Work.Cohomology.gen A n σ'.1))
  rw [Work.Cohomology.pushChain_gen]
  exact Work.Cohomology.isSmallChain_gen (isSmall_map_of_mapsTo f h σ'.2)

end Work.Whitney.tcmSuspAux
