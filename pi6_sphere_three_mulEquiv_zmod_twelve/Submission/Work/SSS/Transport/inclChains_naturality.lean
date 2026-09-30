import Mathlib
import Submission.Work.SSS.Transport.Basic

namespace Work.SSS.Transport

open CategoryTheory CategoryTheory.Limits

/-- The inclusion of relative chains is natural in the pair: a map of pairs induces a commutative
square of chain maps.  `Work.Cohomology.inclChains X A` is the chain map `C_*(A) ⟶ C_*(X)`
induced by the inclusion `A ⊆ X`, and `Work.Cohomology.chainMap ℤ X Y f` is the map on singular
chains induced by the continuous map `f`. -/
theorem inclChains_naturality {X Y : TopCat} (A : Set X) (B : Set Y) (f : X ⟶ Y)
    (g : C(↥A, ↥B)) (hg : ∀ a : ↥A, (g a : Y) = f (a : X)) :
    Work.Cohomology.inclChains X A ≫ Work.Cohomology.chainMap ℤ X Y f =
      Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of B) (TopCat.ofHom g) ≫
        Work.Cohomology.inclChains Y B := by
  -- Both sides are the image under the singular chains functor of the two composites of the
  -- square `A → B → Y` and `A → X → Y`, which agree by `hg`.
  simp only [Work.Cohomology.inclChains, Work.Cohomology.chainMap, Work.Cohomology.subtypeIncl]
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext a
  simpa using (hg a).symm

end Work.SSS.Transport
