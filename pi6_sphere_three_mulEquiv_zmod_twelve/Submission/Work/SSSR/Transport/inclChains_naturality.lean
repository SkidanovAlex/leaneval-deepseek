import Mathlib
import Submission.Work.SSSR.Transport.Basic
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR.Transport

open CategoryTheory CategoryTheory.Limits
/-- The inclusion of relative chains is natural in the pair: a map of pairs induces a commutative
square of chain maps.  `Work.Cohomology.inclChains R X A` is the chain map `C_*(A) ⟶ C_*(X)`
induced by the inclusion `A ⊆ X`, and `Work.Cohomology.chainMap ℤ X Y f` is the map on singular
chains induced by the continuous map `f`. -/
theorem inclChains_naturality {X Y : TopCat} (A : Set X) (B : Set Y) (f : X ⟶ Y)
    (g : C(↥A, ↥B)) (hg : ∀ a : ↥A, (g a : Y) = f (a : X)) :
    Work.SSSR.Cohomology.inclChains R X A ≫ Work.SSSR.Cohomology.chainMap R X Y f =
      Work.SSSR.Cohomology.chainMap R (TopCat.of A) (TopCat.of B) (TopCat.ofHom g) ≫
        Work.SSSR.Cohomology.inclChains R Y B := by
  -- Both sides are the image under the singular chains functor of the two composites of the
  -- square `A → B → Y` and `A → X → Y`, which agree by `hg`.
  simp only [Work.SSSR.Cohomology.inclChains, Work.SSSR.Cohomology.chainMap, Work.SSSR.Cohomology.subtypeIncl]
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext a
  simpa using (hg a).symm

end Work.SSSR.Transport
