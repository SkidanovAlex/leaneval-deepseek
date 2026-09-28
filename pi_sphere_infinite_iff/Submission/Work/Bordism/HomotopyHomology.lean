import Mathlib
import Submission.Work.Cohomology.Pullback

/-!
# Homotopy invariance of singular homology (a wrapper)

Two homotopic continuous maps induce equal maps on singular homology.  This is Mathlib's
`TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor` in this workspace's notation
(`Work.Cohomology.chainMap`); it is recorded here because the obvious homotopy `M × {0} ≃ M × {1}`
inside the cylinder `M × [0,1]` is how the product bordism `Work.Bordism.prodBordism_hbd` satisfies
the boundary relation of `Work.Bordism.Bordism`, and because it is the homology counterpart of
`Work.Cohomology.homotopyInvariance`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicTopology

namespace Work.Bordism

open Work.Cohomology

/-- **Homotopy invariance of singular homology**: homotopic maps of spaces induce the same map on
singular homology, in every degree. -/
theorem homologyMap_eq_of_homotopic {X Y : TopCat} {f g : X ⟶ Y} (H : TopCat.Homotopy f g)
    (n : ℕ) :
    HomologicalComplex.homologyMap (chainMap ℤ X Y f) n
      = HomologicalComplex.homologyMap (chainMap ℤ X Y g) n :=
  H.congr_homologyMap_singularChainComplexFunctor (ModuleCat.of ℤ ℤ) n

end Work.Bordism
