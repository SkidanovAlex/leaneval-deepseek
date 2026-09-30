import Mathlib
import Submission.Work.HomologyExtra.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

namespace Work.HomologyExtra

/-- The `k`-th component of the inclusion of a subspace, composed with the projection onto the
relative chains, is zero (componentwise form of the cokernel condition). -/
theorem inclChain_f_comp_relProj_f (k : ℕ) :
    (Work.Homology.inclChain Work.Homology.ZMod (simplex (k + 1))
        (simplexBoundary (k + 1))).f k ≫
      (Work.Homology.relProj Work.Homology.ZMod (simplex (k + 1))
        (simplexBoundary (k + 1))).f k = 0 := by
  rw [← HomologicalComplex.comp_f]
  change (Work.Homology.inclChain Work.Homology.ZMod (simplex (k + 1))
      (simplexBoundary (k + 1)) ≫
    cokernel.π (Work.Homology.inclChain Work.Homology.ZMod (simplex (k + 1))
      (simplexBoundary (k + 1)))).f k = 0
  rw [cokernel.condition, HomologicalComplex.zero_f]

/-- **The fundamental class of `(Δⁿ, ∂Δⁿ)` is a cycle**: the class of the identity simplex in the
relative chains of the pair `(Δⁿ, ∂Δⁿ)` has zero boundary.

Indeed, the boundary `∂ιₙ` of the identity simplex is a sum of the codimension one faces, each of
which lies in `∂Δⁿ`; hence `∂ιₙ` lies in the image of `C_{n-1}(∂Δⁿ) → C_{n-1}(Δⁿ)` and is killed by
the projection onto relative chains. -/
theorem simplexRelChain_d (n : ℕ) :
    CategoryTheory.CategoryStruct.comp (Work.HomologyExtra.simplexRelChain n)
      ((Work.Homology.relChain Work.Homology.ZMod (Work.HomologyExtra.simplex n)
        (Work.HomologyExtra.simplexBoundary n)).d n ((ComplexShape.down ℕ).next n)) = 0 := by
  rcases n with _ | k
  · simp
  · rw [ChainComplex.next_nat_succ]
    simp only [simplexRelChain]
    rw [Category.assoc]
    rw [HomologicalComplex.Hom.comm]
    rw [← Category.assoc]
    rw [← simplexBoundaryChain_incl k]
    rw [Category.assoc]
    rw [inclChain_f_comp_relProj_f k, comp_zero]

end Work.HomologyExtra
