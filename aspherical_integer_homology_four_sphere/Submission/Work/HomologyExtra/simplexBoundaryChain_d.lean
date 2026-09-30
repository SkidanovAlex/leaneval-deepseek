import Mathlib
import Submission.Work.HomologyExtra.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The fundamental cycle of `∂Δⁿ⁺¹` is a cycle

`Work.HomologyExtra.simplexBoundaryChain n` is the alternating sum of the codimension one
faces of the identity `(n+1)`-simplex, viewed as an `n`-chain of the boundary
`∂Δⁿ⁺¹ ⊂ Δⁿ⁺¹` (`Work.HomologyExtra.simplexBoundaryChain_incl`).  In this file we show
that it is a cycle, i.e. that its boundary in the singular chain complex of `∂Δⁿ⁺¹` vanishes.

The argument is the standard one: the chain is the boundary of the identity simplex in the
ambient space `Δⁿ⁺¹`, where `∂∂ = 0`; the inclusion `∂Δⁿ⁺¹ ↪ Δⁿ⁺¹` induces a monomorphism
of singular chain complexes in each degree, so the boundary vanishes already in `∂Δⁿ⁺¹`.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

set_option linter.style.haveILetI false

namespace Work.HomologyExtra

noncomputable section

/-- The inclusion of a subspace `A ⊆ X` induces a monomorphism `Sing(A) ⟶ Sing(X)` of
singular simplicial sets: on `k`-simplices it is postcomposition with the (injective)
inclusion. -/
theorem mono_toSSet_map_incl (X : TopCat) (A : Set X) :
    Mono (TopCat.toSSet.map (Work.Homology.incl A)) := by
  haveI : ∀ k, Mono ((TopCat.toSSet.map (Work.Homology.incl A)).app k) := fun k => by
    rw [mono_iff_injective]
    intro x y h
    apply (TopCat.toSSetObjEquiv (TopCat.of A) k).injective
    apply ContinuousMap.ext
    intro z
    have hz := congrArg (fun w => TopCat.toSSetObjEquiv X k w z) h
    rw [toSSetObjEquiv_map_apply, toSSetObjEquiv_map_apply] at hz
    exact Subtype.coe_injective hz
  exact NatTrans.mono_of_mono_app _

/-- The inclusion of a subspace of a topological space induces a monomorphism of singular
chain complexes in every degree. -/
theorem mono_inclChain_f_aux (X : TopCat) (A : Set X) (n : ℕ) :
    Mono ((Work.Homology.inclChain Work.Homology.ZMod X A).f n) := by
  haveI : Mono (TopCat.toSSet.map (Work.Homology.incl A)) := mono_toSSet_map_incl X A
  exact Functor.map_mono (sigmaConst.obj Work.Homology.ZMod) _

theorem simplexBoundaryChain_d (n : ℕ) :
    CategoryTheory.CategoryStruct.comp (Work.HomologyExtra.simplexBoundaryChain n)
      ((Work.Homology.singChain Work.Homology.ZMod (Work.HomologyExtra.boundarySpace (n + 1))).d n
        ((ComplexShape.down ℕ).next n)) = 0 := by
  have hmono : Mono ((Work.Homology.inclChain Work.Homology.ZMod (simplex (n + 1))
      (simplexBoundary (n + 1))).f ((ComplexShape.down ℕ).next n)) :=
    mono_inclChain_f_aux _ _ _
  apply (Preadditive.mono_iff_cancel_zero
    ((Work.Homology.inclChain Work.Homology.ZMod (simplex (n + 1))
      (simplexBoundary (n + 1))).f ((ComplexShape.down ℕ).next n))).1 hmono
  rw [Category.assoc, ← HomologicalComplex.Hom.comm
      (Work.Homology.inclChain Work.Homology.ZMod (simplex (n + 1))
        (simplexBoundary (n + 1))) n ((ComplexShape.down ℕ).next n),
    ← Category.assoc, simplexBoundaryChain_incl, Category.assoc,
    HomologicalComplex.d_comp_d (Work.Homology.singChain Work.Homology.ZMod (simplex (n + 1)))
      (n + 1) n ((ComplexShape.down ℕ).next n),
    Limits.comp_zero]

end

end Work.HomologyExtra
