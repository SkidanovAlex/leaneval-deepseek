import Mathlib
import Submission.Work.SINGMV.Defs

/-!
# Injectivity of the map induced on singular chains by the inclusion of a subspace

For a topological space `X`, a subset `U ⊆ X` and `n : ℕ`, the induced map
`C_n(U) ⟶ C_n(X)` on integral singular `n`-chains is injective.

Mathematically: `C_n(X)` is the free abelian group on the continuous maps
`Δⁿ ⟶ X`, and the map in question sends the generator of `σ : Δⁿ ⟶ U` to the
generator of `U ↪ X ∘ σ`.  This assignment is injective on generators (because
`U ↪ X` is injective), hence the induced map of free abelian groups is injective.

Formally, we use Mathlib's simplicial chain complex: `singC` is the composite
`TopCat.toSSet ⋙ SSet.chainComplex (ModuleCat ℤ)`, so the map in question is
`SSet.chainComplexMap (toSSet.map f) R`.  The inclusion `inclTop U` is a
monomorphism in `TopCat`, `TopCat.toSSet` carries it to a monomorphism of
simplicial sets, and — because `ModuleCat ℤ` has coproducts in which the
inclusions of the summands are monomorphisms (`MonoCoprod`) — the chain map of a
monomorphism of simplicial sets is degreewise a monomorphism
(`Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative`, via `SSetPair`).
A monomorphism in `ModuleCat ℤ` is exactly an injective linear map.
-/

namespace Work.SingMV

open CategoryTheory Limits

/-- The inclusion of a subspace is a monomorphism of topological spaces, i.e. an injective map. -/
instance mono_inclTop (X : TopCat) (U : Set X) : Mono (Submission.Blueprint.inclTop U) := by
  rw [TopCat.mono_iff_injective]
  exact Subtype.val_injective

theorem injective_map_inclTop (X : TopCat) (n : ℕ) (U : Set X) :
    Function.Injective
      (((Submission.Blueprint.singC).map (Submission.Blueprint.inclTop U)).f n).hom := by
  refine (ModuleCat.mono_iff_injective _).mp ?_
  -- `singC` is the simplicial chain complex functor applied to `toSSet.map`,
  -- and the chain map of a monomorphism of simplicial sets is degreewise a monomorphism.
  exact inferInstanceAs (Mono ((SSet.chainComplexMap
      (SSetPair.of (TopCat.toSSet.map (Submission.Blueprint.inclTop U))).hom
      (ModuleCat.of ℤ ℤ)).f n))

end Work.SingMV
