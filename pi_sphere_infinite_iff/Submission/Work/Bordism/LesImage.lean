import Mathlib
import Submission.Work.Cohomology.PairSequence
import Submission.Work.Cohomology.HomologyPairSequence

/-!
# The image of the restriction to the boundary, as a kernel (the long exact sequence of a pair)

For a space `X` and a subspace `A ⊆ X`, the long exact sequence of the pair in cohomology reads

`⋯ → Hᵏ(X,A) → Hᵏ(X) --restr--> Hᵏ(A) --pairδ--> Hᵏ⁺¹(X,A) → Hᵏ⁺¹(X) → ⋯`

so the **image of the restriction** `Hᵏ(X) → Hᵏ(A)` is exactly the **kernel of the connecting
homomorphism** `pairδ`.  In the geometry of bordism this is the classical description of the
Lagrangian of the middle form of a boundary: for a compact oriented `(2k+1)`-manifold `W` with
boundary `∂W`, the subspace

`K = image(Hᵏ(W) → Hᵏ(∂W)) = ker(Hᵏ(∂W) → Hᵏ⁺¹(W,∂W))`

is totally isotropic (because `[∂W]` is null-homologous in `W`) and half-dimensional (Lefschetz
duality); the isotropy is proved in `Submission/Work/Bordism/Middle.lean`
(`Work.Bordism.boundaryForm_middleMap_eq_zero`, for the middle comparison map `(iM*, iN*)` of a
bordism) and the half-dimensionality is the named hypothesis `Work.Bordism.HalfDimension`.

The homological counterpart (with `C_*(X,A)` the relative chains) is

`image(∂ : H_{k+1}(X,A) → H_k(A)) = ker(H_k(A) → H_k(X))`,

the image of the connecting homomorphism of the homology long exact sequence being exactly the
boundary classes that are null-homologous in `X` — which is what the relation `hbd` of
`Work.Bordism.Bordism` records (`(iM)_*[M] = (iN)_*[N]`).

Both statements are the `range = ker` form of the exactness of the long exact sequence of a pair
(`Work.Cohomology.pair_exact₃`, `Work.Cohomology.hPair_exact₁`).
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology

namespace Work.Bordism

open Work.Cohomology

noncomputable section

/-- **The image of the restriction to a subspace is the kernel of the connecting homomorphism**
(cohomology).  This is the classical description of the Lagrangian subspace of the middle form of a
boundary: `K = image(Hᵏ(W) → Hᵏ(∂W)) = ker(Hᵏ(∂W) → Hᵏ⁺¹(W,∂W))`. -/
theorem range_restr_eq_ker_pairDelta (X : TopCat) (A : Set X) (k : ℕ) :
    LinearMap.range ((HomologicalComplex.homologyMap (restr ℤ X A) k).hom) =
      LinearMap.ker ((pairδ ℤ X A k).hom) :=
  (ShortComplex.moduleCat_exact_iff_range_eq_ker
    (ShortComplex.mk (HomologicalComplex.homologyMap (restr ℤ X A) k) (pairδ ℤ X A k)
      (pair_comp_δ ℤ X A k))).mp (pair_exact₃ ℤ X A k)

/-- **The image of the connecting homomorphism of a pair is the kernel of the map induced by the
inclusion** (homology): `image(∂ : H_{k+1}(X,A) → H_k(A)) = ker(H_k(A) → H_k(X))`, i.e. the
boundary classes of `A` that are null-homologous in `X`. -/
theorem range_hPairDelta_eq_ker_incl (X : TopCat) (A : Set X) (k : ℕ) :
    LinearMap.range ((hPairδ X A k).hom) =
      LinearMap.ker ((HomologicalComplex.homologyMap (inclChains X A) k).hom) :=
  (ShortComplex.moduleCat_exact_iff_range_eq_ker
    (ShortComplex.mk (hPairδ X A k) (HomologicalComplex.homologyMap (inclChains X A) k)
      (hPairδ_comp X A k))).mp (hPair_exact₁ X A k)

end

end Work.Bordism
