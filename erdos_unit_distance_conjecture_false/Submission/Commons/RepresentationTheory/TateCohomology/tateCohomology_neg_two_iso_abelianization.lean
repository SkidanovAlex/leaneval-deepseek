import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic

/-!
# The canonical identification `Ĥ^{-2}(G, ℤ) ≅ Gᵃᵇ`

For a finite group `G` and trivial coefficients `ℤ`, the `(-2)`-nd Tate cohomology group of `G`
is the abelianisation of `G`.  This is the degree `-2` case of the standard shift isomorphism
`Ĥ^{-n-1}(G, ℤ) ≅ Hₙ(G, ℤ)` (`n ≥ 1`) combined with the low-degree computation
`H₁(G, ℤ) ≅ Gᵃᵇ ⊗[ℤ] ℤ ≅ Gᵃᵇ`.

In Mathlib both ingredients are available:

* `TateCohomology.isoGroupHomology (-2) 1` gives `Ĥ^{-2}(G, M) ≅ H₁(G, M)` naturally in `M`;
* `groupHomology.H1AddEquivOfIsTrivial` gives `H₁(G, A) ≃+ Gᵃᵇ ⊗[ℤ] A` for a trivial
  representation `A`, and for `A = ℤ` the tensor factor `ℤ` can be removed with
  `TensorProduct.rid`.

The composite of these two identifications is the statement below.
-/

namespace Commons.RepresentationTheory.TateCohomology

open CategoryTheory
open scoped TensorProduct

/-- The canonical identification `Ĥ^{-2}(G, ℤ) ≅ Gᵃᵇ` for a finite group `G`. -/
theorem tateCohomology_neg_two_iso_abelianization (G : Type) [Group G] [Fintype G] :
    Nonempty (tateCohomology (Rep.trivial ℤ G ℤ) (-2) ≃+ Additive (Abelianization G)) := by
  refine ⟨?_⟩
  -- The shift `Ĥ^{-n-1}(G, M) ≅ Hₙ(G, M)` in the case `n = 1`: `Ĥ^{-2}(G, ℤ) ≅ H₁(G, ℤ)`.
  have e1 : tateCohomology (Rep.trivial ℤ G ℤ) (-2) ≅
      groupHomology (Rep.trivial ℤ G ℤ) 1 :=
    (TateCohomology.isoGroupHomology (R := ℤ) (G := G) (-2) 1 (by norm_num)).app _
  -- For a trivial representation `A`, `H₁(G, A) ≃+ Gᵃᵇ ⊗[ℤ] A`; here `A = ℤ`.
  have e2 : groupHomology (Rep.trivial ℤ G ℤ) 1 ≃+
      (Additive (Abelianization G)) ⊗[ℤ] ℤ :=
    groupHomology.H1AddEquivOfIsTrivial (A := Rep.trivial ℤ G ℤ)
  -- Remove the trivial tensor factor `ℤ` from `Gᵃᵇ ⊗[ℤ] ℤ`.
  exact (e1.toLinearEquiv.toAddEquiv).trans
    (e2.trans (TensorProduct.rid ℤ (Additive (Abelianization G))).toAddEquiv)

end Commons.RepresentationTheory.TateCohomology