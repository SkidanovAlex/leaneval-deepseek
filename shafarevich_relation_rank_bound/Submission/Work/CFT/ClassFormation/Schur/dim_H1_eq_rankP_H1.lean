import Mathlib
import Submission.Work.CFT.ClassFormation.Defs
import Submission.Work.CFT.ClassFormation.Schur.finrank_addHom_eq_finrank_tensor
import Submission.Work.CFT.ClassFormation.Schur.finrank_addHom_abelianization

namespace Work.CFT.ClassFormation.Schur

open scoped TensorProduct

/-!
# `H¹(G, 𝔽_p)` is the `p`-rank of `H₁(G, ℤ)`

This file proves

`dim_{𝔽_p} H¹(G, 𝔽_p) = rankP p (H₁(G, ℤ))`

for a finite group `G` and a prime `p`, where `H¹` is group cohomology with trivial `𝔽_p`
coefficients, `H₁` is group homology with trivial `ℤ` coefficients, and `rankP p A` is
`dim_{𝔽_p} (𝔽_p ⊗_ℤ A)`.

The proof chains three standard identifications.

1. For trivial coefficients, `H¹(G, 𝔽_p) = Hom(G, 𝔽_p)`
   (`groupCohomology.H1IsoOfIsTrivial`).
2. `Hom(G, 𝔽_p) = Hom(Gᵃᵇ, 𝔽_p)`, since `𝔽_p` is abelian: homomorphisms out of `G` into an
   abelian group factor uniquely through the abelianization (`Abelianization.lift`);
   see `finrank_addHom_abelianization`.
3. For any abelian group `A`, `dim_{𝔽_p} Hom(A, 𝔽_p) = dim_{𝔽_p} (𝔽_p ⊗_ℤ A)`: the
   extension-of-scalars adjunction gives `Hom_ℤ(A, 𝔽_p) ≅ Hom_{𝔽_p}(𝔽_p ⊗_ℤ A, 𝔽_p)`, the
   `𝔽_p`-linear dual, and `dim V* = dim V` over a field; see
   `finrank_addHom_eq_finrank_tensor`.
4. Finally `H₁(G, ℤ) ≅ Gᵃᵇ` (`groupHomology.H1AddEquivOfIsTrivial`), and tensoring with `ℤ`
   changes nothing: `𝔽_p ⊗_ℤ H₁(G, ℤ) ≅ 𝔽_p ⊗_ℤ Gᵃᵇ`.
-/

/-- `H₁(G, ℤ) ≅ Gᵃᵇ`, as an additive equivalence.  This is
`groupHomology.H1AddEquivOfIsTrivial` composed with the cancellation `M ⊗[ℤ] ℤ ≅ M`. -/
private noncomputable def H1ZAddEquiv (G : Type) [Group G] :
    (HnZ G 1 : Type) ≃+ Additive (Abelianization G) :=
  (groupHomology.H1AddEquivOfIsTrivial (Rep.trivial ℤ G ℤ)).trans
    (TensorProduct.rid ℤ (Additive (Abelianization G))).toAddEquiv

/-- Tensoring an additive equivalence with `𝔽_p` gives an `𝔽_p`-linear equivalence.  The
underlying `ℤ`-linear equivalence is automatically `𝔽_p`-linear because both sides are
`𝔽_p`-modules. -/
private noncomputable def tensorCongrEquivGen (p : ℕ) {A B : Type} [AddCommGroup A]
    [AddCommGroup B] (e : A ≃+ B) :
    (TensorProduct ℤ (ZMod p) A) ≃ₗ[ZMod p] (TensorProduct ℤ (ZMod p) B) :=
  { (TensorProduct.congr (LinearEquiv.refl ℤ (ZMod p)) (e.toIntLinearEquiv)).toAddEquiv with
    map_smul' := fun c x => by simpa using ZMod.map_smul _ c x }

/-- Transport of `finrank` along an additive equivalence, after tensoring with `𝔽_p`. -/
private theorem finrank_tensor_congr (p : ℕ) {A B : Type} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) :
    Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) A) =
      Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) B) :=
  LinearEquiv.finrank_eq (tensorCongrEquivGen p e)

/-- **`H¹` is the `p`-rank of `H₁`.**  For a finite group `G` and a prime `p`, with trivial
`𝔽_p` coefficients, `H¹(G, 𝔽_p) = Hom(G, 𝔽_p) = Hom(G^ab, 𝔽_p)`, and for a finite abelian group
`A` one has `dim_𝔽_p Hom(A, 𝔽_p) = dim_𝔽_p (A ⊗_ℤ 𝔽_p)` (tensor–hom adjunction plus
`Hom_𝔽_p(V,𝔽_p) ≅ V` in finite dimension).  With `H₁(G, ℤ) = G^ab` this gives
`dim H¹(G, 𝔽_p) = rankP p (H_1(G, ℤ))`.  Suggested route: use
`groupCohomology.H1IsoOfIsTrivial` and `groupHomology.H1AddEquivOfIsTrivial`, then the
tensor–hom adjunction isomorphism `Hom_ℤ(A, 𝔽_p) ≅ Hom_ℤ(A ⊗_ℤ 𝔽_p, 𝔽_p)`. -/
theorem dim_H1_eq_rankP_H1 (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G] :
    Module.finrank (ZMod p) (Work.CFT.ClassFormation.HnFp p G 1) =
      Work.CFT.ClassFormation.rankP p (Work.CFT.ClassFormation.HnZ G 1 : Type) := by
  -- `H¹(G, 𝔽_p) ≅ Hom(G, 𝔽_p)`
  have h1 := LinearEquiv.finrank_eq
    (groupCohomology.H1IsoOfIsTrivial (Rep.trivial (ZMod p) G (ZMod p))).toLinearEquiv
  -- `Hom(G, 𝔽_p) ≅ Hom(Gᵃᵇ, 𝔽_p)`
  have h2 := finrank_addHom_abelianization p G
  -- `dim Hom(Gᵃᵇ, 𝔽_p) = dim (𝔽_p ⊗_ℤ Gᵃᵇ)`
  have h3 := finrank_addHom_eq_finrank_tensor p (Additive (Abelianization G))
  -- `𝔽_p ⊗_ℤ H₁(G, ℤ) ≅ 𝔽_p ⊗_ℤ Gᵃᵇ`
  have h4 := (finrank_tensor_congr p (H1ZAddEquiv G)).symm
  simp only [Work.CFT.ClassFormation.rankP]
  exact h1.trans (h2.trans (h3.trans h4))

end Work.CFT.ClassFormation.Schur
