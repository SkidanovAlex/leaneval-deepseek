import Mathlib
import Submission.Commons.RepresentationTheory.TateCohomology.tateCohomology_neg_two_iso_abelianization

/-!
# `Ĥ^{-2}(G, ℤ)` for a finite abelian group

For a finite group `G`, the shared-commons lemma
`Commons.RepresentationTheory.TateCohomology.tateCohomology_neg_two_iso_abelianization`
identifies the `(-2)`-nd Tate cohomology group of the trivial integral representation with the
abelianisation `Gᵃᵇ` of `G`.  When `G` is commutative, `G ≃* Gᵃᵇ` (`Abelianization.equivOfComm`),
so `Ĥ^{-2}(G, ℤ)` has the same cardinality as `G`.
-/

namespace Commons.RepresentationTheory.TateCohomology

theorem natCard_tateCohomology_neg_two_of_commutative (G : Type) [Group G] [Fintype G]
    (hcomm : ∀ a b : G, a * b = b * a) :
    Nat.card (tateCohomology (Rep.trivial ℤ G ℤ) (-2)) = Nat.card G := by
  -- A commutative group, in the `CommGroup` form needed to invoke `Abelianization.equivOfComm`.
  letI : CommGroup G := { ‹Group G› with mul_comm := hcomm }
  -- `Ĥ^{-2}(G, ℤ) ≃+ Gᵃᵇ`.
  obtain ⟨e⟩ := tateCohomology_neg_two_iso_abelianization G
  calc Nat.card (tateCohomology (Rep.trivial ℤ G ℤ) (-2))
      = Nat.card (Additive (Abelianization G)) := Nat.card_congr e.toEquiv
    _ = Nat.card (Abelianization G) := Nat.card_congr Additive.toMul
    _ = Nat.card G := (Nat.card_congr (Abelianization.equivOfComm).toEquiv).symm

end Commons.RepresentationTheory.TateCohomology
