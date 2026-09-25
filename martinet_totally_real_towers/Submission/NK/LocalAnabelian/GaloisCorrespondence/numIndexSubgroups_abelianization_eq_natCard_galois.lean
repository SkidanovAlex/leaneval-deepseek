import Mathlib
import Submission.NK.LocalAnabelian.Basic

open scoped Classical

namespace NK.LocalAnabelian.GaloisCorrespondence

open IntermediateField

/-! # Index-`p` subgroups of the abelianisation and degree-`p` Galois subextensions

The Galois correspondence of infinite Galois theory matches intermediate fields
of a Galois extension `K'/k` with *closed* subgroups of `Gal(K'/k)`.  Passing to
the abelianisation `Gal(K'/k)ᵃᵇ = Gal(K'/k) ⧸ [Gal(K'/k), Gal(K'/k)]` replaces
"closed" by "normal and of prime index": a subgroup of index `p` (`p` prime) of an
abstract group contains the commutator subgroup exactly when it is normal, and
then it corresponds to an index-`p` subgroup of the abelianisation.

Hence, provided every index-`p` normal subgroup of `Gal(K'/k)` is closed (true
for the absolute Galois group of a `p`-adic field, by Nikolov–Segal), the number
of index-`p` subgroups of `Gal(K'/k)ᵃᵇ` equals the number of degree-`p` Galois
intermediate fields `k ⊆ L ⊆ K'`. -/

/-- A normal subgroup of prime index contains the commutator subgroup: the
quotient is a group of prime order, hence cyclic, hence commutative. -/
lemma commutator_le_of_normal_index_eq_prime {G : Type*} [Group G] {K : Subgroup G}
    (hN : K.Normal) {p : ℕ} (hp : p.Prime) (hK : K.index = p) : commutator G ≤ K := by
  have hp' : Fact p.Prime := ⟨hp⟩
  have := hN
  have hcard : Nat.card (G ⧸ K) = p := by rw [← Subgroup.index_eq_card]; exact hK
  have hcyc : IsCyclic (G ⧸ K) := isCyclic_of_prime_card hcard
  exact (Subgroup.Normal.quotient_commutative_iff_commutator_le (G := G) (N := K)).mp
    hcyc.isMulCommutative

/-- **Index-`p` subgroups of the abelianisation.**  Subgroups of index `p` of
`Abelianization G = G ⧸ [G, G]` are the same thing as *normal* subgroups of `G`
of index `p`; passing through the commutator subgroup gives the equivalence. -/
lemma numIndexSubgroups_abelianization_eq_natCard_normal_indexPrime {G : Type*} [Group G]
    (p : ℕ) (hp : p.Prime) :
    numIndexSubgroups p (Abelianization G) =
      Nat.card {K : Subgroup G // K.index = p ∧ K.Normal} := by
  classical
  unfold numIndexSubgroups
  refine Nat.card_congr ?_
  let f : G →* Abelianization G := Abelianization.of
  have hf : Function.Surjective f := fun x => Quotient.inductionOn x fun g => ⟨g, rfl⟩
  have hker : f.ker = commutator G := Abelianization.ker_of G
  have hker_le : ∀ K : {K : Subgroup G // K.index = p ∧ K.Normal}, f.ker ≤ K.1 := fun K =>
    hker.trans_le (commutator_le_of_normal_index_eq_prime K.2.2 hp K.2.1)
  refine
    { toFun := fun H =>
        ⟨H.1.comap f, (Subgroup.index_comap_of_surjective H.1 hf).trans H.2, inferInstance⟩
      invFun := fun K =>
        ⟨K.1.map f, (Subgroup.index_map_eq K.1 hf (hker_le K)).trans K.2.1⟩
      left_inv := fun H => by
        refine Subtype.ext ?_
        show (H.1.comap f).map f = H.1
        exact Subgroup.map_comap_eq_self_of_surjective hf H.1
      right_inv := fun K => by
        refine Subtype.ext ?_
        show (K.1.map f).comap f = K.1
        rw [Subgroup.comap_map_eq, sup_eq_left.mpr (hker_le K)] }

/-- **Normal index-`p` subgroups are degree-`p` Galois subextensions.**  The
order-reversing Galois correspondence restricts to an equivalence between closed
normal subgroups of index `p` and intermediate fields which are Galois of degree
`p` over `k`, using that a closed subgroup is normal in `Gal(K'/k)` exactly when
its fixed field is Galois over `k`. -/
lemma numIndexNormalSubgroups_eq_natCard_isGalois_finrank {k K' : Type*} [Field k] [Field K']
    [Algebra k K'] [IsGalois k K'] (p : ℕ)
    (hclosed : ∀ H : Subgroup (Gal(K'/k)), H.index = p → H.Normal →
      IsClosed (H : Set (Gal(K'/k)))) :
    Nat.card {K : Subgroup (Gal(K'/k)) // K.index = p ∧ K.Normal} =
      Nat.card {L : IntermediateField k K' // IsGalois k L ∧ Module.finrank k L = p} := by
  classical
  -- Normal index-`p` subgroups are closed, and conversely.
  have hmiddle : Nat.card {K : Subgroup (Gal(K'/k)) // K.index = p ∧ K.Normal} =
      Nat.card {H : ClosedSubgroup (Gal(K'/k)) //
        (H : Subgroup (Gal(K'/k))).index = p ∧ (H : Subgroup (Gal(K'/k))).Normal} := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun K => ⟨⟨K.1, hclosed K.1 K.2.1 K.2.2⟩, K.2.1, K.2.2⟩
        invFun := fun H => ⟨(H.1 : Subgroup (Gal(K'/k))), H.2.1, H.2.2⟩
        left_inv := fun K => Subtype.ext rfl
        right_inv := fun H => Subtype.ext rfl }
  rw [hmiddle]
  -- The Galois correspondence.
  let Φ : ClosedSubgroup (Gal(K'/k)) ≃ IntermediateField k K' :=
    { toFun := fun H => IntermediateField.fixedField (H : Subgroup (Gal(K'/k)))
      invFun := fun L => ⟨L.fixingSubgroup, InfiniteGalois.fixingSubgroup_isClosed L⟩
      left_inv := fun H =>
        ClosedSubgroup.toSubgroup_injective (InfiniteGalois.fixingSubgroup_fixedField H)
      right_inv := fun L => InfiniteGalois.fixedField_fixingSubgroup L }
  refine Nat.card_congr (Equiv.subtypeEquiv Φ ?_)
  intro H
  change (H : Subgroup (Gal(K'/k))).index = p ∧ (H : Subgroup (Gal(K'/k))).Normal ↔
    IsGalois k ↥(IntermediateField.fixedField (H : Subgroup (Gal(K'/k)))) ∧
      Module.finrank k ↥(IntermediateField.fixedField (H : Subgroup (Gal(K'/k)))) = p
  have hfix : (IntermediateField.fixedField (H : Subgroup (Gal(K'/k)))).fixingSubgroup
      = (H : Subgroup (Gal(K'/k))) := InfiniteGalois.fixingSubgroup_fixedField H
  have hfin : Module.finrank k ↥(IntermediateField.fixedField (H : Subgroup (Gal(K'/k))))
      = (H : Subgroup (Gal(K'/k))).index := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index (F := k) (E' := K')
      (L := IntermediateField.fixedField (H : Subgroup (Gal(K'/k)))), hfix]
  have hgal : IsGalois k ↥(IntermediateField.fixedField (H : Subgroup (Gal(K'/k))))
      ↔ (H : Subgroup (Gal(K'/k))).Normal := by
    have h := (InfiniteGalois.normal_iff_isGalois
      (IntermediateField.fixedField (H : Subgroup (Gal(K'/k))))).symm
    rwa [hfix] at h
  constructor
  · rintro ⟨hi, hn⟩; exact ⟨hgal.mpr hn, by rw [hfin]; exact hi⟩
  · rintro ⟨hg, hf⟩; exact ⟨by rw [← hfin]; exact hf, hgal.mp hg⟩

theorem numIndexSubgroups_abelianization_eq_natCard_galois {k K' : Type*} [Field k] [Field K']
    [Algebra k K'] [IsGalois k K'] (p : ℕ) (hp : p.Prime)
    (hclosed : ∀ H : Subgroup (Gal(K'/k)), H.index = p → H.Normal →
      IsClosed (H : Set (Gal(K'/k)))) :
    numIndexSubgroups p (Abelianization (Gal(K'/k))) =
      Nat.card {L : IntermediateField k K' // IsGalois k L ∧ Module.finrank k L = p} := by
  rw [numIndexSubgroups_abelianization_eq_natCard_normal_indexPrime (G := Gal(K'/k)) p hp]
  exact numIndexNormalSubgroups_eq_natCard_isGalois_finrank p hclosed

end NK.LocalAnabelian.GaloisCorrespondence
