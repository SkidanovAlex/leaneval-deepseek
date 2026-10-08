import Mathlib

namespace Work.BG

open scoped Pointwise

/-- If `K` normalizes `H` and `H ⊓ K = ⊥`, then `H ⊔ K` is (the underlying set of) the
product `H * K`, so `|H ⊔ K| = |H| * |K|`.  This is the universe-general form of
`Work.BSW.Api.card_sup_of_le_normalizer_of_inf_eq_bot`. -/
theorem card_sup_of_le_normalizer_inf_eq_bot {G : Type*} [Group G] [Finite G]
    {H K : Subgroup G} (hn : K ≤ Subgroup.normalizer (H : Set G)) (hd : H ⊓ K = ⊥) :
    Nat.card ↥(H ⊔ K) = Nat.card ↥H * Nat.card ↥K := by
  -- `K` normalizes `H`, so `H ⊔ K = H * K` as sets.
  have hcoe : (↑(H ⊔ K) : Set G) = (H : Set G) * (K : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left H K hn
  have hdj : Disjoint H K := disjoint_iff.mpr hd
  -- Multiplication `H × K → ↥(H ⊔ K)` is a bijection.
  have hbij : Function.Bijective
      (fun x : H × K => (⟨(x.1 : G) * x.2, Subgroup.mul_mem_sup x.1.2 x.2.2⟩ : ↥(H ⊔ K))) := by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      exact Subgroup.mul_injective_of_disjoint hdj (Subtype.ext_iff.mp hxy)
    · intro z
      have hz : (z : G) ∈ (H : Set G) * (K : Set G) := hcoe ▸ z.2
      obtain ⟨h, hh, k, hk, hk_eq⟩ := Set.mem_mul.mp hz
      exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), Subtype.ext hk_eq⟩
  calc Nat.card ↥(H ⊔ K) = Nat.card (H × K) := Nat.card_congr (Equiv.ofBijective _ hbij).symm
    _ = Nat.card ↥H * Nat.card ↥K := Nat.card_prod _ _

/-- Multiplicativity of the index `[A ⊔ B : C]` when `C = (C ⊓ A) ⊔ (C ⊓ B)` is a "product"
of its intersections with `A` and `B`, with `B` normalizing `A` and `C ⊓ B` normalizing
`C ⊓ A`.  Concretely `[A ⊔ B : C] = [A : C ⊓ A] * [B : C ⊓ B]`. -/
theorem relIndexSupDecomposition {G : Type*} [Group G] [Finite G]
    {A B C : Subgroup G} (hB : B ≤ Subgroup.normalizer (A : Set G)) (hAB : A ⊓ B = ⊥)
    (hC : C = (C ⊓ A) ⊔ (C ⊓ B)) (hCA : C ⊓ B ≤ Subgroup.normalizer (C ⊓ A : Subgroup G))
    (hCinf : (C ⊓ A) ⊓ (C ⊓ B) = ⊥) :
    C.relIndex (A ⊔ B) = (C ⊓ A).relIndex A * (C ⊓ B).relIndex B := by
  -- `C` is contained in `A ⊔ B`, so the relative index `[A ⊔ B : C]` is the plain index.
  have hCle : C ≤ A ⊔ B :=
    le_trans (le_of_eq hC)
      (sup_le (le_trans inf_le_right le_sup_left) (le_trans inf_le_right le_sup_right))
  have hCinfAB : C ⊓ (A ⊔ B) = C := inf_eq_left.mpr hCle
  -- Cardinalities: `|A ⊔ B| = |A| * |B|` and `|C| = |(C ⊓ A)| * |(C ⊓ B)|`.
  have hcardAB : Nat.card ↥(A ⊔ B) = Nat.card ↥A * Nat.card ↥B :=
    card_sup_of_le_normalizer_inf_eq_bot hB hAB
  have hcardCint : Nat.card ↥(C ⊓ (A ⊔ B)) = Nat.card ↥(C ⊓ A) * Nat.card ↥(C ⊓ B) :=
    (congrArg (fun X : Subgroup G => Nat.card ↥X) (hCinfAB.trans hC)).trans
      (card_sup_of_le_normalizer_inf_eq_bot hCA hCinf)
  -- Index times cardinality equals cardinality.
  have hA : (C ⊓ A).relIndex A * Nat.card ↥(C ⊓ A) = Nat.card ↥A := by
    have h := Subgroup.relIndex_mul_card (H := C ⊓ A) (K := A)
    have he : Nat.card ↥((C ⊓ A) ⊓ A) = Nat.card ↥(C ⊓ A) :=
      congrArg (fun X : Subgroup G => Nat.card ↥X)
        (inf_eq_left.mpr (inf_le_right : C ⊓ A ≤ A))
    rw [he] at h
    exact h
  have hB' : (C ⊓ B).relIndex B * Nat.card ↥(C ⊓ B) = Nat.card ↥B := by
    have h := Subgroup.relIndex_mul_card (H := C ⊓ B) (K := B)
    have he : Nat.card ↥((C ⊓ B) ⊓ B) = Nat.card ↥(C ⊓ B) :=
      congrArg (fun X : Subgroup G => Nat.card ↥X)
        (inf_eq_left.mpr (inf_le_right : C ⊓ B ≤ B))
    rw [he] at h
    exact h
  -- Both sides, multiplied by `|C ⊓ A| * |C ⊓ B|`, equal `|A ⊔ B|`.
  have key1 : C.relIndex (A ⊔ B) * (Nat.card ↥(C ⊓ A) * Nat.card ↥(C ⊓ B)) =
      Nat.card ↥(A ⊔ B) := by
    have h := Subgroup.relIndex_mul_card (H := C) (K := A ⊔ B)
    rw [hcardCint] at h
    exact h
  have key2 : ((C ⊓ A).relIndex A * (C ⊓ B).relIndex B)
        * (Nat.card ↥(C ⊓ A) * Nat.card ↥(C ⊓ B)) = Nat.card ↥(A ⊔ B) := by
    calc ((C ⊓ A).relIndex A * (C ⊓ B).relIndex B)
            * (Nat.card ↥(C ⊓ A) * Nat.card ↥(C ⊓ B))
        = ((C ⊓ A).relIndex A * Nat.card ↥(C ⊓ A))
            * ((C ⊓ B).relIndex B * Nat.card ↥(C ⊓ B)) :=
          mul_mul_mul_comm _ _ _ _
      _ = Nat.card ↥A * Nat.card ↥B := by rw [hA, hB']
      _ = Nat.card ↥(A ⊔ B) := hcardAB.symm
  -- Cancel the common positive factor.
  have hpos : 0 < Nat.card ↥(C ⊓ A) * Nat.card ↥(C ⊓ B) := by
    have h1 : 0 < Nat.card ↥(C ⊓ A) := Nat.card_pos
    have h2 : 0 < Nat.card ↥(C ⊓ B) := Nat.card_pos
    positivity
  exact Nat.mul_right_cancel hpos (key1.trans key2.symm)

end Work.BG
