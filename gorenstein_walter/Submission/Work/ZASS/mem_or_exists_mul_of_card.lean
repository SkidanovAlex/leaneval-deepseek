import Mathlib

namespace Work.ZASS

theorem mem_or_exists_mul_of_card {G : Type} [Group G] [Finite G] (B U : Subgroup G) (s : G)
    (hinj : Function.Injective (fun q : B × U => (q.1 : G) * s * (q.2 : G)))
    (hdis : ∀ b : B, ∀ u : U, (b : G) * s * (u : G) ∉ B)
    (hcard : Nat.card G = Nat.card B * Nat.card U + Nat.card B) :
    ∀ g : G, g ∈ B ∨ ∃ q : B × U, g = (q.1 : G) * s * (q.2 : G) := by
  classical
  -- The set `S = {b * s * u}` has cardinality `|B| * |U|` (injectivity), is disjoint from `B`
  -- (`hdis`), so `B ∪ S` has cardinality `|B| * |U| + |B| = |G|`; being a subset of `G` it is all
  -- of `G`.
  have hBcard : (B : Set G).ncard = Nat.card B := rfl
  set f : B × U → G := fun q => (q.1 : G) * s * (q.2 : G) with hf
  set S : Set G := f '' (Set.univ : Set (B × U)) with hS
  have hdisj : Disjoint (B : Set G) S := by
    rw [Set.disjoint_left]
    rintro x hxB ⟨q, -, rfl⟩
    exact hdis q.1 q.2 hxB
  have hBS : ((B : Set G) ∪ S).ncard = Nat.card B + Nat.card B * Nat.card U := by
    rw [Set.ncard_union_eq hdisj, hS, Set.ncard_image_of_injective _ hinj, Set.ncard_univ,
      Nat.card_prod, hBcard]
  have hEq : ((B : Set G) ∪ S) = Set.univ := by
    refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_
    rw [Set.ncard_univ, hBS, hcard]
    exact le_of_eq (Nat.add_comm _ _)
  intro g
  have hg : g ∈ (B : Set G) ∪ S := by rw [hEq]; trivial
  rcases hg with hgB | hgS
  · exact Or.inl hgB
  · right
    rw [hS, Set.mem_image] at hgS
    obtain ⟨q, -, hq⟩ := hgS
    exact ⟨q, hq.symm⟩

end Work.ZASS
