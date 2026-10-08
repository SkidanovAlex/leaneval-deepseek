import Mathlib

set_option linter.style.haveILetI false

namespace Work.CORE4

/-- If `X ≤ Y`, then `X.subgroupOf Y` has the same cardinality as `X`. -/
private lemma card_subgroupOf_of_le {G : Type*} [Group G] {X Y : Subgroup G} (h : X ≤ Y) :
    Nat.card ↥(X.subgroupOf Y) = Nat.card ↥X := by
  have h1 := Subgroup.card_map_of_injective (f := Y.subtype) (K := X.subgroupOf Y)
    Y.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le h] at h1
  exact h1.symm

/-- In a finite group, two subgroups of a common cyclic subgroup `N` that have the same
cardinality coincide: a finite cyclic group has at most one subgroup of each order. -/
private lemma eq_of_card_eq_of_isCyclic_le {G : Type*} [Group G] [Finite G] {N : Subgroup G}
    (hN : IsCyclic ↥N) {A B : Subgroup G} (hA : A ≤ N) (hB : B ≤ N)
    (hcard : Nat.card ↥A = Nat.card ↥B) : A = B := by
  haveI : IsCyclic ↥N := hN
  have hcard' : Nat.card ↥(A.subgroupOf N) = Nat.card ↥(B.subgroupOf N) := by
    rw [card_subgroupOf_of_le hA, card_subgroupOf_of_le hB, hcard]
  have hsub : A.subgroupOf N = B.subgroupOf N :=
    IsCyclic.subgroup_eq_iff_card_eq.mpr hcard'
  calc A = Subgroup.map N.subtype (A.subgroupOf N) := (Subgroup.map_subgroupOf_eq_of_le hA).symm
    _ = Subgroup.map N.subtype (B.subgroupOf N) := by rw [hsub]
    _ = B := Subgroup.map_subgroupOf_eq_of_le hB

/-- If `N` is a cyclic subgroup of a finite group `G`, `X ≤ N` has prime order `p`, and
`C ≤ N` meets `X` trivially, then `p` does not divide `|C|`.

Indeed, if `p ∣ |C|` then `C` contains a subgroup of order `p`; in the cyclic `N` the unique
subgroup of order `p` is `X`, so `X ≤ C`, contradicting `C ⊓ X = ⊥`. -/
theorem CyclicNotDvd {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) {N X C : Subgroup G} (hcyc : IsCyclic ↥N) (hXcard : Nat.card X = p) (hXN : X ≤ N) (hCN : C ≤ N) (hCX : C ⊓ X = ⊥) : ¬ p ∣ Nat.card C := by
  intro hpdvd
  -- A subgroup `K ≤ C` of order `p` exists (Sylow's first theorem in the special case `n = 1`).
  obtain ⟨K, hKcard, -, hKC⟩ :=
    Sylow.exists_subgroup_card_pow_prime_le_le hp (n := 1) (H := ⊥) (L := C)
      (by rw [Subgroup.card_bot]; exact one_dvd _) (by simpa using hpdvd) bot_le
  -- Uniqueness of the subgroup of order `p` in the cyclic `N` forces `K = X`.
  have hKN : K ≤ N := le_trans hKC hCN
  have hKeq : K = X :=
    eq_of_card_eq_of_isCyclic_le hcyc hKN hXN (by rw [hKcard, hXcard, pow_one])
  have hXC : X ≤ C := hKeq ▸ hKC
  -- Hence `X ≤ C ⊓ X = ⊥`, so `X = ⊥` and `p = |X| = 1`, contradiction.
  have hXbot : X ≤ (⊥ : Subgroup G) := by
    rw [← hCX]
    exact le_inf hXC le_rfl
  have hXeq : X = ⊥ := le_bot_iff.mp hXbot
  have hone : p = 1 := by rw [← hXcard, hXeq, Subgroup.card_bot]
  exact hp.ne_one hone

end Work.CORE4
