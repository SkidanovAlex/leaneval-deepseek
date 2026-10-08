import Mathlib

namespace Work.ZASS

open scoped Pointwise

/-- In a 2-pretransitive action, the setwise stabilizer of a two-element set `{a,b}` has exactly
twice the order of the pointwise stabilizer `G_{a,b} = G_a ⊓ G_b`: the orbit of `a` under the
setwise stabilizer is exactly `{a, b}`, and the stabilizer of `a` inside it is `G_{a,b}`.
(`open scoped Pointwise` is needed: the action of `G` on `Set X` is the scoped instance
`Set.mulActionSet`.) -/
theorem zass_setwiseStabCard {G X : Type} [Group G] [Finite G] [MulAction G X] {a b : X}
    (hab : a ≠ b) (hpre : MulAction.IsMultiplyPretransitive G X 2) :
    Nat.card (MulAction.stabilizer G ({a, b} : Set X)) =
      2 * Nat.card ↥(MulAction.stabilizer G a ⊓ MulAction.stabilizer G b) := by
  classical
  -- `S` is the setwise stabilizer of `{a,b}`, the group whose order we compute.
  set S : Subgroup G := MulAction.stabilizer G ({a, b} : Set X) with hS
  -- 2-transitivity provides an element swapping `a` and `b`.
  obtain ⟨g, hga, hgb⟩ := (MulAction.is_two_pretransitive_iff.mp hpre) hab hab.symm
  -- Membership in `S` means preserving the unordered pair `{a,b}`.
  have hsmulS : ∀ x : G, x ∈ S → x • ({a,b} : Set X) = {a,b} := by
    intro x hx
    exact (MulAction.mem_stabilizer_iff).mp (hS ▸ hx)
  have hgS : g ∈ S := by
    rw [hS, MulAction.mem_stabilizer_iff]
    simp only [Set.smul_set_insert, Set.smul_set_singleton, hga, hgb, Set.pair_comm]
  -- Key point: an element of `S` fixing `a` also fixes `b` (and conversely).
  have key : ∀ x : G, x ∈ S → x • a = a → x • b = b := by
    intro x hxS hxa
    have hmem : x • b ∈ ({a,b} : Set X) := by
      have := Set.smul_mem_smul_set (s := ({a,b} : Set X)) (a := x) (b := b) (by simp)
      rwa [hsmulS x hxS] at this
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h
    · exfalso
      exact hab (MulAction.injective x (by simp only [hxa, h]))
    · exact h
  -- The orbit of `a` under the setwise stabilizer is exactly the pair `{a,b}`.
  have horbit : MulAction.orbit ↥S a = ({a,b} : Set X) := by
    ext y
    constructor
    · intro hy
      rw [MulAction.mem_orbit_iff] at hy
      obtain ⟨s, hs⟩ := hy
      have hmem : (s : G) • a ∈ ({a,b} : Set X) := by
        have := Set.smul_mem_smul_set (s := ({a,b} : Set X)) (a := (s : G)) (b := a) (by simp)
        rwa [hsmulS (s : G) s.2] at this
      rw [← hs]
      exact hmem
    · intro hy
      rcases (by simpa using hy : y = a ∨ y = b) with h | h
      · rw [h]; exact MulAction.mem_orbit_self a
      · rw [h, MulAction.mem_orbit_iff]; exact ⟨⟨g, hgS⟩, hga⟩
  have hcard_orbit : Nat.card (MulAction.orbit ↥S a) = 2 := by
    rw [Nat.card_coe_set_eq, horbit, Set.ncard_pair hab]
  -- The stabilizer of `a` inside `S` is the pointwise stabilizer of `{a,b}`.
  have hstab_card : Nat.card ↥(MulAction.stabilizer ↥S a) =
      Nat.card ↥(MulAction.stabilizer G a ⊓ MulAction.stabilizer G b) := by
    have hmap : (MulAction.stabilizer ↥S a).map S.subtype =
        (MulAction.stabilizer G a ⊓ MulAction.stabilizer G b : Subgroup G) := by
      ext x
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨s, hs, rfl⟩
        rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
        exact ⟨hs, key (s : G) s.2 hs⟩
      · intro hx
        rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff] at hx
        obtain ⟨hxa, hxb⟩ := hx
        refine ⟨⟨x, ?_⟩, hxa, rfl⟩
        rw [hS, MulAction.mem_stabilizer_iff]
        simp only [Set.smul_set_insert, Set.smul_set_singleton, hxa, hxb, Set.pair_comm]
    have h1 := Subgroup.card_map_of_injective (K := MulAction.stabilizer ↥S a)
        (f := S.subtype) S.subtype_injective
    rw [← h1, hmap]
  -- Orbit–stabilizer for the action of `S` on `X`.
  have hos' : Nat.card ↥S = Nat.card (MulAction.orbit ↥S a) *
      Nat.card ↥(MulAction.stabilizer ↥S a) := by
    have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (G := ↥S) a)
    rw [Nat.card_prod] at h
    exact h.symm
  rw [hos', hcard_orbit, hstab_card]

end Work.ZASS
