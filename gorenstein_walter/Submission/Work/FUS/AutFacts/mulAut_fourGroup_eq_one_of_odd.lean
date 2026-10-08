import Mathlib

set_option linter.style.haveILetI false

namespace Work.FUS.AutFacts

/-- If `V` is a finite group of order `4` in which every element is an involution
(`v ^ 2 = 1`), then any automorphism `β` of `V` of odd order that fixes a non-identity
element `t` must be the identity.

The proof is elementary: `V` has exactly four elements `1, t, u, t * u` for any
`u ∉ {1, t}`. Since `β` fixes `1` and `t` and is a bijection, it maps the two-element
set `{u, t * u}` into itself, hence `β` has order dividing `2`; combined with the
oddness of `orderOf β` this forces `β = 1`. -/
theorem mulAut_fourGroup_eq_one_of_odd {V : Type*} [Group V] [Finite V] (hV : Nat.card V = 4)
    (hV2 : ∀ v : V, v ^ 2 = 1) (t : V) (ht : t ≠ 1) (β : V ≃* V) (hβt : β t = t)
    (hodd : Odd (orderOf β)) : β = 1 := by
  classical
  haveI := Fintype.ofFinite V
  have hcard : Fintype.card V = 4 := by
    rw [← Nat.card_eq_fintype_card]; exact hV
  -- produce an element `u` distinct from `1` and `t`
  obtain ⟨u, hu1, hut⟩ : ∃ u : V, u ≠ 1 ∧ u ≠ t := by
    by_contra h
    have hx' : ∀ x : V, x = 1 ∨ x = t := by
      intro x
      by_cases h1 : x = 1
      · exact Or.inl h1
      · by_cases h2 : x = t
        · exact Or.inr h2
        · exact (h ⟨x, h1, h2⟩).elim
    have hsub : (Finset.univ : Finset V) ⊆ ({1, t} : Finset V) := by
      intro x _
      rcases hx' x with hx | hx <;> simp [hx]
    have h2 : ({1, t} : Finset V).card = 2 := by
      rw [Finset.card_eq_two]; exact ⟨1, t, ht.symm, rfl⟩
    have hle := Finset.card_le_card hsub
    rw [Finset.card_univ, hcard, h2] at hle
    omega
  have ht2 : t * t = 1 := by rw [← pow_two]; exact hV2 t
  -- the four elements `1, t, u, t * u` are pairwise distinct
  have htu1 : t * u ≠ 1 := by
    intro h
    exact hut (mul_left_cancel (by rw [h, ht2]))
  have htut : t * u ≠ t := by
    intro h
    exact hu1 (mul_left_cancel (by rw [h, mul_one]))
  have htuu : t * u ≠ u := by
    intro h
    exact ht (mul_right_cancel (by rw [one_mul, h]))
  -- they exhaust `V`
  have hS : ({1, t, u, t * u} : Finset V) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hcard, Finset.card_eq_four]
    exact ⟨1, t, u, t * u, ht.symm, hu1.symm, htu1.symm, hut.symm, htut.symm, htuu.symm, rfl⟩
  have hmem : ∀ x : V, x = 1 ∨ x = t ∨ x = u ∨ x = t * u := by
    intro x
    have hx : x ∈ ({1, t, u, t * u} : Finset V) := by rw [hS]; exact Finset.mem_univ x
    simpa using hx
  -- `β` maps the two-element set `{u, t * u}` into itself
  have hβu : β u = u ∨ β u = t * u := by
    rcases hmem (β u) with h | h | h | h
    · exfalso; exact hu1 (β.injective (h.trans (map_one β).symm))
    · exfalso; exact hut (β.injective (h.trans hβt.symm))
    · exact Or.inl h
    · exact Or.inr h
  -- hence `β` is an involution
  have hxx : ∀ x : V, β (β x) = x := by
    intro x
    rcases hmem x with hx | hx | hx | hx
    · rw [hx]; simp
    · rw [hx, hβt, hβt]
    · rw [hx]
      rcases hβu with h | h
      · rw [h, h]
      · rw [h, map_mul, hβt, h, ← mul_assoc, ht2, one_mul]
    · rw [hx]
      rcases hβu with h | h
      · have htu : β (t * u) = t * u := by rw [map_mul, hβt, h]
        rw [htu, htu]
      · have htu : β (t * u) = u := by rw [map_mul, hβt, h, ← mul_assoc, ht2, one_mul]
        rw [htu, h]
  have hββ : β * β = 1 := by
    apply MulEquiv.ext
    intro x
    simpa using hxx x
  have hdvd : orderOf β ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_two]
    exact hββ
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exact orderOf_eq_one_iff.mp h1
  · exfalso
    rw [h2] at hodd
    obtain ⟨k, hk⟩ := hodd
    omega

end Work.FUS.AutFacts
