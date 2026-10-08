import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausTwoGroup

/-- If every term of a finite sum of naturals is at least `1` and the sum equals the number
of terms, then every term is exactly `1`. -/
private lemma sum_eq_card_imp_eq_one {α : Type*} [DecidableEq α] {s : Finset α} {g : α → ℕ}
    (h : ∀ x ∈ s, 1 ≤ g x) (hs : ∑ x ∈ s, g x = s.card) :
    ∀ x ∈ s, g x = 1 := by
  intro a ha
  have herase : (s.erase a).card ≤ ∑ x ∈ s.erase a, g x := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum (fun x hx => h x (Finset.mem_of_mem_erase hx))
  have hcarderase : (s.erase a).card = s.card - 1 := Finset.card_erase_of_mem ha
  rw [hcarderase] at herase
  have hdecomp : g a + ∑ x ∈ s.erase a, g x = ∑ x ∈ s, g x := Finset.add_sum_erase s g ha
  have key : g a + (s.card - 1) ≤ s.card := by
    have h1 : g a + (s.card - 1) ≤ g a + ∑ x ∈ s.erase a, g x := Nat.add_le_add_left herase _
    rw [hdecomp, hs] at h1
    exact h1
  have hpos : 1 ≤ s.card := Finset.card_pos.mpr ⟨a, ha⟩
  have := h a ha
  omega

theorem counting_abstract {ι : Type} [Fintype ι] (c : ι → ℕ) (A B : Finset ι) (q : ℕ)
    (hsum : ∑ i, (c i) ^ 2 = q + 1) (hdisj : Disjoint A B)
    (hAcard : q ≤ A.card) (hAc : ∀ a ∈ A, 1 ≤ c a)
    (hB : B.Nonempty) (hBc : ∀ b ∈ B, 1 ≤ c b) :
    A.card = q ∧ B.card = 1 ∧ (∀ a ∈ A, c a = 1) ∧ (∀ b ∈ B, c b = 1) ∧
      (∀ i, i ∉ A → i ∉ B → c i = 0) := by
  classical
  -- Lower bound `card ≤ sum of squares` on each side.
  have hAterm : ∀ a ∈ A, (1 : ℕ) ≤ (c a) ^ 2 := fun a ha =>
    Nat.pow_le_pow_left (hAc a ha) 2
  have hBterm : ∀ b ∈ B, (1 : ℕ) ≤ (c b) ^ 2 := fun b hb =>
    Nat.pow_le_pow_left (hBc b hb) 2
  have hSA : A.card ≤ ∑ a ∈ A, (c a) ^ 2 := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum (fun a ha => hAterm a ha)
  have hSB : B.card ≤ ∑ b ∈ B, (c b) ^ 2 := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum (fun b hb => hBterm b hb)
  -- The two blocks are disjoint inside the whole index set.
  have hsub : (∑ a ∈ A, (c a) ^ 2) + (∑ b ∈ B, (c b) ^ 2) ≤ ∑ i, (c i) ^ 2 := by
    rw [← Finset.sum_union hdisj]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => Nat.zero_le _)
  have hBcard : 1 ≤ B.card := Finset.Nonempty.card_pos hB
  -- Everything is pinched.
  have hAB : A.card + B.card = q + 1 := by
    have hle : A.card + B.card ≤ q + 1 := by
      calc A.card + B.card
          ≤ (∑ a ∈ A, (c a) ^ 2) + (∑ b ∈ B, (c b) ^ 2) := add_le_add hSA hSB
        _ ≤ ∑ i, (c i) ^ 2 := hsub
        _ = q + 1 := hsum
    have hge : q + 1 ≤ A.card + B.card := by omega
    omega
  have hAcard_eq : A.card = q := by omega
  have hBcard_eq : B.card = 1 := by omega
  have hSAeq : (∑ a ∈ A, (c a) ^ 2) = A.card := by
    have hle : (∑ a ∈ A, (c a) ^ 2) ≤ A.card := by
      have h1 := hsub
      have := hSB
      have := hAB
      have := hsum
      omega
    omega
  have hSBeq : (∑ b ∈ B, (c b) ^ 2) = B.card := by
    have hle : (∑ b ∈ B, (c b) ^ 2) ≤ B.card := by
      have h1 := hsub
      have := hSA
      have := hAB
      have := hsum
      omega
    omega
  refine ⟨hAcard_eq, hBcard_eq, ?_, ?_, ?_⟩
  · intro a ha
    have h1 : (c a) ^ 2 = 1 :=
      sum_eq_card_imp_eq_one (g := fun x => (c x) ^ 2) hAterm hSAeq a ha
    rcases Nat.pow_eq_one.mp h1 with h2 | h2
    · exact h2
    · norm_num at h2
  · intro b hb
    have h1 : (c b) ^ 2 = 1 :=
      sum_eq_card_imp_eq_one (g := fun x => (c x) ^ 2) hBterm hSBeq b hb
    rcases Nat.pow_eq_one.mp h1 with h2 | h2
    · exact h2
    · norm_num at h2
  · -- The complement of `A ∪ B` carries total weight zero.
    intro i hiA hiB
    have hcompl : ∑ j ∈ (A ∪ B)ᶜ, (c j) ^ 2 = 0 := by
      have hdecomp := Finset.sum_add_sum_compl (A ∪ B) (fun j => (c j) ^ 2)
      rw [Finset.sum_union hdisj, hSAeq, hSBeq, hsum, hAB] at hdecomp
      omega
    have hi : i ∈ (A ∪ B)ᶜ := by
      simp only [Finset.mem_compl, Finset.mem_union, not_or]
      exact ⟨hiA, hiB⟩
    have hzero : (c i) ^ 2 = 0 := (Finset.sum_eq_zero_iff.mp hcompl) i hi
    rw [pow_two, mul_self_eq_zero] at hzero
    exact hzero

end Work.ZassenhausTwoGroup
