import Mathlib
import Submission.Work.BG.Thm43Defs
import Submission.Work.BG.invJCard
import Submission.Work.BG.kappaExists

set_option linter.style.haveILetI false

namespace Work.BG

/-- A `Finset` with four pairwise distinct entries has cardinality four. -/
private lemma card_four {α : Type*} [DecidableEq α] (a b c d : α) (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ({a, b, c, d} : Finset α).card = 4 := by
  rw [Finset.card_insert_of_notMem (by simp [hab, hac, had]),
      Finset.card_insert_of_notMem (by simp [hbc, hbd]),
      Finset.card_insert_of_notMem (by simp [hcd]),
      Finset.card_singleton]

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Subgroup in
theorem l42S4grid {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G) (hn : D.n = 2) :
    Nat.card ↥(D.S : Subgroup G) = 4 ∧
    (∀ σ : ↥(D.S : Subgroup G), σ = 1 ∨ (σ : G) = D.t ∨ (σ : G) = D.t1 ∨ (σ : G) = D.t2) ∧
    D.t * D.t1 = D.t2 ∧ D.t * D.t2 = D.t1 ∧ D.t1 ≠ D.t2 := by
  classical
  haveI : Fintype ↥(D.S : Subgroup G) := Fintype.ofFinite _
  -- `|S| = |DihedralGroup n| = 2n = 4`.
  obtain ⟨e⟩ := D.dih
  have hS : Nat.card ↥(D.S : Subgroup G) = 2 * D.n := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hcardS : Nat.card ↥(D.S : Subgroup G) = 4 := by rw [hS, hn]
  -- The three involutions `t`, `t₁`, `t₂` are distinct.
  have ht_ne_one : D.t ≠ 1 := by
    intro h
    have hh := D.t_order
    rw [h, orderOf_one] at hh
    omega
  have ht1_ne_one : D.t1 ≠ 1 := by
    intro h
    have hh := D.t1_order
    rw [h, orderOf_one] at hh
    omega
  have ht2_ne_one : D.t2 ≠ 1 := by
    intro h
    have hh := D.t2_order
    rw [h, orderOf_one] at hh
    omega
  have ht_ne_t1 : D.t ≠ D.t1 := by
    intro h; exact D.t1_nmem (h ▸ D.t_mem)
  have ht_ne_t2 : D.t ≠ D.t2 := by
    intro h; exact D.t2_nmem (h ▸ D.t_mem)
  have hsq_t : D.t * D.t = 1 := by
    have h := pow_orderOf_eq_one D.t
    rw [D.t_order, pow_two] at h
    exact h
  have hsq_t1 : D.t1 * D.t1 = 1 := by
    have h := pow_orderOf_eq_one D.t1
    rw [D.t1_order, pow_two] at h
    exact h
  -- `t₁ ≠ t₂`: otherwise `S₀ = zpowers (t₁ * t₂) = ⊥` would force `t = 1`.
  have ht1_ne_t2 : D.t1 ≠ D.t2 := by
    intro h
    have hprod : D.t1 * D.t2 = 1 := by rw [← h]; exact hsq_t1
    have hbot : D.S0 = ⊥ := by rw [D.gen, hprod, Subgroup.zpowers_one_eq_bot]
    have : D.t = 1 := by
      have hm : D.t ∈ D.S0 := D.t_mem
      rw [hbot] at hm
      exact Subgroup.mem_bot.mp hm
    exact ht_ne_one this
  -- The same distinctness, transported to the subtype `S`.
  have hTt_ne_one : (⟨D.t, D.S0_le D.t_mem⟩ : ↥(D.S : Subgroup G)) ≠ 1 := by
    intro h; exact ht_ne_one (by simpa using congrArg Subtype.val h)
  have hT1_ne_one : (⟨D.t1, D.t1_mem⟩ : ↥(D.S : Subgroup G)) ≠ 1 := by
    intro h; exact ht1_ne_one (by simpa using congrArg Subtype.val h)
  have hT2_ne_one : (⟨D.t2, D.t2_mem⟩ : ↥(D.S : Subgroup G)) ≠ 1 := by
    intro h; exact ht2_ne_one (by simpa using congrArg Subtype.val h)
  have hTt_ne_T1 : (⟨D.t, D.S0_le D.t_mem⟩ : ↥(D.S : Subgroup G)) ≠ ⟨D.t1, D.t1_mem⟩ := by
    intro h; exact ht_ne_t1 (by simpa using congrArg Subtype.val h)
  have hTt_ne_T2 : (⟨D.t, D.S0_le D.t_mem⟩ : ↥(D.S : Subgroup G)) ≠ ⟨D.t2, D.t2_mem⟩ := by
    intro h; exact ht_ne_t2 (by simpa using congrArg Subtype.val h)
  have hT1_ne_T2 : (⟨D.t1, D.t1_mem⟩ : ↥(D.S : Subgroup G)) ≠ ⟨D.t2, D.t2_mem⟩ := by
    intro h; exact ht1_ne_t2 (by simpa using congrArg Subtype.val h)
  -- `{1, t, t₁, t₂} ⊆ S` has four elements, so it is all of `S` (`|S| = 4`).
  have hcardF : ({1, ⟨D.t, D.S0_le D.t_mem⟩, ⟨D.t1, D.t1_mem⟩, ⟨D.t2, D.t2_mem⟩} :
      Finset ↥(D.S : Subgroup G)).card = 4 :=
    card_four (α := ↥(D.S : Subgroup G)) 1 ⟨D.t, D.S0_le D.t_mem⟩ ⟨D.t1, D.t1_mem⟩
      ⟨D.t2, D.t2_mem⟩ (Ne.symm hTt_ne_one) (Ne.symm hT1_ne_one) (Ne.symm hT2_ne_one)
      hTt_ne_T1 hTt_ne_T2 hT1_ne_T2
  have hF : ({1, ⟨D.t, D.S0_le D.t_mem⟩, ⟨D.t1, D.t1_mem⟩, ⟨D.t2, D.t2_mem⟩} :
      Finset ↥(D.S : Subgroup G)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hcardF, ← Nat.card_eq_fintype_card, hcardS]
  -- The grid: every element of `S` is one of `1, t, t₁, t₂`.
  have hmem : ∀ σ : ↥(D.S : Subgroup G),
      σ = 1 ∨ (σ : G) = D.t ∨ (σ : G) = D.t1 ∨ (σ : G) = D.t2 := by
    intro σ
    have hσ : σ ∈ ({1, ⟨D.t, D.S0_le D.t_mem⟩, ⟨D.t1, D.t1_mem⟩, ⟨D.t2, D.t2_mem⟩} :
        Finset ↥(D.S : Subgroup G)) := by
      rw [hF]; exact Finset.mem_univ σ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hσ
    rcases hσ with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (by rw [h]))
    · exact Or.inr (Or.inr (Or.inl (by rw [h])))
    · exact Or.inr (Or.inr (Or.inr (by rw [h])))
  -- Products: in the Klein four group the product of two distinct involutions is the third.
  have hmul1 : D.t * D.t1 = D.t2 := by
    have hσ := hmem ⟨D.t * D.t1, D.S.mul_mem (D.S0_le D.t_mem) D.t1_mem⟩
    rcases hσ with h | h | h | h
    · have h1 : D.t * D.t1 = 1 := by have := congrArg Subtype.val h; simpa using this
      exact absurd (mul_left_cancel (h1.trans hsq_t.symm)) (Ne.symm ht_ne_t1)
    · have hc : D.t * D.t1 = D.t := h
      have heq : D.t * D.t1 = D.t * 1 := by rw [hc, mul_one]
      exact absurd (mul_left_cancel heq) ht1_ne_one
    · have hc : D.t * D.t1 = D.t1 := h
      have heq : D.t * D.t1 = 1 * D.t1 := by rw [hc, one_mul]
      exact absurd (mul_right_cancel heq) ht_ne_one
    · exact h
  have hmul2 : D.t * D.t2 = D.t1 := by
    have hσ := hmem ⟨D.t * D.t2, D.S.mul_mem (D.S0_le D.t_mem) D.t2_mem⟩
    rcases hσ with h | h | h | h
    · have h1 : D.t * D.t2 = 1 := by have := congrArg Subtype.val h; simpa using this
      exact absurd (mul_left_cancel (h1.trans hsq_t.symm)) (Ne.symm ht_ne_t2)
    · have hc : D.t * D.t2 = D.t := h
      have heq : D.t * D.t2 = D.t * 1 := by rw [hc, mul_one]
      exact absurd (mul_left_cancel heq) ht2_ne_one
    · exact h
    · have hc : D.t * D.t2 = D.t2 := h
      have heq : D.t * D.t2 = 1 * D.t2 := by rw [hc, one_mul]
      exact absurd (mul_right_cancel heq) ht_ne_one
  exact ⟨hcardS, hmem, hmul1, hmul2, ht1_ne_t2⟩

end Work.BG
