import Mathlib
import Submission.Work.Higman.QuadAux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman

/-- For `k < l < n` the binomial exponent `2 ^ k + 2 ^ l` is strictly below `2 ^ n`. -/
private lemma two_pow_add_two_pow_lt {k l n : ℕ} (hkl : k < l) (hln : l < n) :
    2 ^ k + 2 ^ l < 2 ^ n := by
  have hk : 2 ^ k ≤ 2 ^ (l - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ (l - 1) < 2 ^ l := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have h3 : 2 ^ l + 2 ^ l = 2 ^ (l + 1) := by rw [pow_succ]; ring
  have h4 : 2 ^ (l + 1) ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc 2 ^ k + 2 ^ l ≤ 2 ^ (l - 1) + 2 ^ l := by omega
    _ < 2 ^ l + 2 ^ l := by omega
    _ = 2 ^ (l + 1) := h3
    _ ≤ 2 ^ n := h4

/-- Two positive natural numbers that are `≤ m` and congruent modulo `m` are equal. -/
private lemma eq_of_modEq_of_pos_le {m a b : ℕ} (h : a ≡ b [MOD m]) (ha0 : 0 < a) (hb0 : 0 < b)
    (ha : a ≤ m) (hb : b ≤ m) : a = b := by
  have h' : a % m = b % m := h
  rcases lt_or_eq_of_le ha with ha' | ha'
  · rw [Nat.mod_eq_of_lt ha'] at h'
    rcases lt_or_eq_of_le hb with hb' | hb'
    · rw [Nat.mod_eq_of_lt hb'] at h'; exact h'
    · rw [hb', Nat.mod_self] at h'; omega
  · rw [ha', Nat.mod_self] at h'
    rcases lt_or_eq_of_le hb with hb' | hb'
    · rw [Nat.mod_eq_of_lt hb'] at h'; omega
    · rw [ha', hb']

theorem monomial_extract {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {n : ℕ} (nu lam : F) (hnu : orderOf nu = 2 ^ n - 1) (d : ℕ → ℕ → F)
    (hd : ∀ k l : ℕ, k < n → l < n → d k l * (nu ^ (2 ^ k + 2 ^ l) - lam) = 0)
    (Q : F → F)
    (hQ : ∀ x : F, Q x = ∑ k ∈ Finset.range n,
      ∑ l ∈ (Finset.range n).filter (fun l => k < l), d k l * x ^ (2 ^ k + 2 ^ l))
    (hQnz : ∃ x : F, Q x ≠ 0) :
    ∃ i j : ℕ, i < j ∧ j < n ∧ nu ^ (2 ^ i + 2 ^ j) = lam ∧
      ∃ c : F, c ≠ 0 ∧ ∀ x : F, Q x = c * x ^ (2 ^ i + 2 ^ j) := by
  -- There is at least one pair `(k,l)` with `k < l < n` and a nonzero coefficient.
  have hex : ∃ k l, k < l ∧ l < n ∧ d k l ≠ 0 := by
    obtain ⟨x0, hx0⟩ := hQnz
    by_contra h
    have hforall : ∀ k l, k < l → l < n → d k l = 0 := by
      intro k l hkl hln
      by_contra hd0
      exact h ⟨k, l, hkl, hln, hd0⟩
    apply hx0
    rw [hQ x0]
    apply Finset.sum_eq_zero
    intro k hk
    apply Finset.sum_eq_zero
    intro l hl
    simp only [Finset.mem_filter, Finset.mem_range] at hl
    rw [hforall k l hl.2 hl.1, zero_mul]
  obtain ⟨i, j, hij, hjn, hdij⟩ := hex
  have hin : i < n := lt_trans hij hjn
  have hn2 : 2 ≤ n := by omega
  have hfin : IsOfFinOrder nu := by
    rw [isOfFinOrder_iff_pow_eq_one]
    refine ⟨2 ^ n - 1, ?_, ?_⟩
    · have hge : (4 : ℕ) ≤ 2 ^ n := by
        have := Nat.pow_le_pow_right (show 0 < (2:ℕ) by norm_num) hn2
        simpa using this
      omega
    · rw [← hnu]; exact pow_orderOf_eq_one nu
  -- The chosen exponent satisfies `nu ^ (2 ^ i + 2 ^ j) = lam`.
  have hlam : nu ^ (2 ^ i + 2 ^ j) = lam := by
    have h0 := hd i j hin hjn
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd h1 hdij
    · rwa [sub_eq_zero] at h1
  -- Any pair with nonzero coefficient has the same exponent.
  have h_exp : ∀ k l, k < l → l < n → d k l ≠ 0 → 2 ^ k + 2 ^ l = 2 ^ i + 2 ^ j := by
    intro k l hkl hln hdkl
    have hkn : k < n := lt_trans hkl hln
    have hnak : nu ^ (2 ^ k + 2 ^ l) = lam := by
      have h0 := hd k l hkn hln
      rcases mul_eq_zero.mp h0 with h1 | h1
      · exact absurd h1 hdkl
      · rwa [sub_eq_zero] at h1
    have hpoweq : nu ^ (2 ^ k + 2 ^ l) = nu ^ (2 ^ i + 2 ^ j) := by rw [hnak, hlam]
    have hmod : (2 ^ k + 2 ^ l) ≡ (2 ^ i + 2 ^ j) [MOD 2 ^ n - 1] := by
      have h2 := (IsOfFinOrder.pow_eq_pow_iff_modEq hfin).mp hpoweq
      rwa [hnu] at h2
    exact eq_of_modEq_of_pos_le hmod (by positivity) (by positivity)
      (by have := two_pow_add_two_pow_lt hkl hln; omega)
      (by have := two_pow_add_two_pow_lt hij hjn; omega)
  refine ⟨i, j, hij, hjn, hlam, ?_⟩
  -- `Q` is a single monomial.
  have hkey : ∀ x : F, Q x =
      (∑ k ∈ Finset.range n, ∑ l ∈ (Finset.range n).filter (fun l => k < l), d k l)
        * x ^ (2 ^ i + 2 ^ j) := by
    intro x
    rw [hQ x, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l hl
    simp only [Finset.mem_filter, Finset.mem_range] at hl
    by_cases hd0 : d k l = 0
    · rw [hd0]; simp
    · rw [h_exp k l hl.2 hl.1 hd0]
  refine ⟨(∑ k ∈ Finset.range n, ∑ l ∈ (Finset.range n).filter (fun l => k < l), d k l),
    ?_, hkey⟩
  intro hc0
  obtain ⟨x0, hx0⟩ := hQnz
  apply hx0
  rw [hkey x0, hc0, zero_mul]

end Work.Higman
