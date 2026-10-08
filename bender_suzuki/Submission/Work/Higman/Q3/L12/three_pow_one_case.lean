import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false

namespace Work.Higman.Q3.L12

/-! ## Elementary arithmetic helpers for the `A - B = 2 ^ n - 1` case

The argument is: the right-hand side is `≥ 2 ^ n + 2`, which forces two of `a, b, c` to equal
`n - 1`; then the equality reduces to `2 ^ d + 2 ^ e = 2 ^ z + 1` for the remaining exponent `z`,
which forces `{d, e} = {0, z}`.
-/

/-- `2 ^ u + 2 ^ u = 2 ^ (u + 1)`. -/
private theorem tpoc_two_pow_add_self (u : ℕ) : 2 ^ u + 2 ^ u = 2 ^ (u + 1) := by
  rw [pow_succ]; ring

/-- `2 ^ k` is even for `k ≥ 1`. -/
private theorem tpoc_even_two_pow {k : ℕ} (hk : 1 ≤ k) : Even (2 ^ k) :=
  Nat.even_pow.mpr ⟨even_two, by omega⟩

/-- `2 ^ k + 1` is odd, hence odd is not divisible by `2`, for `k ≥ 1`. -/
private theorem tpoc_not_two_dvd_two_pow_add_one {k : ℕ} (hk : 1 ≤ k) :
    ¬ 2 ∣ 2 ^ k + 1 := by
  rw [← even_iff_two_dvd]
  exact Nat.not_even_iff_odd.mpr ((tpoc_even_two_pow hk).add_odd odd_one)

/-- If `2 ^ d + 2 ^ e = 2 ^ c + 1` then one of `d, e` is `0` and the other equals `c`. -/
private theorem tpoc_pow_two_sum_eq_one {c d e : ℕ} (h : 2 ^ d + 2 ^ e = 2 ^ c + 1) :
    (d = 0 ∧ e = c) ∨ (e = 0 ∧ d = c) := by
  rcases Nat.eq_zero_or_pos c with hc | hc
  · -- `c = 0`: the right-hand side is `2`, and both summands are at least `1`.
    subst hc
    simp only [pow_zero] at h
    have hdge : 1 ≤ 2 ^ d := Nat.one_le_two_pow
    have hege : 1 ≤ 2 ^ e := Nat.one_le_two_pow
    have hd1 : 2 ^ d = 1 := by omega
    have he1 : 2 ^ e = 1 := by omega
    have hd : d = 0 := by
      have hdd : (2 : ℕ) ^ d = (2 : ℕ) ^ 0 := by rw [hd1, pow_zero]
      exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) hdd
    have he : e = 0 := by
      have hee : (2 : ℕ) ^ e = (2 : ℕ) ^ 0 := by rw [he1, pow_zero]
      exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) hee
    exact Or.inl ⟨hd, he⟩
  · -- `c ≥ 1`: the right-hand side is odd, so exactly one of `d, e` is `0`.
    have hde : d = 0 ∨ e = 0 := by
      by_contra hcon
      simp only [not_or] at hcon
      obtain ⟨hd, he⟩ := hcon
      have hdd : 2 ∣ 2 ^ d := dvd_pow_self 2 hd
      have hed : 2 ∣ 2 ^ e := dvd_pow_self 2 he
      have hsum : 2 ∣ 2 ^ d + 2 ^ e := Nat.dvd_add hdd hed
      rw [h] at hsum
      exact tpoc_not_two_dvd_two_pow_add_one hc hsum
    rcases hde with hd | he
    · refine Or.inl ⟨hd, ?_⟩
      have h0 : 2 ^ d = 1 := by rw [hd, pow_zero]
      have : 2 ^ e = 2 ^ c := by omega
      exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) this
    · refine Or.inr ⟨he, ?_⟩
      have h0 : 2 ^ e = 1 := by rw [he, pow_zero]
      have : 2 ^ d = 2 ^ c := by omega
      exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) this

/-- If at most one of `a, b, c` equals `n - 1` (encoded by the three pairwise clauses) and all are
`< n`, then `2 ^ a + 2 ^ b + 2 ^ c ≤ 2 ^ n`.  The worst case is two exponents as large as possible
below `n - 1`, giving `2 ^ (n-1) + 2 ^ (n-2) + 2 ^ (n-2) = 2 ^ n`. -/
private theorem tpoc_at_most_one_bound {n a b c : ℕ} (hn : 0 < n) (ha : a < n) (hb : b < n)
    (hc : c < n) (h1 : ¬(a = n - 1 ∧ b = n - 1)) (h2 : ¬(a = n - 1 ∧ c = n - 1))
    (h3 : ¬(b = n - 1 ∧ c = n - 1)) :
    2 ^ a + 2 ^ b + 2 ^ c ≤ 2 ^ n := by
  have key : ∀ x : ℕ, x < n → 2 ^ (x + 1) ≤ 2 ^ n := by
    intro x hx
    apply Nat.pow_le_pow_right (by norm_num); omega
  have key' : ∀ x : ℕ, x < n → x ≠ n - 1 → 2 ^ (x + 1) ≤ 2 ^ (n - 1) := by
    intro x hx hne
    apply Nat.pow_le_pow_right (by norm_num)
    have : x < n - 1 := by omega
    omega
  have hsum : 2 ^ (a + 1) + 2 ^ (b + 1) + 2 ^ (c + 1) ≤ 2 ^ (n + 1) := by
    have hp : 2 ^ (n - 1) + 2 ^ (n - 1) = 2 ^ n := by
      rw [← two_mul, ← pow_succ']; congr 1; omega
    have htot : 2 ^ n + 2 ^ (n - 1) + 2 ^ (n - 1) = 2 ^ (n + 1) := by
      have hsq : 2 ^ n + 2 ^ n = 2 ^ (n + 1) := by rw [← two_mul, Nat.pow_succ, mul_comm]
      linarith
    rcases eq_or_ne a (n - 1) with ha' | ha'
    · have hbn : b ≠ n - 1 := by rintro rfl; exact h1 ⟨ha', rfl⟩
      have hcn : c ≠ n - 1 := by rintro rfl; exact h2 ⟨ha', rfl⟩
      have e1 : 2 ^ (a + 1) = 2 ^ n := by rw [ha']; omega
      have e2 : 2 ^ (b + 1) ≤ 2 ^ (n - 1) := key' b hb hbn
      have e3 : 2 ^ (c + 1) ≤ 2 ^ (n - 1) := key' c hc hcn
      rw [e1]; linarith
    · rcases eq_or_ne b (n - 1) with hb' | hb'
      · have hcn : c ≠ n - 1 := by rintro rfl; exact h3 ⟨hb', rfl⟩
        have e1 : 2 ^ (b + 1) = 2 ^ n := by rw [hb']; omega
        have e2 : 2 ^ (a + 1) ≤ 2 ^ (n - 1) := key' a ha ha'
        have e3 : 2 ^ (c + 1) ≤ 2 ^ (n - 1) := key' c hc hcn
        rw [e1]; linarith
      · have e1 : 2 ^ (a + 1) ≤ 2 ^ (n - 1) := key' a ha ha'
        have e2 : 2 ^ (b + 1) ≤ 2 ^ (n - 1) := key' b hb hb'
        have e3 : 2 ^ (c + 1) ≤ 2 ^ n := key c hc
        linarith
  have hmul : 2 * (2 ^ a + 2 ^ b + 2 ^ c) ≤ 2 * 2 ^ n := by
    have heq : 2 * (2 ^ a + 2 ^ b + 2 ^ c) = 2 ^ (a + 1) + 2 ^ (b + 1) + 2 ^ (c + 1) := by
      rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ]; ring
    rw [heq]
    have : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, mul_comm]
    rw [← this]; exact hsum
  exact Nat.le_of_mul_le_mul_left hmul (by norm_num)

/-- Case `a = b = n - 1`: then `2 ^ a + 2 ^ b = 2 ^ n`, leaving `2 ^ c + 1 = 2 ^ d + 2 ^ e`, which
forces `{d, e} = {0, c}`. -/
private theorem tpoc_case_ab {n a b c d e : ℕ} (hn : 0 < n)
    (ha : a = n - 1) (hb : b = n - 1)
    (h : 2 ^ a + 2 ^ b + 2 ^ c + 1 = 2 ^ d + 2 ^ e + 2 ^ n) :
    (a = b ∧ d = (a + 1) % n ∧ c = e) ∨ (a = b ∧ e = (a + 1) % n ∧ c = d) := by
  have hpow : 2 ^ (n - 1) + 2 ^ (n - 1) = 2 ^ n := by
    rw [tpoc_two_pow_add_self]; congr 1; omega
  have hmod : (n - 1 + 1) % n = 0 := by
    have : n - 1 + 1 = n := by omega
    rw [this, Nat.mod_self]
  subst ha
  subst hb
  have hkey : 2 ^ c + 1 = 2 ^ d + 2 ^ e := by omega
  rcases tpoc_pow_two_sum_eq_one hkey.symm with ⟨hd0, hec⟩ | ⟨he0, hdc⟩
  · left
    exact ⟨rfl, by rw [hd0, hmod], hec.symm⟩
  · right
    exact ⟨rfl, by rw [he0, hmod], hdc.symm⟩

/-- Case `a = c = n - 1` of `three_pow_one_case`. -/
private theorem tpoc_case_ac {n a b c d e : ℕ} (hn : 0 < n)
    (ha : a = n - 1) (hc : c = n - 1)
    (h : 2 ^ a + 2 ^ b + 2 ^ c + 1 = 2 ^ d + 2 ^ e + 2 ^ n) :
    (a = c ∧ d = (a + 1) % n ∧ b = e) ∨ (a = c ∧ e = (a + 1) % n ∧ b = d) := by
  have hpow : 2 ^ (n - 1) + 2 ^ (n - 1) = 2 ^ n := by
    rw [tpoc_two_pow_add_self]; congr 1; omega
  have hmod : (n - 1 + 1) % n = 0 := by
    have : n - 1 + 1 = n := by omega
    rw [this, Nat.mod_self]
  subst ha
  subst hc
  have hkey : 2 ^ b + 1 = 2 ^ d + 2 ^ e := by omega
  rcases tpoc_pow_two_sum_eq_one hkey.symm with ⟨hd0, heb⟩ | ⟨he0, hdb⟩
  · left
    exact ⟨rfl, by rw [hd0, hmod], heb.symm⟩
  · right
    exact ⟨rfl, by rw [he0, hmod], hdb.symm⟩

/-- Case `b = c = n - 1` of `three_pow_one_case`. -/
private theorem tpoc_case_bc {n a b c d e : ℕ} (hn : 0 < n)
    (hb : b = n - 1) (hc : c = n - 1)
    (h : 2 ^ a + 2 ^ b + 2 ^ c + 1 = 2 ^ d + 2 ^ e + 2 ^ n) :
    (b = c ∧ d = (b + 1) % n ∧ a = e) ∨ (b = c ∧ e = (b + 1) % n ∧ a = d) := by
  have hpow : 2 ^ (n - 1) + 2 ^ (n - 1) = 2 ^ n := by
    rw [tpoc_two_pow_add_self]; congr 1; omega
  have hmod : (n - 1 + 1) % n = 0 := by
    have : n - 1 + 1 = n := by omega
    rw [this, Nat.mod_self]
  subst hb
  subst hc
  have hkey : 2 ^ a + 1 = 2 ^ d + 2 ^ e := by omega
  rcases tpoc_pow_two_sum_eq_one hkey.symm with ⟨hd0, hea⟩ | ⟨he0, hda⟩
  · left
    exact ⟨rfl, by rw [hd0, hmod], hea.symm⟩
  · right
    exact ⟨rfl, by rw [he0, hmod], hda.symm⟩

/-- Case `A - B = 2 ^ n - 1` of Higman's congruence (p. 92), i.e. of
`Work.Higman.Q3.L12.three_pow_congruence`: if `2 ^ a + 2 ^ b + 2 ^ c + 1 = 2 ^ d + 2 ^ e + 2 ^ n`
(all exponents `< n`, `n > 0`), then two of `a, b, c` coincide — necessarily both equal `n - 1`,
so that `(that value + 1) mod n = 0` — and `{d, e}` is `{0, the third exponent}`.

Proof idea: bounding forces `max (a,b,c) = n - 1` and forces two of `a, b, c` to be `n - 1`
(if exactly one of them were `n - 1`, the left side would be at most
`2 ^ (n-1) + 2 ^ (n-2) + 2 ^ (n-2) + 1 = 2 ^ n + 1`, while the right side is `≥ 2 ^ n + 2`);
then comparing binary expansions gives `2 ^ d + 2 ^ e = 2 ^ c + 1`, i.e. `{d, e} = {0, c}`.
Exhaustively verified for `n ≤ 16`. -/
theorem three_pow_one_case {n a b c d e : ℕ} (hn : 0 < n)
    (ha : a < n) (hb : b < n) (hc : c < n) (hd : d < n) (he : e < n)
    (h : 2 ^ a + 2 ^ b + 2 ^ c + 1 = 2 ^ d + 2 ^ e + 2 ^ n) :
    (a = b ∧ d = (a + 1) % n ∧ c = e) ∨ (a = b ∧ e = (a + 1) % n ∧ c = d) ∨
    (a = c ∧ d = (a + 1) % n ∧ b = e) ∨ (a = c ∧ e = (a + 1) % n ∧ b = d) ∨
    (b = c ∧ d = (b + 1) % n ∧ a = e) ∨ (b = c ∧ e = (b + 1) % n ∧ a = d) := by
  -- The right-hand side is `≥ 2 ^ n + 2`, while the left-hand side is `= 2 ^ a + 2 ^ b + 2 ^ c + 1`.
  have hN1 : 2 ^ n + 2 ≤ 2 ^ a + 2 ^ b + 2 ^ c + 1 := by
    have h1 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
    have h2 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
    omega
  -- Hence at least two of `a, b, c` equal `n - 1`.
  have h_two : (a = n - 1 ∧ b = n - 1) ∨ (a = n - 1 ∧ c = n - 1) ∨
      (b = n - 1 ∧ c = n - 1) := by
    by_contra hcon
    have g1 : ¬(a = n - 1 ∧ b = n - 1) := fun hh => hcon (Or.inl hh)
    have g2 : ¬(a = n - 1 ∧ c = n - 1) := fun hh => hcon (Or.inr (Or.inl hh))
    have g3 : ¬(b = n - 1 ∧ c = n - 1) := fun hh => hcon (Or.inr (Or.inr hh))
    have hbound := tpoc_at_most_one_bound hn ha hb hc g1 g2 g3
    omega
  rcases h_two with ⟨ha', hb'⟩ | ⟨ha', hc'⟩ | ⟨hb', hc'⟩
  · rcases tpoc_case_ab hn ha' hb' h with hh | hh
    · exact Or.inl hh
    · exact Or.inr (Or.inl hh)
  · rcases tpoc_case_ac hn ha' hc' h with hh | hh
    · exact Or.inr (Or.inr (Or.inl hh))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hh)))
  · rcases tpoc_case_bc hn hb' hc' h with hh | hh
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))

end Work.Higman.Q3.L12
