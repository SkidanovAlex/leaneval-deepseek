import Mathlib
import Submission.Work.Higman.Q3.L12.three_pow_helpers
import Submission.Work.Higman.Q3.L12.pair_unique_le

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false

namespace Work.Higman.Q3.L12

/-- Uniqueness of the representation of a natural number as an unordered sum of two powers of
two: if `2 ^ u + 2 ^ v = 2 ^ d + 2 ^ e` then `{u, v} = {d, e}` as multisets. -/
theorem pair_unique {u v d e : ℕ} (h : 2 ^ u + 2 ^ v = 2 ^ d + 2 ^ e) :
    (u = d ∧ v = e) ∨ (u = e ∧ v = d) := by
  rcases le_total u v with huv | hvu
  · rcases le_total d e with hde | hed
    · exact Or.inl (pair_unique_le huv hde h)
    · exact Or.inr (pair_unique_le huv hed
        (h.trans (by ring : 2 ^ d + 2 ^ e = 2 ^ e + 2 ^ d)))
  · rcases le_total d e with hde | hed
    · obtain ⟨h1, h2⟩ := pair_unique_le hvu hde
        ((by ring : 2 ^ v + 2 ^ u = 2 ^ u + 2 ^ v).trans h)
      exact Or.inr ⟨h2, h1⟩
    · obtain ⟨h1, h2⟩ := pair_unique_le hvu hed
        ((by ring : 2 ^ v + 2 ^ u = 2 ^ u + 2 ^ v).trans
          (h.trans (by ring : 2 ^ d + 2 ^ e = 2 ^ e + 2 ^ d)))
      exact Or.inl ⟨h2, h1⟩

/-- `2 ^ x + 2 ^ y` is never a power of two when `x ≠ y`. -/
private theorem two_pow_add_ne_two_pow {x y k : ℕ} (hxy : x ≠ y) : 2 ^ x + 2 ^ y ≠ 2 ^ k := by
  intro hk
  rcases k with _ | k'
  · simp only [pow_zero] at hk
    have hx : 1 ≤ 2 ^ x := Nat.one_le_two_pow
    have hy : 1 ≤ 2 ^ y := Nat.one_le_two_pow
    omega
  · have h2 : 2 ^ (k' + 1) = 2 ^ k' + 2 ^ k' := by rw [pow_succ]; ring
    rw [h2] at hk
    rcases pair_unique hk with ⟨h1, h2'⟩ | ⟨h1, h2'⟩
    · exact hxy (h1.trans h2'.symm)
    · exact hxy (h1.trans h2'.symm)

/-- If `a ≠ b` and both `a` and `b` are `< c`, then `2 ^ a + 2 ^ b < 2 ^ c`. -/
private theorem two_pow_add_lt {a b c : ℕ} (hab : a ≠ b) (hac : a < c) (hbc : b < c) :
    2 ^ a + 2 ^ b < 2 ^ c := by
  rcases lt_or_gt_of_ne hab with hab' | hba'
  · have h1 : 2 ^ a < 2 ^ b := (Nat.pow_lt_pow_iff_right (by norm_num : (1 : ℕ) < 2)).mpr hab'
    have h2 : 2 ^ b + 2 ^ b = 2 ^ (b + 1) := two_pow_add_self b
    have h3 : 2 ^ (b + 1) ≤ 2 ^ c :=
      Nat.pow_le_pow_right (by norm_num : (0 : ℕ) < 2) (by omega)
    calc 2 ^ a + 2 ^ b < 2 ^ b + 2 ^ b := by omega
      _ = 2 ^ (b + 1) := h2
      _ ≤ 2 ^ c := h3
  · have h1 : 2 ^ b < 2 ^ a := (Nat.pow_lt_pow_iff_right (by norm_num : (1 : ℕ) < 2)).mpr hba'
    have h2 : 2 ^ a + 2 ^ a = 2 ^ (a + 1) := two_pow_add_self a
    have h3 : 2 ^ (a + 1) ≤ 2 ^ c :=
      Nat.pow_le_pow_right (by norm_num : (0 : ℕ) < 2) (by omega)
    calc 2 ^ a + 2 ^ b < 2 ^ a + 2 ^ a := by omega
      _ = 2 ^ (a + 1) := h2
      _ ≤ 2 ^ c := h3

/-- Core step: if `a ≠ b` and both are below `c`, then `2 ^ a + 2 ^ b + 2 ^ c` is not a sum
of two powers of two.  The value lies strictly between the consecutive powers `2 ^ c` and
`2 ^ (c + 1)`, so its largest two-power summand must be `2 ^ c`, leaving `2 ^ a + 2 ^ b` — not a
power of two — as the other summand. -/
private theorem three_pow_core {a b c d e : ℕ} (hab : a ≠ b) (hac : a < c) (hbc : b < c)
    (h : 2 ^ a + 2 ^ b + 2 ^ c = 2 ^ d + 2 ^ e) : False := by
  have hlt : 2 ^ a + 2 ^ b < 2 ^ c := two_pow_add_lt hab hac hbc
  have hgt : 2 ^ c < 2 ^ a + 2 ^ b + 2 ^ c := by
    have hpos : 0 < 2 ^ a + 2 ^ b := by positivity
    omega
  have hlt2 : 2 ^ a + 2 ^ b + 2 ^ c < 2 ^ (c + 1) := by
    have h2 : 2 ^ c + 2 ^ c = 2 ^ (c + 1) := two_pow_add_self c
    omega
  rcases le_total d e with hde | hed
  · have hec : e = c := by
      have h1 : e ≤ c := by
        have heN : 2 ^ e ≤ 2 ^ a + 2 ^ b + 2 ^ c := by rw [h]; exact Nat.le_add_left _ _
        have := (Nat.pow_lt_pow_iff_right (by norm_num : (1 : ℕ) < 2)).mp (lt_of_le_of_lt heN hlt2)
        omega
      have h2 : c ≤ e := by
        have hmax : 2 ^ d + 2 ^ e ≤ 2 ^ (e + 1) := by
          have hd : 2 ^ d ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num : (0 : ℕ) < 2) hde
          have h2' : 2 ^ e + 2 ^ e = 2 ^ (e + 1) := two_pow_add_self e
          omega
        have hcN : 2 ^ c < 2 ^ d + 2 ^ e := by rw [← h]; exact hgt
        have :=
          (Nat.pow_lt_pow_iff_right (by norm_num : (1 : ℕ) < 2)).mp (lt_of_lt_of_le hcN hmax)
        omega
      omega
    have hdecomp : 2 ^ d = 2 ^ a + 2 ^ b := by
      have hh : 2 ^ d + 2 ^ e = 2 ^ a + 2 ^ b + 2 ^ c := h.symm
      rw [hec] at hh
      omega
    exact two_pow_add_ne_two_pow hab hdecomp.symm
  · have hdc : d = c := by
      have h1 : d ≤ c := by
        have hdN : 2 ^ d ≤ 2 ^ a + 2 ^ b + 2 ^ c := by rw [h]; exact Nat.le_add_right _ _
        have := (Nat.pow_lt_pow_iff_right (by norm_num : (1 : ℕ) < 2)).mp (lt_of_le_of_lt hdN hlt2)
        omega
      have h2 : c ≤ d := by
        have hmax : 2 ^ d + 2 ^ e ≤ 2 ^ (d + 1) := by
          have he : 2 ^ e ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num : (0 : ℕ) < 2) hed
          have h2' : 2 ^ d + 2 ^ d = 2 ^ (d + 1) := two_pow_add_self d
          omega
        have hcN : 2 ^ c < 2 ^ d + 2 ^ e := by rw [← h]; exact hgt
        have :=
          (Nat.pow_lt_pow_iff_right (by norm_num : (1 : ℕ) < 2)).mp (lt_of_lt_of_le hcN hmax)
        omega
      omega
    have hdecomp : 2 ^ e = 2 ^ a + 2 ^ b := by
      have hh : 2 ^ d + 2 ^ e = 2 ^ a + 2 ^ b + 2 ^ c := h.symm
      rw [hdc] at hh
      omega
    exact two_pow_add_ne_two_pow hab hdecomp.symm

/-- If `2 ^ a + 2 ^ b + 2 ^ c = 2 ^ d + 2 ^ e` then two of `a, b, c` coincide: the right-hand
side has at most two binary ones, while three pairwise distinct exponents produce three. -/
private theorem two_of_three_pow_eq {a b c d e : ℕ}
    (h : 2 ^ a + 2 ^ b + 2 ^ c = 2 ^ d + 2 ^ e) : a = b ∨ a = c ∨ b = c := by
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨hab, hac, hbc⟩ := hcon
  have key : ∀ x y z : ℕ, x < y → y < z → 2 ^ x + 2 ^ y + 2 ^ z = 2 ^ d + 2 ^ e → False :=
    fun x y z hxy hyz h' => three_pow_core (ne_of_lt hxy) (lt_trans hxy hyz) hyz h'
  rcases lt_trichotomy a b with hab' | hab' | hab'
  · rcases lt_trichotomy b c with hbc' | hbc' | hbc'
    · exact key a b c hab' hbc' h
    · exact hbc hbc'
    · rcases lt_trichotomy a c with hac' | hac' | hac'
      · exact key a c b hac' hbc'
          (by rw [show 2 ^ a + 2 ^ c + 2 ^ b = 2 ^ a + 2 ^ b + 2 ^ c by ring]; exact h)
      · exact hac hac'
      · exact key c a b hac' hab'
          (by rw [show 2 ^ c + 2 ^ a + 2 ^ b = 2 ^ a + 2 ^ b + 2 ^ c by ring]; exact h)
  · exact hab hab'
  · rcases lt_trichotomy b c with hbc' | hbc' | hbc'
    · rcases lt_trichotomy a c with hac' | hac' | hac'
      · exact key b a c hab' hac'
          (by rw [show 2 ^ b + 2 ^ a + 2 ^ c = 2 ^ a + 2 ^ b + 2 ^ c by ring]; exact h)
      · exact hac hac'
      · exact key b c a hbc' hac'
          (by rw [show 2 ^ b + 2 ^ c + 2 ^ a = 2 ^ a + 2 ^ b + 2 ^ c by ring]; exact h)
    · exact hbc hbc'
    · exact key c b a hbc' hab'
        (by rw [show 2 ^ c + 2 ^ b + 2 ^ a = 2 ^ a + 2 ^ b + 2 ^ c by ring]; exact h)

/-- Combining the coincidence of two of `a, b, c` (the carry `2 ^ x + 2 ^ x = 2 ^ (x + 1)`) with
the uniqueness of the two-term representation gives the full classification, stated **without**
reducing the successor modulo `n`. -/
private theorem three_pow_aux {a b c d e : ℕ}
    (h : 2 ^ a + 2 ^ b + 2 ^ c = 2 ^ d + 2 ^ e) :
    (a = b ∧ d = a + 1 ∧ c = e) ∨ (a = b ∧ e = a + 1 ∧ c = d) ∨
    (a = c ∧ d = a + 1 ∧ b = e) ∨ (a = c ∧ e = a + 1 ∧ b = d) ∨
    (b = c ∧ d = b + 1 ∧ a = e) ∨ (b = c ∧ e = b + 1 ∧ a = d) := by
  rcases two_of_three_pow_eq h with hab | hac | hbc
  · have h2 : 2 ^ a + 2 ^ b = 2 ^ (a + 1) := by rw [hab]; exact two_pow_add_self b
    have h' : 2 ^ (a + 1) + 2 ^ c = 2 ^ d + 2 ^ e := by rw [← h2]; exact h
    rcases pair_unique h' with ⟨hd1, hce⟩ | ⟨he1, hcd⟩
    · exact Or.inl ⟨hab, hd1.symm, hce⟩
    · exact Or.inr (Or.inl ⟨hab, he1.symm, hcd⟩)
  · have h2 : 2 ^ a + 2 ^ c = 2 ^ (a + 1) := by rw [hac]; exact two_pow_add_self c
    have h' : 2 ^ (a + 1) + 2 ^ b = 2 ^ d + 2 ^ e := by rw [← h2]; linarith only [h]
    rcases pair_unique h' with ⟨hd1, hbe⟩ | ⟨he1, hbd⟩
    · exact Or.inr (Or.inr (Or.inl ⟨hac, hd1.symm, hbe⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hac, he1.symm, hbd⟩)))
  · have h2 : 2 ^ b + 2 ^ c = 2 ^ (b + 1) := by rw [hbc]; exact two_pow_add_self c
    have h' : 2 ^ (b + 1) + 2 ^ a = 2 ^ d + 2 ^ e := by rw [← h2]; linarith only [h]
    rcases pair_unique h' with ⟨hd1, hae⟩ | ⟨he1, had⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hbc, hd1.symm, hae⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hbc, he1.symm, had⟩))))

/-- Case `k = 0` of Higman's congruence (p. 92), i.e. of
`Work.Higman.Q3.L12.three_pow_congruence`: if `2 ^ a + 2 ^ b + 2 ^ c = 2 ^ d + 2 ^ e` exactly
(all exponents `< n`, `n > 0`), then two of `a, b, c` coincide and `{d, e}` is the pair
`{(common value + 1) mod n, the third exponent}`.

Proof idea (binary digits): the right-hand side has at most two binary ones, so `a, b, c` are not
pairwise distinct.  If exactly two coincide, say `a = b`, then `2 ^ (a+1) + 2 ^ c = 2 ^ d + 2 ^ e`
with `c < n`, and comparing binary expansions (including the carry case `a + 1 = c`, where both
sides are a single power up to the carry) gives `{d, e} = {a + 1 (mod n), c}`; if all three
coincide, `3 * 2 ^ a = 2 ^ a + 2 ^ (a+1)` gives the same conclusion with `a = c`.
Exhaustively verified for `n ≤ 24`. -/
theorem three_pow_zero_case {n a b c d e : ℕ} (hn : 0 < n)
    (ha : a < n) (hb : b < n) (hc : c < n) (hd : d < n) (he : e < n)
    (h : 2 ^ a + 2 ^ b + 2 ^ c = 2 ^ d + 2 ^ e) :
    (a = b ∧ d = (a + 1) % n ∧ c = e) ∨ (a = b ∧ e = (a + 1) % n ∧ c = d) ∨
    (a = c ∧ d = (a + 1) % n ∧ b = e) ∨ (a = c ∧ e = (a + 1) % n ∧ b = d) ∨
    (b = c ∧ d = (b + 1) % n ∧ a = e) ∨ (b = c ∧ e = (b + 1) % n ∧ a = d) := by
  rcases three_pow_aux h with ⟨hab, hd1, hce⟩ | ⟨hab, he1, hcd⟩ | ⟨hac, hd2, hbe⟩
    | ⟨hac, he2, hbd⟩ | ⟨hbc, hd3, hae⟩ | ⟨hbc, he3, had⟩
  · exact Or.inl ⟨hab, by rw [Nat.mod_eq_of_lt (by omega : a + 1 < n)]; omega, hce⟩
  · exact Or.inr (Or.inl ⟨hab, by rw [Nat.mod_eq_of_lt (by omega : a + 1 < n)]; omega, hcd⟩)
  · exact Or.inr (Or.inr (Or.inl
      ⟨hac, by rw [Nat.mod_eq_of_lt (by omega : a + 1 < n)]; omega, hbe⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨hac, by rw [Nat.mod_eq_of_lt (by omega : a + 1 < n)]; omega, hbd⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨hbc, by rw [Nat.mod_eq_of_lt (by omega : b + 1 < n)]; omega, hae⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨hbc, by rw [Nat.mod_eq_of_lt (by omega : b + 1 < n)]; omega, had⟩))))

end Work.Higman.Q3.L12
