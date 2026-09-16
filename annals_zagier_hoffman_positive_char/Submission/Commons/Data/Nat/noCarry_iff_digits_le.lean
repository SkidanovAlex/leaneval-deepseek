import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Defs

namespace Commons.Data.Nat

/-- Peeling off the lowest base-`p` digit: `a / p ^ (j+1) = (a / p) / p ^ j`. -/
lemma div_pow_succ_eq (a p j : ℕ) : a / p ^ (j + 1) = (a / p) / p ^ j := by
  rw [pow_succ', Nat.div_div_eq_div_mul]

/-- Recursion for the "no carry" predicate: the condition at all positions is
equivalent to the condition at position `0` together with the condition at all
positions for the numbers `a / p`, `b / p`. -/
lemma noCarry_rec (p a b : ℕ) :
    (∀ i : ℕ, a / p ^ i % p + b / p ^ i % p < p) ↔
      (a % p + b % p < p) ∧
        (∀ i : ℕ, (a / p) / p ^ i % p + (b / p) / p ^ i % p < p) := by
  constructor
  · intro h
    refine ⟨by simpa using h 0, ?_⟩
    intro i
    have h' := h (i + 1)
    rwa [div_pow_succ_eq a p i, div_pow_succ_eq b p i] at h'
  · rintro ⟨h0, h⟩ i
    cases i with
    | zero => simpa using h0
    | succ j =>
        rw [div_pow_succ_eq a p j, div_pow_succ_eq b p j]
        exact h j

/-- Recursion for the digitwise comparison predicate: the condition at all
positions is equivalent to the condition at position `0` together with the
condition at all positions for the numbers `a / p`, `s / p`. -/
lemma digit_le_rec (p a s : ℕ) :
    (∀ i : ℕ, a / p ^ i % p ≤ s / p ^ i % p) ↔
      (a % p ≤ s % p) ∧
        (∀ i : ℕ, (a / p) / p ^ i % p ≤ (s / p) / p ^ i % p) := by
  constructor
  · intro h
    refine ⟨by simpa using h 0, ?_⟩
    intro i
    have h' := h (i + 1)
    rwa [div_pow_succ_eq a p i, div_pow_succ_eq s p i] at h'
  · rintro ⟨h0, h⟩ i
    cases i with
    | zero => simpa using h0
    | succ j =>
        rw [div_pow_succ_eq a p j, div_pow_succ_eq s p j]
        exact h j

theorem noCarry_iff_digits_le {p : ℕ} (hp : p.Prime) (a b : ℕ) :
    (∀ i : ℕ, a / p ^ i % p + b / p ^ i % p < p) ↔
      ∀ i : ℕ, a / p ^ i % p ≤ (a + b) / p ^ i % p := by
  have hp2 : 1 < p := hp.one_lt
  have hppos : 0 < p := hp.pos
  -- Strong induction on the sum `a + b`, peeling off the lowest digit.
  suffices h : ∀ s a b, a + b = s →
      ((∀ i : ℕ, a / p ^ i % p + b / p ^ i % p < p) ↔
       ∀ i : ℕ, a / p ^ i % p ≤ (a + b) / p ^ i % p) by
    exact h (a + b) a b rfl
  intro s
  induction s using Nat.strong_induction_on with
  | h n ih =>
    intro a b hab
    rcases eq_or_ne n 0 with hs | hs
    · -- base case: `a = b = 0`
      have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      subst ha; subst hb
      simp [hppos]
    · by_cases hlt : a % p + b % p < p
      · -- no carry out of the lowest digit: the recursion applies on both sides
        have hdiv : (a + b) / p = a / p + b / p := Nat.add_div_eq_of_add_mod_lt hlt
        have hmod : (a + b) % p = a % p + b % p := Nat.add_mod_of_add_mod_lt hlt
        have hsp_lt : n / p < n := Nat.div_lt_self (Nat.pos_of_ne_zero hs) hp2
        have ih' := ih (n / p) hsp_lt (a / p) (b / p) (by rw [← hdiv, hab])
        rw [noCarry_rec, digit_le_rec]
        rw [hdiv, hmod]
        have hle : a % p ≤ a % p + b % p := Nat.le_add_right _ _
        simp only [hlt, hle, true_and]
        exact ih'
      · -- carry out of the lowest digit: both sides fail at position `0`
        have hge : p ≤ a % p + b % p := not_lt.mp hlt
        have hmodle : (a + b) % p + p = a % p + b % p := Nat.add_mod_add_of_le_add_mod hge
        have hbp : b % p < p := Nat.mod_lt _ hppos
        have hlt' : (a + b) % p < a % p := by omega
        have h1 : ¬ (a % p + b % p < p) := not_lt.mpr hge
        have h2 : ¬ (a % p ≤ (a + b) % p) := not_le.mpr hlt'
        rw [noCarry_rec, digit_le_rec]
        simp [h1, h2]

end Commons.Data.Nat