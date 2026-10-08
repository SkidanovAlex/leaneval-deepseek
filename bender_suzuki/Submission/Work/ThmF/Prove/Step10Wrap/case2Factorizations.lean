import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.Prove.Step10Wrap

/-- Factorization at the prime `3` of a threefold product, one factor at a time.
(Used with `a = 8^3+1 = 3^3·19`, `b = 8^3 = 2^9`, `c = (2^3-1)·w·3`.) -/
lemma case2_factorization_prod_three {a b c : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    (a * b * c).factorization 3 = a.factorization 3 + b.factorization 3 + c.factorization 3 := by
  rw [Nat.factorization_mul (mul_ne_zero ha hb) hc, Finsupp.add_apply,
      Nat.factorization_mul ha hb, Finsupp.add_apply]

theorem case2Factorizations {p f q w g : ℕ} (hp : p = 3) (hf : f = 8) (hq : q = f ^ p) (hg : g = (q + 1) * q * ((2 ^ p - 1) * w * p)) (hw : w = 3 ∨ w = 9) : g.factorization 3 = 4 + w.factorization 3 ∧ 3 ^ (4 + w.factorization 3) = 3 ^ 4 * w := by
  -- `q = 8^3 = 512` and `g = 513 · 512 · (7 · w · 3)`, so the prime `3` enters
  -- through `513 = 3^3 · 19`, `2^3 - 1 = 7` (three-free) and the explicit `3`:
  -- `g.factorization 3 = 3 + 0 + (0 + w.factorization 3 + 1) = 4 + w.factorization 3`.
  subst hp; subst hf; subst hq; subst hg
  have hw0 : w ≠ 0 := by rcases hw with h | h <;> omega
  have h513 : (8 ^ 3 + 1 : ℕ).factorization 3 = 3 := by
    rw [show (8 ^ 3 + 1 : ℕ) = 3 ^ 3 * 19 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
        Nat.Prime.factorization_self (by norm_num : Nat.Prime 3),
        Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (3 : ℕ) ∣ 19)]
    all_goals norm_num
  have h512 : (8 ^ 3 : ℕ).factorization 3 = 0 := by
    rw [show (8 ^ 3 : ℕ) = 512 by norm_num]
    exact Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (3 : ℕ) ∣ 512)
  have h7 : (2 ^ 3 - 1 : ℕ).factorization 3 = 0 := by
    rw [show (2 ^ 3 - 1 : ℕ) = 7 by norm_num]
    exact Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (3 : ℕ) ∣ 7)
  have h3 : (3 : ℕ).factorization 3 = 1 := Nat.Prime.factorization_self (by norm_num)
  constructor
  · rw [case2_factorization_prod_three (a := 8 ^ 3 + 1) (b := 8 ^ 3) (c := (2 ^ 3 - 1) * w * 3)
        (by norm_num) (by norm_num) (by omega),
      case2_factorization_prod_three (a := 2 ^ 3 - 1) (b := w) (c := 3) (by norm_num) hw0 (by norm_num),
      h513, h512, h7, h3]
    omega
  · -- `w ∈ {3, 9}` is a power of `3`, so `3 ^ (4 + w.factorization 3) = 3^4 * w`.
    rcases hw with h | h
    · subst h; rw [h3]; norm_num
    · subst h
      have h9 : (9 : ℕ).factorization 3 = 2 := by
        rw [show (9 : ℕ) = 3 ^ 2 by norm_num, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
            Nat.Prime.factorization_self (by norm_num : Nat.Prime 3)]
        all_goals norm_num
      rw [h9]; norm_num

end Work.ThmF.Prove.Step10Wrap
