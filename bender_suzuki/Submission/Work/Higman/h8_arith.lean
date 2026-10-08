import Mathlib
import Submission.Work.Higman.clo_arith

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Arithmetic support for the final step of Higman's Lemma 8

`Work.Higman.two_pow_sum_mod_ne_one` (`clo_arith`) says that two *distinct* powers of two
below `2 ^ n` are never congruent to `1` modulo `2 ^ n - 1`.  The Frobenius conjugates of
`ν ^ (2 ^ k + 2 ^ l)` have exponents `2 ^ (k + s) + 2 ^ (l + s)`, which need not be below `n`;
the two lemmas here handle that by reducing the exponents modulo `n`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Higman

/-- `2 ^ k ≡ 2 ^ (k % n)` modulo `2 ^ n - 1`. -/
theorem two_pow_modEq_mod {n k : ℕ} (hn : 1 ≤ n) :
    2 ^ k ≡ 2 ^ (k % n) [MOD 2 ^ n - 1] := by
  have h2n : (2 : ℕ) ^ n ≡ 1 [MOD 2 ^ n - 1] := by
    have hkey : ((2 ^ n - 1) + 1) % (2 ^ n - 1) = 1 % (2 ^ n - 1) := by
      rw [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]
    have hN1 : 2 ^ n = (2 ^ n - 1) + 1 := by
      have : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
      omega
    rw [Nat.ModEq]
    nth_rw 1 [hN1]
    exact hkey
  have hx : k = (k / n) * n + k % n := by
    rw [mul_comm]
    exact (Nat.div_add_mod k n).symm
  calc 2 ^ k = 2 ^ ((k / n) * n + k % n) := congrArg (fun t => 2 ^ t) hx
    _ = (2 ^ n) ^ (k / n) * 2 ^ (k % n) := by
        rw [pow_add, mul_comm (k / n) n, ← pow_mul]
    _ ≡ 1 ^ (k / n) * 2 ^ (k % n) [MOD 2 ^ n - 1] :=
        Nat.ModEq.mul (h2n.pow _) (Nat.ModEq.refl _)
    _ = 2 ^ (k % n) := by simp

/-- `2 ^ a + 2 ^ b` is never congruent to `1` modulo `2 ^ n - 1` when `a % n ≠ b % n`
(`2 ≤ n`). -/
theorem two_pow_sum_mod_ne_one_general {n a b : ℕ} (h2 : 2 ≤ n) (hab : a % n ≠ b % n) :
    ¬ (2 ^ a + 2 ^ b ≡ 1 [MOD 2 ^ n - 1]) := by
  intro h
  have hn : 1 ≤ n := by omega
  have h1 : 2 ^ a ≡ 2 ^ (a % n) [MOD 2 ^ n - 1] := two_pow_modEq_mod hn
  have h2' : 2 ^ b ≡ 2 ^ (b % n) [MOD 2 ^ n - 1] := two_pow_modEq_mod hn
  have hs : 2 ^ (a % n) + 2 ^ (b % n) ≡ 1 [MOD 2 ^ n - 1] :=
    (h1.add h2').symm.trans h
  exact two_pow_sum_mod_ne_one h2 (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) hab hs

/-- For `k ≠ l` both `< n` (`2 ≤ n`) and any `s`, `2 ^ (k + s) + 2 ^ (l + s)` is never
congruent to `1` modulo `2 ^ n - 1`. -/
theorem two_pow_add_mod_ne_one_of_ne {n k l s : ℕ} (h2 : 2 ≤ n) (hkl : k ≠ l) (hkn : k < n)
    (hln : l < n) : ¬ (2 ^ (k + s) + 2 ^ (l + s) ≡ 1 [MOD 2 ^ n - 1]) := by
  refine two_pow_sum_mod_ne_one_general h2 (fun hc => hkl ?_)
  have hm : (k + s) ≡ (l + s) [MOD n] := by rw [Nat.ModEq]; exact hc
  exact Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.add_right_cancel' s hm) hkn hln

/-- **The Frobenius conjugates of `ν ^ (2 ^ k + 2 ^ l)` are all different from `ν`.**  If `ν` has
order `2 ^ n - 1`, `2 ≤ n`, `k ≠ l` and `k, l < n`, then `ν ^ (2 ^ k + 2 ^ l)` is not
Frobenius-conjugate to `ν`, i.e. `ν ≠ (ν ^ (2 ^ k + 2 ^ l)) ^ (2 ^ s)` for every `s`. -/
theorem pow_two_add_not_conj {n k l : ℕ} (h2 : 2 ≤ n) (hkl : k ≠ l) (hkn : k < n) (hln : l < n)
    {F : Type*} [Field F] [Finite F] {ν : F} (hν : orderOf ν = 2 ^ n - 1) (s : ℕ) :
    ν ≠ (ν ^ (2 ^ k + 2 ^ l)) ^ 2 ^ s := by
  intro hc
  have hNpos : 0 < 2 ^ n - 1 := by
    have : 1 < 2 ^ n := Nat.one_lt_pow (by omega) (by norm_num)
    omega
  have hfin : IsOfFinOrder ν := by
    rw [isOfFinOrder_iff_pow_eq_one]
    exact ⟨2 ^ n - 1, hNpos, by rw [← hν]; exact pow_orderOf_eq_one ν⟩
  have hmod : (2 ^ k + 2 ^ l) * 2 ^ s ≡ 1 [MOD 2 ^ n - 1] := by
    have hpoweq : ν ^ ((2 ^ k + 2 ^ l) * 2 ^ s) = ν ^ 1 := by
      rw [pow_one, pow_mul]; exact hc.symm
    have := (IsOfFinOrder.pow_eq_pow_iff_modEq hfin).mp hpoweq
    rwa [hν] at this
  have hexp : (2 ^ k + 2 ^ l) * 2 ^ s = 2 ^ (k + s) + 2 ^ (l + s) := by
    rw [add_mul, ← pow_add, ← pow_add]
  rw [hexp] at hmod
  exact two_pow_add_mod_ne_one_of_ne h2 hkl hkn hln hmod

end Work.Higman
