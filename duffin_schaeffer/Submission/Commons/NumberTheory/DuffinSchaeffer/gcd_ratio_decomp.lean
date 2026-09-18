import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Submission.Commons.NumberTheory.DuffinSchaeffer.padic_ratio_decomp

namespace Commons.NumberTheory.DuffinSchaeffer

/-- If `a ≤ n ≤ a + 1` then `a + [n = a + 1] = n`. -/
lemma add_indicator_eq_self {a n : ℕ} (h1 : a ≤ n) (h2 : n ≤ a + 1) :
    a + (if n = a + 1 then 1 else 0) = n := by
  by_cases hc : n = a + 1
  · rw [if_pos hc, hc]
  · rw [if_neg hc]; omega

/-- Arithmetic key: if the integer distances of `a` and `b` from `n` sum to at most
one, then `min a b + [n = a+1] + [b = n+1] = b`. -/
lemma min_add_indicator_eq {a b n : ℕ}
    (h : |((a:ℤ) - (n:ℤ))| + |((b:ℤ) - (n:ℤ))| ≤ 1) :
    min a b + (if n = a + 1 then 1 else 0) + (if b = n + 1 then 1 else 0) = b := by
  have habs1 : |((a:ℤ) - (n:ℤ))| ≤ 1 := le_trans (le_add_of_nonneg_right (abs_nonneg _)) h
  have habs2 : |((b:ℤ) - (n:ℤ))| ≤ 1 := le_trans (le_add_of_nonneg_left (abs_nonneg _)) h
  have ha1 : a ≤ n + 1 := by have := (abs_le.mp habs1).2; omega
  have ha2 : n ≤ a + 1 := by have := (abs_le.mp habs1).1; omega
  have hb1 : b ≤ n + 1 := by have := (abs_le.mp habs2).2; omega
  have hb2 : n ≤ b + 1 := by have := (abs_le.mp habs2).1; omega
  have heq : a = n ∨ b = n := by
    by_cases ha : a = n
    · exact Or.inl ha
    · right
      have hxne : ((a:ℤ) - (n:ℤ)) ≠ 0 := by
        intro hc; exact ha (by omega)
      have hx1 : (1:ℤ) ≤ |((a:ℤ) - (n:ℤ))| := by
        have hpos : 0 < |((a:ℤ) - (n:ℤ))| := abs_pos.mpr hxne
        omega
      have hy0 : |((b:ℤ) - (n:ℤ))| = 0 := by
        have hle := h; have := abs_nonneg ((b:ℤ) - (n:ℤ)); omega
      have hy0' : ((b:ℤ) - (n:ℤ)) = 0 := abs_eq_zero.mp hy0
      omega
  rcases heq with ha | hb
  · by_cases hbn : b ≤ n
    · have hmin : min a b = b := min_eq_right (by omega)
      have e1 : (if n = a + 1 then 1 else 0) = 0 := by rw [if_neg]; omega
      have e2 : (if b = n + 1 then 1 else 0) = 0 := by rw [if_neg]; omega
      rw [hmin, e1, e2]; omega
    · have hbeq : b = n + 1 := by omega
      have hmin : min a b = a := min_eq_left (by omega)
      have e1 : (if n = a + 1 then 1 else 0) = 0 := by rw [if_neg]; omega
      have e2 : (if b = n + 1 then 1 else 0) = 1 := by rw [if_pos hbeq]
      rw [hmin, e1, e2]; omega
  · by_cases han : a ≤ n
    · have hmin : min a b = a := min_eq_left (by omega)
      have e2 : (if b = n + 1 then 1 else 0) = 0 := by rw [if_neg]; omega
      rw [hmin, e2]
      have := add_indicator_eq_self (by omega : a ≤ n) (by omega : n ≤ a + 1)
      omega
    · have hmin : min a b = b := min_eq_right (by omega)
      have e1 : (if n = a + 1 then 1 else 0) = 0 := by rw [if_neg]; omega
      have e2 : (if b = n + 1 then 1 else 0) = 0 := by rw [if_neg]; omega
      rw [hmin, e1, e2]; omega

theorem gcd_ratio_decomp (N v w : ℕ) (hN : 0 < N) (hv : 0 < v) (hw : 0 < w)
    (h : ∀ p : ℕ, p.Prime →
      |((padicValNat p v : ℤ) - (padicValNat p N : ℤ))|
        + |((padicValNat p w : ℤ) - (padicValNat p N : ℤ))| ≤ 1) :
    (v.gcd w) * (∏ p ∈ (Nat.primeFactors N).filter (fun p => padicValNat p N = padicValNat p v + 1), p)
      * (∏ p ∈ (Nat.primeFactors w).filter (fun p => padicValNat p w = padicValNat p N + 1), p) = w := by
  set A := ∏ p ∈ (Nat.primeFactors N).filter (fun p => padicValNat p N = padicValNat p v + 1), p with hA
  set B := ∏ p ∈ (Nat.primeFactors w).filter (fun p => padicValNat p w = padicValNat p N + 1), p with hB
  have hAne : A ≠ 0 := by
    rw [hA]
    exact (Finset.prod_pos (fun p hp =>
      (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter p hp)).pos)).ne'
  have hBne : B ≠ 0 := by
    rw [hB]
    exact (Finset.prod_pos (fun p hp =>
      (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter p hp)).pos)).ne'
  have hg : v.gcd w ≠ 0 := (Nat.gcd_pos_of_pos_left w hv).ne'
  have hFactA : ∀ q, A.factorization q = if N.factorization q = v.factorization q + 1 then 1 else 0 := by
    intro q; rw [hA]; exact factorization_filter_prod_left N v q
  have hFactB : ∀ q, B.factorization q = if w.factorization q = N.factorization q + 1 then 1 else 0 := by
    intro q; rw [hB]; exact factorization_filter_prod_right N w q
  apply Nat.eq_of_factorization_eq (mul_ne_zero (mul_ne_zero hg hAne) hBne) hw.ne'
  intro q
  rw [Nat.factorization_mul (mul_ne_zero hg hAne) hBne,
      Nat.factorization_mul hg hAne,
      Nat.factorization_gcd hv.ne' hw.ne']
  simp only [Finsupp.add_apply, Finsupp.inf_apply]
  rw [hFactA q, hFactB q]
  by_cases hq : q.Prime
  · rw [Nat.factorization_def v hq, Nat.factorization_def w hq, Nat.factorization_def N hq]
    exact min_add_indicator_eq (h q hq)
  · rw [Nat.factorization_eq_zero_of_not_prime v hq, Nat.factorization_eq_zero_of_not_prime w hq,
        Nat.factorization_eq_zero_of_not_prime N hq]
    simp

end Commons.NumberTheory.DuffinSchaeffer