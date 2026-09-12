import Mathlib

open scoped BigOperators

namespace Commons.Algebra.BigOperators

open Finset

/-- Telescoping identity over an integer interval:
`∑_{j=M}^{t} (f (j+1) - f j) = f (t+1) - f M` for `M ≤ t`. -/
lemma sum_Icc_shift_sub {G : Type*} [AddCommGroup G] (M t : ℕ) (h : M ≤ t) (f : ℕ → G) :
    ∑ j ∈ Finset.Icc M t, (f (j + 1) - f j) = f (t + 1) - f M := by
  rw [← Finset.Ico_add_one_right_eq_Icc M t]
  rw [Finset.sum_Ico_eq_sub _ (show M ≤ t + 1 by omega)]
  rw [Finset.sum_range_sub, Finset.sum_range_sub]
  abel

/-- For `0 ≤ a`, `(a+1)^(k+1) - a^(k+1) ≤ (k+1) (a+1)^k`. -/
lemma pow_succ_sub_pow_le (a : ℚ) (ha : 0 ≤ a) (k : ℕ) :
    (a + 1) ^ (k + 1) - a ^ (k + 1) ≤ (k + 1 : ℚ) * (a + 1) ^ k := by
  have hx : a ≤ a + 1 := by linarith
  have hpow : ∀ i, (k + 1) - 1 - i = k - i := fun i => by omega
  have hval : (a + 1) ^ (k + 1) - a ^ (k + 1)
      = ∑ i ∈ Finset.range (k + 1), (a + 1) ^ i * a ^ (k - i) := by
    have h := geom_sum₂_mul (a + 1) a (k + 1)
    rw [show (a + 1) - a = 1 by ring, mul_one] at h
    simpa [hpow] using h.symm
  rw [hval]
  calc ∑ i ∈ Finset.range (k + 1), (a + 1) ^ i * a ^ (k - i)
      ≤ ∑ _i ∈ Finset.range (k + 1), (a + 1) ^ k := by
        apply Finset.sum_le_sum
        intro i hi
        have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have h1 : a ^ (k - i) ≤ (a + 1) ^ (k - i) := pow_le_pow_left₀ ha hx (k - i)
        calc (a + 1) ^ i * a ^ (k - i)
            ≤ (a + 1) ^ i * (a + 1) ^ (k - i) :=
              mul_le_mul_of_nonneg_left h1 (pow_nonneg (by linarith) i)
          _ = (a + 1) ^ k := by rw [← pow_add, Nat.add_sub_cancel' hik]
    _ = (k + 1 : ℚ) * (a + 1) ^ k := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-- The termwise lower bound used in the telescoping estimate. -/
lemma le_pow_diff_div (a : ℚ) (ha : 0 ≤ a) (k : ℕ) :
    ((a + 1) ^ (k + 1) - a ^ (k + 1)) / (k + 1 : ℚ) ≤ (a + 1) ^ k := by
  rw [div_le_iff₀ (by positivity : (0 : ℚ) < (k + 1))]
  calc (a + 1) ^ (k + 1) - a ^ (k + 1) ≤ (k + 1 : ℚ) * (a + 1) ^ k := pow_succ_sub_pow_le a ha k
    _ = (a + 1) ^ k * (k + 1 : ℚ) := by ring

theorem sum_Icc_pow_lower_bound (k M : ℕ) :
    ∃ c : ℚ, 0 < c ∧ ∃ N : ℕ, ∀ t : ℕ, N ≤ t →
      c * ((t : ℚ) + 1) ^ (k + 1) ≤ ∑ j ∈ Finset.Icc M t, ((j : ℚ) + 1) ^ k := by
  refine ⟨1 / (2 * (k + 1)), ?_, 2 * M + 1, ?_⟩
  · positivity
  · intro t ht
    have hMle : M ≤ t := by omega
    have hterm : ∀ j ∈ Finset.Icc M t,
        (((j : ℚ) + 1) ^ (k + 1) - (j : ℚ) ^ (k + 1)) / (k + 1 : ℚ) ≤ ((j : ℚ) + 1) ^ k :=
      fun j _ => le_pow_diff_div (j : ℚ) (Nat.cast_nonneg j) k
    have htel : ∑ j ∈ Finset.Icc M t, (((j : ℚ) + 1) ^ (k + 1) - (j : ℚ) ^ (k + 1))
        = ((t : ℚ) + 1) ^ (k + 1) - (M : ℚ) ^ (k + 1) := by
      have h := sum_Icc_shift_sub M t hMle (fun j : ℕ => (j : ℚ) ^ (k + 1))
      simpa [Nat.cast_add, Nat.cast_one] using h
    have hbound : (((t : ℚ) + 1) ^ (k + 1) - (M : ℚ) ^ (k + 1)) / (k + 1 : ℚ)
        ≤ ∑ j ∈ Finset.Icc M t, ((j : ℚ) + 1) ^ k := by
      have h := Finset.sum_le_sum hterm
      rw [← Finset.sum_div] at h
      rwa [htel] at h
    have hpow2 : 2 * (M : ℚ) ^ (k + 1) ≤ ((t : ℚ) + 1) ^ (k + 1) := by
      have ha : (2 : ℚ) * (M : ℚ) ≤ (t : ℚ) + 1 := by
        have hcast : ((2 * M + 1 : ℕ) : ℚ) ≤ (t : ℚ) := by exact_mod_cast ht
        push_cast at hcast
        linarith
      have h1 : (2 * (M : ℚ)) ^ (k + 1) ≤ ((t : ℚ) + 1) ^ (k + 1) :=
        pow_le_pow_left₀ (by positivity) ha (k + 1)
      have h2 : 2 * (M : ℚ) ^ (k + 1) ≤ (2 * (M : ℚ)) ^ (k + 1) := by
        rw [mul_pow]
        have hle : (2 : ℚ) ≤ 2 ^ (k + 1) := by
          calc (2 : ℚ) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
        exact mul_le_mul_of_nonneg_right hle (pow_nonneg (Nat.cast_nonneg M) (k + 1))
      linarith
    have hfinal : 1 / (2 * (k + 1)) * ((t : ℚ) + 1) ^ (k + 1)
        ≤ (((t : ℚ) + 1) ^ (k + 1) - (M : ℚ) ^ (k + 1)) / (k + 1 : ℚ) := by
      rw [le_div_iff₀ (by positivity : (0 : ℚ) < (k + 1))]
      have h1 : (1 / (2 * (k + 1)) : ℚ) * (k + 1) = 1 / 2 := by
        have hk : (k + 1 : ℚ) ≠ 0 := by positivity
        field_simp
      calc (1 / (2 * (k + 1)) : ℚ) * ((t : ℚ) + 1) ^ (k + 1) * (k + 1)
          = ((1 / (2 * (k + 1)) : ℚ) * (k + 1)) * ((t : ℚ) + 1) ^ (k + 1) := by ring
        _ = (1 / 2) * ((t : ℚ) + 1) ^ (k + 1) := by rw [h1]
        _ = ((t : ℚ) + 1) ^ (k + 1) / 2 := by ring
        _ ≤ ((t : ℚ) + 1) ^ (k + 1) - (M : ℚ) ^ (k + 1) := by linarith
    linarith [hfinal, hbound]

end Commons.Algebra.BigOperators
