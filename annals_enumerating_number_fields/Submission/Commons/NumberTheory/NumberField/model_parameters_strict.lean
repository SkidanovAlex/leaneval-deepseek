import Mathlib
import Submission.Commons.NumberTheory.NumberField.model_parameters

/-!
# Strict model parameters (Couveignes, §4)

The companion lemma `model_parameters` produces an `r` with
`2(n-1)(r+1) ≤ centralBinom r`.  Here we need the *strict* lower bound
`2(n-1)(r+1) < centralBinom r`, together with the same upper bound
`centralBinom r ≤ 16 n (r+1)`, `6 ≤ r` and `r ≤ 2 log₂ n + 12`.

The argument is identical in shape to `model_parameters`: take `r` minimal
among the integers `≥ 6` satisfying the strict lower bound, and use the
two-term recurrence `centralBinom (r+1) = centralBinom r · 2(2r+1)/(r+1)`.
-/

namespace Commons.NumberTheory.NumberField

theorem model_parameters_strict (n : ℕ) (hn : 100 ≤ n) :
    ∃ r : ℕ, 2 * (n - 1) * (r + 1) < Nat.centralBinom r ∧
      Nat.centralBinom r ≤ 16 * n * (r + 1) ∧ 6 ≤ r ∧
      r ≤ 2 * (Nat.log 2 n) + 12 := by
  have hn0 : n ≠ 0 := by omega
  set L := Nat.log 2 n with hL
  have hL6 : 6 ≤ L := by
    have h64 : 2 ^ 6 ≤ n := by norm_num; omega
    exact Nat.le_log_of_pow_le (by norm_num : 1 < 2) h64
  have hlt : n < 2 ^ (L + 1) := by
    have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num : 1 < 2) n
    simpa [hL] using h
  -- An explicit witness satisfying the *strict* lower bound.
  have hwit : 2 * (n - 1) * (L + 2 + 1) < Nat.centralBinom (L + 2) := by
    have hn1 : n - 1 < 2 ^ (L + 1) := by omega
    have e1 : 2 * (n - 1) * (L + 2 + 1) < 2 ^ (L + 2) * (L + 2 + 1) := by
      have h2 : 2 * (n - 1) < 2 ^ (L + 2) := by
        calc 2 * (n - 1) < 2 * 2 ^ (L + 1) :=
              Nat.mul_lt_mul_of_pos_left hn1 (by norm_num)
          _ = 2 ^ (L + 2) := by
              rw [show L + 2 = L + 1 + 1 by omega, pow_succ]; ring
      exact Nat.mul_lt_mul_of_pos_right h2 (by omega)
    have e2 : 2 ^ (L + 2) * (L + 2 + 1) ≤ Nat.centralBinom (L + 2) := by
      have h4 : 4 ≤ L + 2 := by omega
      have hlow := Nat.four_pow_lt_mul_centralBinom (L + 2) h4
      have hsq : (4 : ℕ) ^ (L + 2) = 2 ^ (L + 2) * 2 ^ (L + 2) := by
        rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]
      have hkey : (L + 2) * (2 ^ (L + 2) * (L + 2 + 1)) ≤ 4 ^ (L + 2) := by
        rw [hsq]
        calc (L + 2) * (2 ^ (L + 2) * (L + 2 + 1))
            = 2 ^ (L + 2) * ((L + 2) * (L + 3)) := by
              rw [show L + 2 + 1 = L + 3 by omega]; ring
          _ ≤ 2 ^ (L + 2) * 2 ^ (L + 2) :=
              Nat.mul_le_mul_left _ (mul_add_le_two_pow L hL6)
      have hstrict : (L + 2) * (2 ^ (L + 2) * (L + 2 + 1)) <
          (L + 2) * Nat.centralBinom (L + 2) := lt_of_le_of_lt hkey hlow
      exact le_of_lt (Nat.lt_of_mul_lt_mul_left hstrict)
    exact lt_of_lt_of_le e1 e2
  -- Take the least `r ≥ 6` satisfying the strict lower bound.
  have hex : ∃ r : ℕ, 6 ≤ r ∧ 2 * (n - 1) * (r + 1) < Nat.centralBinom r :=
    ⟨L + 2, by omega, by simpa using hwit⟩
  obtain ⟨hge, hlowc⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, hlowc, ?_, hge, ?_⟩
  · -- Upper bound, from minimality of `Nat.find hex`.
    have hc6 : Nat.centralBinom 6 = 924 := by norm_num [Nat.centralBinom, Nat.choose]
    have hrne : Nat.find hex ≠ 6 := by
      intro h
      have h99 : 99 ≤ n - 1 := by omega
      have hle : 2 * 99 * 7 ≤ 2 * (n - 1) * (Nat.find hex + 1) := by
        rw [h]
        calc 2 * 99 * 7 ≤ 2 * (n - 1) * 7 :=
              Nat.mul_le_mul_right 7 (Nat.mul_le_mul_left 2 h99)
          _ = 2 * (n - 1) * (6 + 1) := by norm_num
      have hcontra : 1386 ≤ 924 := by
        calc (1386 : ℕ) = 2 * 99 * 7 := by norm_num
          _ ≤ 2 * (n - 1) * (Nat.find hex + 1) := hle
          _ ≤ Nat.centralBinom (Nat.find hex) := le_of_lt hlowc
          _ = Nat.centralBinom 6 := by rw [h]
          _ = 924 := hc6
      norm_num at hcontra
    have hr1 : 1 ≤ Nat.find hex := by omega
    have hnot := Nat.find_min hex (Nat.sub_one_lt (by omega : Nat.find hex ≠ 0))
    have hprev : Nat.centralBinom (Nat.find hex - 1) ≤ 2 * (n - 1) * Nat.find hex := by
      by_contra hcon
      rw [not_le] at hcon
      have h6 : 6 ≤ Nat.find hex - 1 := by omega
      have hsecond : 2 * (n - 1) * (Nat.find hex - 1 + 1) <
          Nat.centralBinom (Nat.find hex - 1) := by
        rwa [Nat.sub_add_cancel hr1]
      exact hnot ⟨h6, hsecond⟩
    have hratio : Nat.find hex * Nat.centralBinom (Nat.find hex)
        = 2 * (2 * Nat.find hex - 1) * Nat.centralBinom (Nat.find hex - 1) := by
      have h := Nat.succ_mul_centralBinom_succ (Nat.find hex - 1)
      rw [Nat.sub_add_cancel hr1] at h
      have h2 : 2 * (Nat.find hex - 1) + 1 = 2 * Nat.find hex - 1 := by omega
      rwa [h2] at h
    have hstep : Nat.find hex * Nat.centralBinom (Nat.find hex)
        ≤ Nat.find hex * (4 * (n - 1) * (2 * Nat.find hex - 1)) := by
      calc Nat.find hex * Nat.centralBinom (Nat.find hex)
          = 2 * (2 * Nat.find hex - 1) * Nat.centralBinom (Nat.find hex - 1) := hratio
        _ ≤ 2 * (2 * Nat.find hex - 1) * (2 * (n - 1) * Nat.find hex) :=
              Nat.mul_le_mul_left (2 * (2 * Nat.find hex - 1)) hprev
        _ = Nat.find hex * (4 * (n - 1) * (2 * Nat.find hex - 1)) := by ring
    have hC : Nat.centralBinom (Nat.find hex) ≤ 4 * (n - 1) * (2 * Nat.find hex - 1) :=
      Nat.le_of_mul_le_mul_left hstep (by omega : 0 < Nat.find hex)
    have hle1 : 4 * (n - 1) * (2 * Nat.find hex - 1) ≤ 16 * n * (Nat.find hex + 1) := by
      calc 4 * (n - 1) * (2 * Nat.find hex - 1)
          = 4 * ((n - 1) * (2 * Nat.find hex - 1)) := by ring
        _ ≤ 4 * (n * (2 * Nat.find hex - 1)) :=
              Nat.mul_le_mul_left 4 (Nat.mul_le_mul_right _ (Nat.sub_le n 1))
        _ = 4 * n * (2 * Nat.find hex - 1) := by ring
        _ ≤ 4 * n * (4 * (Nat.find hex + 1)) :=
              Nat.mul_le_mul_left _ (by omega)
        _ = 16 * n * (Nat.find hex + 1) := by ring
    exact le_trans hC hle1
  · -- Bound on `Nat.find hex`.
    have hle : Nat.find hex ≤ L + 2 :=
      Nat.find_min' hex ⟨by omega, by simpa using hwit⟩
    omega

end Commons.NumberTheory.NumberField
