import Mathlib
import Submission.Work.Higman.Q3.L12.three_pow_zero_case
import Submission.Work.Higman.Q3.L12.three_pow_one_case

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman.Q3.L12

/-- **Higman (1963), the congruence on p. 92** (used in the `C` and `D` cases of Lemma 12).

If `2 ^ a + 2 ^ b + 2 ^ c ≡ 2 ^ d + 2 ^ e (mod 2 ^ n - 1)` with all exponents in `[0, n)`, then
either two of `a, b, c` are equal and `d, e` are the successor (mod `n`) of that common value and
the third exponent.  This is Higman's "only the trivial solution `a ≡ b ≡ d - 1`, `c ≡ e (mod n)`,
and the solutions obtained from it by permuting `a, b, c` and `d, e`".  (Exhaustively verified for
`n ≤ 15`.)

Proof sketch: put `2 ^ a + 2 ^ b + 2 ^ c - (2 ^ d + 2 ^ e) = k (2 ^ n - 1)`.  The left side lies in
`[3 - 2 ^ n, 3 * 2 ^ (n-1) - 2]`, so `k ∈ {-1, 0, 1}`; then compare binary expansions, carrying
the sums of equal powers and the wraparound `2 ^ n ≡ 1`.  (A case check shows `k = 0` and
`k = -1` are impossible and `k = 1` gives the stated solutions.) -/
theorem three_pow_congruence {n : ℕ} (hn : 0 < n) {a b c d e : ℕ}
    (ha : a < n) (hb : b < n) (hc : c < n) (hd : d < n) (he : e < n)
    (h : (2 ^ a + 2 ^ b + 2 ^ c) ≡ (2 ^ d + 2 ^ e) [MOD 2 ^ n - 1]) :
    (a = b ∧ d = (a + 1) % n ∧ c = e) ∨ (a = b ∧ e = (a + 1) % n ∧ c = d) ∨
    (a = c ∧ d = (a + 1) % n ∧ b = e) ∨ (a = c ∧ e = (a + 1) % n ∧ b = d) ∨
    (b = c ∧ d = (b + 1) % n ∧ a = e) ∨ (b = c ∧ e = (b + 1) % n ∧ a = d) := by
  -- basic power relations
  have h2n : 2 ≤ 2 ^ n := by
    have hn1 : 1 ≤ n := by omega
    simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hn1
  have hrel : 2 ^ n = 2 * 2 ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [pow_succ']
  have ht : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
  have hpa : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  have hpb : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  have hpc : 1 ≤ 2 ^ c := Nat.one_le_two_pow
  have hpd : 1 ≤ 2 ^ d := Nat.one_le_two_pow
  have hpe : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  have hna : 2 ^ a ≤ 2 ^ (n - 1) :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
  have hnb : 2 ^ b ≤ 2 ^ (n - 1) :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
  have hnc : 2 ^ c ≤ 2 ^ (n - 1) :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
  have hnd : 2 ^ d ≤ 2 ^ (n - 1) :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
  have hne : 2 ^ e ≤ 2 ^ (n - 1) :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
  have hA_ge : 3 ≤ 2 ^ a + 2 ^ b + 2 ^ c := by omega
  have hB_ge : 2 ≤ 2 ^ d + 2 ^ e := by omega
  have hB_le : 2 ^ d + 2 ^ e ≤ 2 ^ n := by
    have h2 : 2 ^ (n - 1) + 2 ^ (n - 1) = 2 ^ n := by omega
    omega
  have hA_le : 2 ^ a + 2 ^ b + 2 ^ c ≤ 3 * 2 ^ (n - 1) := by omega
  -- main inequality: the left side is always at least the right side
  have hBA : 2 ^ d + 2 ^ e ≤ 2 ^ a + 2 ^ b + 2 ^ c := by
    by_contra hcon
    push_neg at hcon
    have hdvd := (Nat.modEq_iff_dvd' hcon.le).mp h
    have hpos : 0 < (2 ^ d + 2 ^ e) - (2 ^ a + 2 ^ b + 2 ^ c) := Nat.sub_pos_of_lt hcon
    have hle1 : 2 ^ n - 1 ≤ (2 ^ d + 2 ^ e) - (2 ^ a + 2 ^ b + 2 ^ c) :=
      Nat.le_of_dvd hpos hdvd
    have hlt2 : (2 ^ d + 2 ^ e) - (2 ^ a + 2 ^ b + 2 ^ c) ≤ 2 ^ n - 3 := by
      have h1 : (2 ^ d + 2 ^ e) - (2 ^ a + 2 ^ b + 2 ^ c) ≤ (2 ^ d + 2 ^ e) - 3 :=
        Nat.sub_le_sub_left hA_ge (2 ^ d + 2 ^ e)
      have h2 : (2 ^ d + 2 ^ e) - 3 ≤ 2 ^ n - 3 := Nat.sub_le_sub_right hB_le 3
      omega
    omega
  -- divisibility and size bound for A - B
  have hdvdAB : 2 ^ n - 1 ∣ (2 ^ a + 2 ^ b + 2 ^ c) - (2 ^ d + 2 ^ e) :=
    (Nat.modEq_iff_dvd' hBA).mp h.symm
  have hAB_lt : (2 ^ a + 2 ^ b + 2 ^ c) - (2 ^ d + 2 ^ e) < 2 * (2 ^ n - 1) := by
    have h1 : (2 ^ a + 2 ^ b + 2 ^ c) - (2 ^ d + 2 ^ e) ≤ (2 ^ a + 2 ^ b + 2 ^ c) - 2 :=
      Nat.sub_le_sub_left hB_ge (2 ^ a + 2 ^ b + 2 ^ c)
    have h2 : (2 ^ a + 2 ^ b + 2 ^ c) - 2 ≤ 3 * 2 ^ (n - 1) - 2 :=
      Nat.sub_le_sub_right hA_le 2
    have h3 : 3 * 2 ^ (n - 1) - 2 < 2 * (2 ^ n - 1) := by omega
    omega
  obtain ⟨q, hq⟩ := hdvdAB
  have hMpos : 0 < 2 ^ n - 1 := by omega
  have hq_lt2 : q < 2 := by
    have hh : (2 ^ n - 1) * q < (2 ^ n - 1) * 2 := by
      rw [← hq, mul_comm (2 ^ n - 1) 2]
      exact hAB_lt
    exact (Nat.mul_lt_mul_left hMpos).mp hh
  have hq_cases : q = 0 ∨ q = 1 := by omega
  rcases hq_cases with hq0 | hq1
  · -- `A - B = 0`: the exact equality case
    have hzero : (2 ^ a + 2 ^ b + 2 ^ c) - (2 ^ d + 2 ^ e) = 0 := by rw [hq, hq0]; ring
    have hAB : 2 ^ a + 2 ^ b + 2 ^ c = 2 ^ d + 2 ^ e :=
      le_antisymm (Nat.sub_eq_zero_iff_le.mp hzero) hBA
    exact three_pow_zero_case hn ha hb hc hd he hAB
  · -- `A - B = 2^n - 1`: the wraparound case
    have hAeq : 2 ^ a + 2 ^ b + 2 ^ c = (2 ^ n - 1) + (2 ^ d + 2 ^ e) := by
      have hsub : (2 ^ a + 2 ^ b + 2 ^ c) - (2 ^ d + 2 ^ e) + (2 ^ d + 2 ^ e)
          = 2 ^ a + 2 ^ b + 2 ^ c := Nat.sub_add_cancel hBA
      rw [hq, hq1, Nat.mul_one] at hsub
      omega
    have hmain : 2 ^ a + 2 ^ b + 2 ^ c + 1 = 2 ^ d + 2 ^ e + 2 ^ n := by
      have hp1 : (2 ^ n - 1) + 1 = 2 ^ n := Nat.sub_add_cancel (by omega : 1 ≤ 2 ^ n)
      rw [hAeq]
      omega
    exact three_pow_one_case hn ha hb hc hd he hmain

end Work.Higman.Q3.L12
