import Mathlib

namespace Work.A3.Weil

/-- Auxiliary form of `pow_le_of_rpow_le` for an arbitrary natural exponent `n ≥ 1`:
if `S ^ n ≤ C * N ^ n * N ^ ε * B` with `S, C, N, B ≥ 0`, `C, N ≥ 1`, `ε ≥ 0`,
then `S ≤ C * N ^ (1 + ε) * B ^ (1 / n)`.

The `n`-th root of the right-hand side is `Cᵃ * (Nⁿ)ᵃ * (N^ε)ᵃ * Bᵃ` with `a = 1/n`,
and each factor is bounded by the corresponding factor of the right-hand side:
`Cᵃ ≤ C`, `(Nⁿ)ᵃ = N`, `(N^ε)ᵃ = N^(ε/n) ≤ N^ε`, `Bᵃ = Bᵃ`. -/
private theorem rpow_le_of_pow_le_aux {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : 0 ≤ ε) {S C N B : ℝ}
    (hS : 0 ≤ S) (hC : 1 ≤ C) (hN : 1 ≤ N) (hB : 0 ≤ B)
    (h : S ^ n ≤ C * N ^ (n : ℝ) * N ^ ε * B) :
    S ≤ C * N ^ (1 + ε) * B ^ ((1 : ℝ) / (n : ℝ)) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one hn1
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN
  have hNnn : (0 : ℝ) ≤ N := hNpos.le
  set r : ℝ := (1 : ℝ) / (n : ℝ) with hr
  have hrpos : (0 : ℝ) < r := by rw [hr]; positivity
  have hrle1 : r ≤ 1 := by rw [hr]; exact div_le_one_of_le₀ hn1 (by positivity)
  have hnr : (n : ℝ) * r = 1 := by rw [hr, mul_one_div, div_self (ne_of_gt hn0)]
  -- Step 1: extract the `n`-th root of the hypothesis.
  have hstep1 : S ≤ (C * N ^ (n : ℝ) * N ^ ε * B) ^ r := by
    have hpow := Real.rpow_le_rpow (pow_nonneg hS n) h hrpos.le
    have hSr : (S ^ n) ^ r = S := by
      rw [← Real.rpow_natCast S n, ← Real.rpow_mul hS, hnr, Real.rpow_one]
    rwa [hSr] at hpow
  -- Step 2: bound the root by the target expression, factor by factor.
  have hCpow : C ^ r ≤ C := Real.rpow_le_self_of_one_le hC hrle1
  have hNn : (N ^ (n : ℝ)) ^ r = N := by
    have h' := Real.rpow_mul hNnn (n : ℝ) r
    rw [hnr, Real.rpow_one] at h'
    exact h'.symm
  have hNeps : (N ^ ε) ^ r = N ^ (ε * r) := (Real.rpow_mul hNnn ε r).symm
  have hNeps_le : N ^ (ε * r) ≤ N ^ ε :=
    Real.rpow_le_rpow_of_exponent_le hN (mul_le_of_le_one_right hε hrle1)
  have hstep2 : (C * N ^ (n : ℝ) * N ^ ε * B) ^ r ≤ C * N ^ (1 + ε) * B ^ r := by
    calc (C * N ^ (n : ℝ) * N ^ ε * B) ^ r
        = C ^ r * ((N ^ (n : ℝ)) ^ r * (N ^ ε) ^ r) * B ^ r := by
          rw [show C * N ^ (n : ℝ) * N ^ ε * B
                = (C * (N ^ (n : ℝ) * N ^ ε)) * B from by ring]
          rw [Real.mul_rpow (x := C * (N ^ (n : ℝ) * N ^ ε)) (y := B)
                (by positivity) (by positivity)]
          rw [Real.mul_rpow (x := C) (y := N ^ (n : ℝ) * N ^ ε) (by positivity) (by positivity)]
          rw [Real.mul_rpow (x := N ^ (n : ℝ)) (y := N ^ ε) (by positivity) (by positivity)]
      _ ≤ C * (N * N ^ ε) * B ^ r := by
          refine mul_le_mul (mul_le_mul hCpow ?_ (by positivity) (by positivity)) le_rfl
            (by positivity) (by positivity)
          rw [hNn, hNeps]
          exact mul_le_mul_of_nonneg_left hNeps_le hNnn
      _ = C * N ^ (1 + ε) * B ^ r := by
          rw [Real.rpow_add hNpos 1 ε, Real.rpow_one]
  exact le_trans hstep1 hstep2

theorem pow_le_of_rpow_le {k : ℕ} (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) {S C N B : ℝ}
    (hS : 0 ≤ S) (hC : 1 ≤ C) (hN : 1 ≤ N) (hB : 0 < B)
    (h : S ^ (2 ^ k) ≤ C * N ^ ((2 ^ k : ℕ) : ℝ) * N ^ ε * B) :
    S ≤ C * N ^ (1 + ε) * B ^ ((1 : ℝ) / (2 ^ k)) := by
  have hcast : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := Nat.cast_pow 2 k
  rw [← hcast]
  exact rpow_le_of_pow_le_aux (n := 2 ^ k) Nat.one_le_two_pow hε.le hS hC hN hB.le h

end Work.A3.Weil
