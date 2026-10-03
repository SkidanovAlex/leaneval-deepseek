import Mathlib

/-!
# The `N'`-clause arithmetic of the `D`-lossy gap case (pure real arithmetic).

See `NOTES_small_shift_GAP_SESSION.md`.
-/

set_option autoImplicit false

namespace Work.Peluse.Ulower

theorem ss_gap_N'_arith {k : ℕ} {c0 C0 A0 D M Ns del delc gac A' N C N' : ℝ}
    (hc00 : 0 < c0) (hd0 : 0 < del) (hd1 : del ≤ 1) (hD0 : 0 < D) (hDM : D ≤ M) (hM0 : 0 < M)
    (hNs0 : 0 < Ns) (hNsM : Ns ≤ A0 * M) (hA00 : 0 < A0) (hA'1 : 1 ≤ A')
    (hC0 : 0 < C0) (hdelc0 : 0 < delc) (hgac0 : 0 < gac) (hN0 : 0 < N)
    (hC1 : 0 < C)
    (hC : C0 * c0 ^ k * A0 ^ k ≤ C) (hlam : del ^ 3 / c0 ≤ delc * gac)
    (hN' : delc ^ k * gac ^ k * (D / Ns) ^ k * N / C0 ≤ N') :
    del ^ (6 * k) * (D / M) ^ (6 * k) * N / (C * A' ^ (3 * k)) ≤ N' := by
  have hd3c0 : 0 < del ^ 3 / c0 := by positivity
  have h1 : (del ^ 3 / c0) ^ k ≤ delc ^ k * gac ^ k := by
    have := pow_le_pow_left₀ (by positivity) hlam k
    rwa [mul_pow] at this
  have hDN : D / (A0 * M) ≤ D / Ns := by
    refine div_le_div_of_nonneg_left hD0.le (by positivity) ?_
    exact hNsM
  have h2 : (D / (A0 * M)) ^ k ≤ (D / Ns) ^ k := pow_le_pow_left₀ (by positivity) hDN k
  have hstep : del ^ (3 * k) * (D / M) ^ k * N / (c0 ^ k * A0 ^ k * C0) ≤ N' := by
    refine le_trans ?_ hN'
    have heq : (del ^ 3 / c0) ^ k * (D / (A0 * M)) ^ k * N / C0
        = del ^ (3 * k) * (D / M) ^ k * N / (c0 ^ k * A0 ^ k * C0) := by
      rw [div_pow, div_pow, mul_pow, div_pow]
      rw [← pow_mul]
      ring
    rw [← heq]
    have h3 : (del ^ 3 / c0) ^ k * (D / (A0 * M)) ^ k ≤ delc ^ k * gac ^ k * (D / Ns) ^ k :=
      mul_le_mul h1 h2 (by positivity) (by positivity)
    have h4 : (del ^ 3 / c0) ^ k * (D / (A0 * M)) ^ k * N
        ≤ delc ^ k * gac ^ k * (D / Ns) ^ k * N :=
      mul_le_mul_of_nonneg_right h3 (le_of_lt hN0)
    exact div_le_div_of_nonneg_right h4 (le_of_lt hC0)
  refine le_trans ?_ hstep
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hA'k : 1 ≤ A' ^ (3 * k) := one_le_pow₀ hA'1
  have hDM1 : D / M ≤ 1 := (div_le_one hM0).mpr hDM
  have hd3 : del ^ (3 * k) ≤ 1 := pow_le_one₀ hd0.le hd1
  have hdm5 : (D / M) ^ (5 * k) ≤ 1 := pow_le_one₀ (by positivity) hDM1
  have hX1 : del ^ (3 * k) * (D / M) ^ (5 * k) ≤ 1 := by
    have := mul_le_mul hd3 hdm5 (by positivity) (by positivity)
    simpa using this
  have hX : del ^ (3 * k) * (D / M) ^ (5 * k) * (c0 ^ k * A0 ^ k * C0) ≤ C := by
    calc del ^ (3 * k) * (D / M) ^ (5 * k) * (c0 ^ k * A0 ^ k * C0)
        ≤ 1 * (c0 ^ k * A0 ^ k * C0) := mul_le_mul_of_nonneg_right hX1 (by positivity)
      _ = c0 ^ k * A0 ^ k * C0 := one_mul _
      _ = C0 * c0 ^ k * A0 ^ k := by ring
      _ ≤ C := hC
  have hX2 : del ^ (3 * k) * (D / M) ^ (5 * k) * (c0 ^ k * A0 ^ k * C0) ≤ C * A' ^ (3 * k) := by
    calc del ^ (3 * k) * (D / M) ^ (5 * k) * (c0 ^ k * A0 ^ k * C0) ≤ C := hX
      _ = C * 1 := (mul_one C).symm
      _ ≤ C * A' ^ (3 * k) := mul_le_mul_of_nonneg_left hA'k (le_of_lt hC1)
  have hp1 : del ^ (6 * k) = del ^ (3 * k) * del ^ (3 * k) := by
    rw [show 6 * k = 3 * k + 3 * k by ring, pow_add]
  have hp2 : (D / M) ^ (6 * k) = (D / M) ^ k * (D / M) ^ (5 * k) := by
    rw [show 6 * k = k + 5 * k by ring, pow_add]
  calc del ^ (6 * k) * (D / M) ^ (6 * k) * N * (c0 ^ k * A0 ^ k * C0)
      = (del ^ (3 * k) * (D / M) ^ k * N) *
          (del ^ (3 * k) * (D / M) ^ (5 * k) * (c0 ^ k * A0 ^ k * C0)) := by
        rw [hp1, hp2]
        ring
    _ ≤ (del ^ (3 * k) * (D / M) ^ k * N) * (C * A' ^ (3 * k)) :=
        mul_le_mul_of_nonneg_left hX2 (by positivity)

end Work.Peluse.Ulower
