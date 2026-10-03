import Mathlib

namespace Work.Peluse.Ulower

/-- Arithmetic bookkeeping for the `ss`-gap: propagating the "one-level" gap inequality
`del ^ 3 / c0 ≤ delc * gac` and the window comparison `Ns ≤ A0 * M` through the `k`-th
power, and converting the `delc, Ns`-normalised progression bound into the `del, M`-normalised
one.  The two shorthands are `delc ^ k * gac ^ k * (D / Ns) ^ k * Ns / C0 ≤ P` (the input)
and `del ^ (3 * k) * (D / M) ^ k * M / ((c0 * A0) ^ k * A0 * C0) ≤ P` (the output); the
comparison factor is `(del ^ 3 / (c0 * delc * gac)) ^ k * (Ns / M) ^ (k - 1) / A0 ^ (k + 1)`,
which is `≤ 1` because `del ^ 3 / c0 ≤ delc * gac`, `Ns ≤ A0 * M`, and `A0 ≥ 1`. -/
theorem ss_gap_Pv_le_prog {k : ℕ} {c0 C0 A0 D M Ns : ℝ} {del delc gac P : ℝ}
    (hk : 1 ≤ k) (hc00 : 0 < c0) (hC00 : 0 < C0) (hA01 : 1 ≤ A0)
    (hdel0 : 0 < del) (hD0 : 0 < D) (hM0 : 0 < M) (hNs0 : 0 < Ns)
    (hlam : del ^ 3 / c0 ≤ delc * gac)
    (hNsle : Ns ≤ A0 * M)
    (hprog : delc ^ k * gac ^ k * (D / Ns) ^ k * Ns / C0 ≤ P) :
    del ^ (3 * k) * (D / M) ^ k * M / ((c0 * A0) ^ k * A0 * C0) ≤ P := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hMne : M ≠ 0 := hM0.ne'
  have hNsne : Ns ≠ 0 := hNs0.ne'
  -- Unfold the one-level gap into a product inequality.
  have hlam' : del ^ 3 ≤ c0 * delc * gac := by
    have h := (div_le_iff₀ hc00).mp hlam
    nlinarith [h]
  have hcg : 0 ≤ c0 * delc * gac := le_trans (pow_pos hdel0 3).le hlam'
  have hdel3 : del ^ (3 * (j + 1)) ≤ (c0 * delc * gac) ^ (j + 1) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) hlam' (j + 1)
  -- Comparison of the window scales `Ns` and `M` (both positive).
  have h1M : (1 : ℝ) / M ≤ A0 / Ns := by
    rw [div_le_div_iff₀ hM0 hNs0]
    simpa using hNsle
  have hDMle : D / M ≤ A0 * (D / Ns) := by
    calc D / M = D * (1 / M) := by ring
      _ ≤ D * (A0 / Ns) := mul_le_mul_of_nonneg_left h1M hD0.le
      _ = A0 * (D / Ns) := by ring
  have hp : (D / M) ^ j ≤ A0 ^ (j + 1) * A0 * (D / Ns) ^ j := by
    calc (D / M) ^ j ≤ (A0 * (D / Ns)) ^ j := pow_le_pow_left₀ (by positivity) hDMle j
      _ = A0 ^ j * (D / Ns) ^ j := by rw [mul_pow]
      _ ≤ A0 ^ (j + 1) * A0 * (D / Ns) ^ j := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          calc A0 ^ j ≤ A0 ^ (j + 1) := pow_le_pow_right₀ hA01 (by omega)
            _ ≤ A0 ^ (j + 1) * A0 := le_mul_of_one_le_right (by positivity) hA01
  have hDM2 : (D / M) ^ (j + 1) * M ≤ (D / Ns) ^ (j + 1) * Ns * (A0 ^ (j + 1) * A0) := by
    have hl : (D / M) ^ (j + 1) * M = (D / M) ^ j * D := by
      rw [pow_succ]
      rw [mul_assoc, div_mul_cancel₀ D hMne]
    have hr : (D / Ns) ^ (j + 1) * Ns = (D / Ns) ^ j * D := by
      rw [pow_succ]
      rw [mul_assoc, div_mul_cancel₀ D hNsne]
    rw [hl, hr]
    calc (D / M) ^ j * D ≤ (A0 ^ (j + 1) * A0 * (D / Ns) ^ j) * D :=
          mul_le_mul_of_nonneg_right hp hD0.le
      _ = (D / Ns) ^ j * D * (A0 ^ (j + 1) * A0) := by ring
  -- The cross-multiplied comparison of the two normalisations.
  have hfin : del ^ (3 * (j + 1)) * (D / M) ^ (j + 1) * M
      ≤ delc ^ (j + 1) * gac ^ (j + 1) * (D / Ns) ^ (j + 1) * Ns
          * ((c0 * A0) ^ (j + 1) * A0) := by
    have hstep1 : del ^ (3 * (j + 1)) * ((D / M) ^ (j + 1) * M)
        ≤ (c0 * delc * gac) ^ (j + 1)
            * ((D / Ns) ^ (j + 1) * Ns * (A0 ^ (j + 1) * A0)) :=
      mul_le_mul hdel3 hDM2 (by positivity) (pow_nonneg hcg _)
    calc del ^ (3 * (j + 1)) * (D / M) ^ (j + 1) * M
        = del ^ (3 * (j + 1)) * ((D / M) ^ (j + 1) * M) := by ring
      _ ≤ (c0 * delc * gac) ^ (j + 1)
            * ((D / Ns) ^ (j + 1) * Ns * (A0 ^ (j + 1) * A0)) := hstep1
      _ = delc ^ (j + 1) * gac ^ (j + 1) * (D / Ns) ^ (j + 1) * Ns
            * ((c0 * A0) ^ (j + 1) * A0) := by
          rw [mul_pow, mul_pow]
          ring
  have hmain : del ^ (3 * (j + 1)) * (D / M) ^ (j + 1) * M / ((c0 * A0) ^ (j + 1) * A0 * C0)
      ≤ delc ^ (j + 1) * gac ^ (j + 1) * (D / Ns) ^ (j + 1) * Ns / C0 := by
    rw [div_le_div_iff₀ (by positivity) hC00]
    have h := mul_le_mul_of_nonneg_right hfin hC00.le
    simpa only [mul_assoc] using h
  exact le_trans hmain hprog

end Work.Peluse.Ulower
