import Mathlib

/-!
# The `prog`-clause arithmetic of the `D`-lossy gap case, part I

`ss_gap_i` is the fact `2·D₃ ≤ Pv` used in the second branch of
`Work.Peluse.Ulower.ss_gap_case` (see `NOTES_small_shift_GAP_SESSION.md`): with
`D₃ = δ^{6k}(D/M)^{6k}N₀/(C A'^{3k})` and `Pv = δ^{3k}(D/M)^kM/((c₀A₀)^kA₀C₀)`, the pair
`(N₀ ≤ A'M, A' ≥ 2, (c₀A₀)^kA₀C₀ ≤ C)` suffices.
-/

set_option autoImplicit false

namespace Work.Peluse.Ulower

theorem ss_gap_i {k : ℕ} {c0 C0 A0 D M N0 C A' del : ℝ}
    (hk : 1 ≤ k) (hc00 : 0 < c0) (hA01 : 1 ≤ A0) (hC00 : 0 < C0) (hd0 : 0 < del) (hd1 : del ≤ 1)
    (hD0 : 0 < D) (hDM : D ≤ M) (hM0 : 0 < M) (hN0 : N0 ≤ A' * M) (hA'2 : 2 ≤ A') (hC1 : 0 < C)
    (hi : (c0 * A0) ^ k * A0 * C0 ≤ C) :
    2 * (del ^ (6 * k) * (D / M) ^ (6 * k) * N0 / (C * A' ^ (3 * k)))
      ≤ del ^ (3 * k) * (D / M) ^ k * M / ((c0 * A0) ^ k * A0 * C0) := by
  have hXY : del ^ (6 * k) * (D / M) ^ (6 * k) ≤ del ^ (3 * k) * (D / M) ^ k := by
    have h1 : del ^ (6 * k) ≤ del ^ (3 * k) := pow_le_pow_of_le_one hd0.le hd1 (by omega)
    have h2 : (D / M) ^ (6 * k) ≤ (D / M) ^ k :=
      pow_le_pow_of_le_one (by positivity) ((div_le_one hM0).mpr hDM) (by omega)
    have h3 := mul_le_mul h1 h2 (by positivity) (by positivity)
    simpa using h3
  have hZC : del ^ (6 * k) * (D / M) ^ (6 * k) * ((c0 * A0) ^ k * A0 * C0)
      ≤ del ^ (3 * k) * (D / M) ^ k * C := by
    calc del ^ (6 * k) * (D / M) ^ (6 * k) * ((c0 * A0) ^ k * A0 * C0)
        = (del ^ (6 * k) * (D / M) ^ (6 * k)) * ((c0 * A0) ^ k * A0 * C0) := by ring
      _ ≤ (del ^ (3 * k) * (D / M) ^ k) * ((c0 * A0) ^ k * A0 * C0) :=
          mul_le_mul_of_nonneg_right hXY (by positivity)
      _ ≤ (del ^ (3 * k) * (D / M) ^ k) * C := mul_le_mul_of_nonneg_left hi (by positivity)
      _ = del ^ (3 * k) * (D / M) ^ k * C := by ring
  have hA'3 : 2 * A' ≤ A' ^ (3 * k) := by
    have h1 : (2:ℝ) * A' ≤ A' ^ 2 := by nlinarith [hA'2]
    have h2 : A' ^ 2 ≤ A' ^ (3 * k) := pow_le_pow_right₀ (by linarith) (by omega)
    linarith
  rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
  calc 2 * (del ^ (6 * k) * (D / M) ^ (6 * k) * N0) * ((c0 * A0) ^ k * A0 * C0)
      ≤ 2 * (del ^ (6 * k) * (D / M) ^ (6 * k) * (A' * M)) * ((c0 * A0) ^ k * A0 * C0) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hN0 (by positivity)) (by norm_num)
    _ = (2 * A') * (del ^ (6 * k) * (D / M) ^ (6 * k)) * M * ((c0 * A0) ^ k * A0 * C0) := by ring
    _ ≤ (A' ^ (3 * k)) * (del ^ (6 * k) * (D / M) ^ (6 * k)) * M * ((c0 * A0) ^ k * A0 * C0) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul_of_nonneg_right hA'3 (by positivity)
    _ = A' ^ (3 * k) * M * (del ^ (6 * k) * (D / M) ^ (6 * k) * ((c0 * A0) ^ k * A0 * C0)) := by ring
    _ ≤ A' ^ (3 * k) * M * (del ^ (3 * k) * (D / M) ^ k * C) :=
        mul_le_mul_of_nonneg_left hZC (by positivity)
    _ = (del ^ (3 * k) * (D / M) ^ k * M) * (C * A' ^ (3 * k)) := by ring


/-! ## Part II: the transfer-loss comparison -/

theorem ss_gap_ii {k : ℕ} {c0 C0 A0 D M N C A' del Nprime q : ℝ}
    (hk : 1 ≤ k) (hc00 : 0 < c0) (hA01 : 1 ≤ A0) (hC00 : 0 < C0) (hd0 : 0 < del) (hd1 : del ≤ 1)
    (hD0 : 0 < D) (hDM : D ≤ M) (hM0 : 0 < M) (hN0 : 0 < N) (hA'1 : 1 ≤ A') (hC1 : 0 < C)
    (hNsq : N * N ≤ M)
    (hii : 4 * C0 ^ 2 * (c0 * A0) ^ (2 * k) * A0 ≤ C)
    (hbr : C * A' ^ (3 * k) < del ^ (6 * k) * (D / M) ^ (6 * k) * N)
    (hq : q ≤ C0 * c0 ^ k * A0 ^ k * (del⁻¹) ^ (3 * k) * (M / D) ^ k)
    (hq0 : 0 ≤ q) (hN' : Nprime ≤ N) :
    4 * Nprime * q * ((c0 * A0) ^ k * A0 * C0) ≤ del ^ (3 * k) * (D / M) ^ k * M := by
  have hMDk : (M / D) ^ k = ((D / M) ^ k)⁻¹ := by
    rw [show (M / D) = (D / M)⁻¹ from (inv_div D M).symm]
    exact inv_pow (D / M) k
  have hMD4k : (M / D) ^ (4 * k) = ((D / M) ^ (4 * k))⁻¹ := by
    rw [show (M / D) = (D / M)⁻¹ from (inv_div D M).symm]
    exact inv_pow (D / M) (4 * k)
  have hprodz : (D / M) ^ (4 * k) * (M / D) ^ (4 * k) = 1 := by
    rw [hMD4k, mul_inv_cancel₀ (ne_of_gt (by positivity : (0:ℝ) < (D / M) ^ (4 * k)))]
  have hNid : N * (M / N) = M := by
    rw [mul_comm, div_mul_cancel₀ M (ne_of_gt hN0)]
  set W : ℝ := del ^ (3 * k) * (D / M) ^ k with hWdef
  have hWpos : 0 < W := by rw [hWdef]; positivity
  -- (A) the branch hypothesis
  have hRHS : del ^ (6 * k) * (D / M) ^ (6 * k) * N * ((M / D) ^ (4 * k) * (M / N))
      = W * W * M := by
    have h6 : (D / M) ^ (6 * k) = (D / M) ^ (2 * k) * (D / M) ^ (4 * k) := by
      rw [show 6 * k = 2 * k + 4 * k by ring, pow_add]
    have hWW : W * W = del ^ (6 * k) * (D / M) ^ (2 * k) := by
      rw [hWdef]
      have ha : del ^ (3 * k) * del ^ (3 * k) = del ^ (6 * k) := by rw [← pow_add]; congr 1; ring
      have hb : (D / M) ^ k * (D / M) ^ k = (D / M) ^ (2 * k) := by rw [← pow_add]; congr 1; ring
      calc del ^ (3 * k) * (D / M) ^ k * (del ^ (3 * k) * (D / M) ^ k)
          = (del ^ (3 * k) * del ^ (3 * k)) * ((D / M) ^ k * (D / M) ^ k) := by ring
        _ = del ^ (6 * k) * (D / M) ^ (2 * k) := by rw [ha, hb]
    rw [hWW, h6]
    rw [show del ^ (6 * k) * ((D / M) ^ (2 * k) * (D / M) ^ (4 * k)) * N *
          ((M / D) ^ (4 * k) * (M / N))
        = del ^ (6 * k) * (D / M) ^ (2 * k) * ((D / M) ^ (4 * k) * (M / D) ^ (4 * k)) *
            (N * (M / N)) by ring]
    rw [hprodz, hNid]
    ring
  have hA : C * A' ^ (3 * k) * (M / D) ^ (4 * k) * (M / N) < W * W * M := by
    have h := mul_lt_mul_of_pos_right hbr (by positivity : (0:ℝ) < (M / D) ^ (4 * k) * (M / N))
    have hL : C * A' ^ (3 * k) * ((M / D) ^ (4 * k) * (M / N))
        = C * A' ^ (3 * k) * (M / D) ^ (4 * k) * (M / N) := by ring
    rw [hL] at h
    rw [hRHS] at h
    exact h
  -- (B) the constant comparison
  have hB : 4 * C0 ^ 2 * (c0 * A0) ^ (2 * k) * A0 * N
      ≤ C * A' ^ (3 * k) * (M / D) ^ (4 * k) * (M / N) := by
    have h1 : 4 * C0 ^ 2 * (c0 * A0) ^ (2 * k) * A0 * N ≤ C * N := by
      have h := mul_le_mul_of_nonneg_right hii hN0.le
      have he : 4 * C0 ^ 2 * (c0 * A0) ^ (2 * k) * A0 * N
          = (4 * C0 ^ 2 * (c0 * A0) ^ (2 * k) * A0) * N := by ring
      rw [he]; exact h
    have hA'k : (1:ℝ) ≤ A' ^ (3 * k) := one_le_pow₀ hA'1
    have hMD4 : (1:ℝ) ≤ (M / D) ^ (4 * k) := one_le_pow₀ ((one_le_div hD0).mpr hDM)
    have hMN : N ≤ M / N := by rw [le_div_iff₀ hN0]; exact hNsq
    have h3 : N ≤ A' ^ (3 * k) * (M / D) ^ (4 * k) * (M / N) := by
      calc N ≤ M / N := hMN
        _ = 1 * 1 * (M / N) := by ring
        _ ≤ A' ^ (3 * k) * (M / D) ^ (4 * k) * (M / N) :=
            mul_le_mul_of_nonneg_right (mul_le_mul hA'k hMD4 (by norm_num) (by positivity))
              (by positivity)
    calc 4 * C0 ^ 2 * (c0 * A0) ^ (2 * k) * A0 * N ≤ C * N := h1
      _ ≤ C * (A' ^ (3 * k) * (M / D) ^ (4 * k) * (M / N)) :=
          mul_le_mul_of_nonneg_left h3 (le_of_lt hC1)
      _ = C * A' ^ (3 * k) * (M / D) ^ (4 * k) * (M / N) := by ring
  have hcore : 4 * C0 ^ 2 * (c0 * A0) ^ (2 * k) * A0 * N ≤ W * W * M := le_trans hB (le_of_lt hA)
  -- (C) the algebra
  have hdel : (del⁻¹) ^ (3 * k) = (del ^ (3 * k))⁻¹ := inv_pow del (3 * k)
  have hQZ : (C0 * c0 ^ k * A0 ^ k * (del⁻¹) ^ (3 * k) * (M / D) ^ k) * ((c0 * A0) ^ k * A0 * C0)
      = C0 ^ 2 * (c0 * A0) ^ (2 * k) * A0 * W⁻¹ := by
    rw [hWdef, mul_inv_rev, hdel, hMDk]
    ring
  have h1 : 4 * Nprime * q * ((c0 * A0) ^ k * A0 * C0)
      ≤ 4 * N * (C0 * c0 ^ k * A0 ^ k * (del⁻¹) ^ (3 * k) * (M / D) ^ k) *
          ((c0 * A0) ^ k * A0 * C0) := by
    have h4 : Nprime * q ≤ N * (C0 * c0 ^ k * A0 ^ k * (del⁻¹) ^ (3 * k) * (M / D) ^ k) :=
      mul_le_mul hN' hq hq0 (le_of_lt hN0)
    have h5 := mul_le_mul_of_nonneg_right h4 (by norm_num : (0:ℝ) ≤ 4)
    have h6 := mul_le_mul_of_nonneg_right h5 (by positivity : (0:ℝ) ≤ (c0 * A0) ^ k * A0 * C0)
    linarith [h6]
  refine le_trans h1 ?_
  have heq : 4 * N * (C0 * c0 ^ k * A0 ^ k * (del⁻¹) ^ (3 * k) * (M / D) ^ k) *
        ((c0 * A0) ^ k * A0 * C0) = (4 * C0 ^ 2 * (c0 * A0) ^ (2 * k) * A0 * N) / W := by
    rw [show 4 * N * (C0 * c0 ^ k * A0 ^ k * (del⁻¹) ^ (3 * k) * (M / D) ^ k) *
          ((c0 * A0) ^ k * A0 * C0)
        = 4 * N * ((C0 * c0 ^ k * A0 ^ k * (del⁻¹) ^ (3 * k) * (M / D) ^ k) *
          ((c0 * A0) ^ k * A0 * C0)) by ring, hQZ, div_eq_mul_inv]
    ring
  rw [heq, div_le_iff₀ hWpos]
  rw [show W * M * W = W * W * M by ring]
  exact hcore
end Work.Peluse.Ulower

