import Mathlib

namespace Work.LinnikAreas.TuranOther

/-- Geometric control away from the pole: if `t.re > 1` and `u` lies in the region
`‖t - u‖ ≥ t.re - 1`, then `u` is bounded by a fixed multiple of `‖t - u‖`. -/
theorem norm_le_mul_norm_sub {t u : ℂ} (ht : 1 < t.re)
    (h : t.re - 1 ≤ ‖t - u‖) :
    ‖u‖ ≤ (1 + ‖t‖ / (t.re - 1)) * ‖t - u‖ := by
  have ha : 0 < t.re - 1 := by linarith [ht]
  have hrnn : 0 ≤ ‖t - u‖ := norm_nonneg _
  have hA : ‖u‖ ≤ ‖t‖ + ‖t - u‖ := by
    calc ‖u‖ = ‖(u - t) + t‖ := by rw [sub_add_cancel]
      _ ≤ ‖u - t‖ + ‖t‖ := norm_add_le _ _
      _ = ‖t‖ + ‖t - u‖ := by rw [norm_sub_rev]; ring
  have hB : ‖t‖ ≤ (‖t‖ / (t.re - 1)) * ‖t - u‖ := by
    have hmul : (‖t‖ / (t.re - 1)) * (t.re - 1) ≤ (‖t‖ / (t.re - 1)) * ‖t - u‖ :=
      mul_le_mul_of_nonneg_left h (by positivity)
    rwa [div_mul_cancel₀ (‖t‖) (ne_of_gt ha)] at hmul
  have hcomp : ‖t‖ + ‖t - u‖ ≤ (1 + ‖t‖ / (t.re - 1)) * ‖t - u‖ := by
    nlinarith [hB, hrnn]
  exact le_trans hA hcomp

/-- Polynomial decay bound: for `a > 0`, `r ≥ a` and `k ≥ 1`,
`1 + C² r² ≤ (1/a^{k+1} + C²/a^{k-1}) · r^{k+1}`. -/
theorem one_add_sq_le_mul_pow {k : ℕ} (hk : 1 ≤ k) {a C r : ℝ}
    (ha : 0 < a) (hr : a ≤ r) :
    1 + C ^ 2 * r ^ 2 ≤ (1 / a ^ (k + 1) + C ^ 2 / a ^ (k - 1)) * r ^ (k + 1) := by
  have hra : a ^ (k + 1) ≤ r ^ (k + 1) := pow_le_pow_left₀ (le_of_lt ha) hr _
  have hra' : a ^ (k - 1) ≤ r ^ (k - 1) := pow_le_pow_left₀ (le_of_lt ha) hr _
  have h1 : 1 ≤ (1 / a ^ (k + 1)) * r ^ (k + 1) := by
    have hle : (1 : ℝ) ≤ r ^ (k + 1) / a ^ (k + 1) :=
      (one_le_div (pow_pos ha _)).mpr hra
    rwa [div_eq_mul_one_div, mul_comm] at hle
  have h2 : C ^ 2 * r ^ 2 ≤ (C ^ 2 / a ^ (k - 1)) * r ^ (k + 1) := by
    have hk_eq : k + 1 = 2 + (k - 1) := by omega
    have hcore : r ^ 2 * a ^ (k - 1) ≤ r ^ (k + 1) := by
      rw [hk_eq, pow_add]
      exact mul_le_mul_of_nonneg_left hra' (sq_nonneg _)
    have hdiv : r ^ 2 ≤ r ^ (k + 1) / a ^ (k - 1) :=
      (le_div_iff₀ (pow_pos ha _)).mpr hcore
    calc C ^ 2 * r ^ 2 ≤ C ^ 2 * (r ^ (k + 1) / a ^ (k - 1)) :=
          mul_le_mul_of_nonneg_left hdiv (sq_nonneg C)
      _ = (C ^ 2 / a ^ (k - 1)) * r ^ (k + 1) := by ring
  nlinarith [h1, h2]

/-- The `k`-th term of the Taylor/Turán expansion of the completed ξ-kernel decays
like `1/(1 + ‖u‖²)` on the half-plane `re t > 1`, away from the pole. -/
theorem xiTermKernelDecay (k : ℕ) (hk : 1 ≤ k) {t : ℂ} (ht : 1 < t.re) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : ℂ, t.re - 1 ≤ ‖t - u‖ →
      (1 / ‖t - u‖) ^ (k + 1) ≤ c / (1 + ‖u‖ ^ 2) := by
  have ha : 0 < t.re - 1 := by linarith [ht]
  refine ⟨1 / (t.re - 1) ^ (k + 1)
      + (1 + ‖t‖ / (t.re - 1)) ^ 2 / (t.re - 1) ^ (k - 1), ?_, ?_⟩
  · have h2 : 0 < (t.re - 1) ^ (k - 1) := pow_pos ha _
    have h1 : 0 < (t.re - 1) ^ (k + 1) := pow_pos ha _
    have hpos : 0 < 1 / (t.re - 1) ^ (k + 1) := div_pos one_pos h1
    have hnn : 0 ≤ (1 + ‖t‖ / (t.re - 1)) ^ 2 / (t.re - 1) ^ (k - 1) :=
      div_nonneg (sq_nonneg _) (le_of_lt h2)
    linarith
  · intro u hu
    have hrpos : 0 < ‖t - u‖ := lt_of_lt_of_le ha hu
    have hnorm := norm_le_mul_norm_sub ht hu
    have hsq : ‖u‖ ^ 2 ≤ (1 + ‖t‖ / (t.re - 1)) ^ 2 * ‖t - u‖ ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg u) hnorm 2
      simpa [mul_pow] using this
    have hpow := one_add_sq_le_mul_pow hk (C := 1 + ‖t‖ / (t.re - 1)) ha hu
    have hbound : 1 + ‖u‖ ^ 2 ≤
        (1 / (t.re - 1) ^ (k + 1)
          + (1 + ‖t‖ / (t.re - 1)) ^ 2 / (t.re - 1) ^ (k - 1))
          * ‖t - u‖ ^ (k + 1) := le_trans (by linarith [hsq]) hpow
    rw [one_div_pow]
    rw [div_le_div_iff₀ (pow_pos hrpos _) (by positivity)]
    linarith [hbound]

end Work.LinnikAreas.TuranOther
