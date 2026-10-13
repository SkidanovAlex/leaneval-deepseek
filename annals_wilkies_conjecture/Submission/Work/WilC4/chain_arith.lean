import Mathlib

namespace Work.WilC4

/-- Elementary bound: for `t ≥ 1/2`, `|log t| ≤ 2 |t - 1|`.
(For `t ≥ 1` this is `log t ≤ t - 1`; for `1/2 ≤ t < 1` it follows from
`log (1/t) ≤ 1/t - 1` together with `1/t ≤ 2`.) -/
lemma abs_log_le_two_mul_abs_sub_one {t : ℝ} (ht : 1 / 2 ≤ t) :
    |Real.log t| ≤ 2 * |t - 1| := by
  have ht0 : 0 < t := by linarith
  rcases lt_or_ge t 1 with h | h
  · have hlog : Real.log t ≤ 0 := Real.log_nonpos ht0.le h.le
    rw [abs_of_nonpos hlog, abs_of_nonpos (by linarith : t - 1 ≤ 0)]
    have h4 : 1 / t - 1 ≤ 2 * (1 - t) := by
      rw [div_sub_one ht0.ne', div_le_iff₀ ht0]
      nlinarith
    have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 / t by positivity)
    rw [Real.log_div one_ne_zero ht0.ne', Real.log_one] at h2
    simp only [zero_sub] at h2
    linarith
  · rw [abs_of_nonneg (Real.log_nonneg h), abs_of_nonneg (by linarith : 0 ≤ t - 1)]
    have := Real.log_le_sub_one_of_pos ht0
    linarith

/-- Passing between a multiplicative inequality and a logarithmic one:
if `|log A - log B| ≤ log N` with `A, B, N > 0`, then `A ≤ N * B` and `B ≤ N * A`. -/
lemma le_mul_of_abs_log_sub_le {A B N : ℝ} (hA : 0 < A) (hB : 0 < B) (hN : 0 < N)
    (h : |Real.log A - Real.log B| ≤ Real.log N) : A ≤ N * B ∧ B ≤ N * A := by
  have hAB : 0 < A / B := div_pos hA hB
  have hBA : 0 < B / A := div_pos hB hA
  have hlogAB : Real.log (A / B) = Real.log A - Real.log B := Real.log_div hA.ne' hB.ne'
  have hlogBA : Real.log (B / A) = Real.log B - Real.log A := Real.log_div hB.ne' hA.ne'
  rw [abs_le] at h
  constructor
  · have h1 : Real.log (A / B) ≤ Real.log N := by rw [hlogAB]; exact h.2
    have h2 := (Real.log_le_log_iff hAB hN).mp h1
    rwa [div_le_iff₀ hB] at h2
  · have h1 : Real.log (B / A) ≤ Real.log N := by rw [hlogBA]; linarith [h.1]
    have h2 := (Real.log_le_log_iff hBA hN).mp h1
    rwa [div_le_iff₀ hA] at h2

theorem chain_arith {q : ℚ} {K : ℕ} {w ε : Fin K → ℝ}
    {y₁ y₂ L x₁ x₂ N : ℝ} (hy₁ : y₁ ≠ 0) (hL : L ≠ 0) (hx₁ : 0 < x₁) (hx₂ : 0 < x₂)
    (hN : 1 ≤ N)
    (hε0 : ∀ k, 0 ≤ ε k) (hε2 : ∀ k, ε k ≤ 1 / 2)
    (hw : ∀ k, |w k / (2 : ℝ) ^ (q : ℝ) - 1| ≤ ε k)
    (hKle : Real.logb 2 (x₂ / x₁) ≤ (K : ℝ))
    (hKlt : (K : ℝ) ≤ Real.logb 2 (x₂ / x₁) + 1)
    (hkey : 4 * (∑ k, ε k) + |Real.logb 2 L| + |(q : ℝ)| ≤ Real.logb 2 N)
    (hy : y₂ = y₁ * (∏ k, w k) * L) :
    |y₂| * x₁ ^ (q : ℝ) ≤ N * (|y₁| * x₂ ^ (q : ℝ)) ∧
    |y₁| * x₂ ^ (q : ℝ) ≤ N * (|y₂| * x₁ ^ (q : ℝ)) := by
  -- `log 2 > 0`, and the basic rpow bookkeeping.
  have hc_pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hb : (0:ℝ) < (2:ℝ)^(q:ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have hlogb : Real.log ((2:ℝ)^(q:ℝ)) = (q:ℝ) * Real.log 2 := Real.log_rpow (by norm_num) _
  have hxp₁ : (0:ℝ) < x₁ ^ (q:ℝ) := Real.rpow_pos_of_pos hx₁ _
  have hxp₂ : (0:ℝ) < x₂ ^ (q:ℝ) := Real.rpow_pos_of_pos hx₂ _
  -- The normalised factors `u k = w k / 2^q`.
  obtain ⟨u, hu⟩ : ∃ u : Fin K → ℝ, ∀ k, u k = w k / (2:ℝ)^(q:ℝ) :=
    ⟨fun k => w k / (2:ℝ)^(q:ℝ), fun k => rfl⟩
  have hu_le : ∀ k, |u k - 1| ≤ ε k := fun k => by rw [hu k]; exact hw k
  have hu_half : ∀ k, (1/2:ℝ) ≤ u k := by
    intro k
    have h := (abs_le.mp (hu_le k)).1
    have := hε2 k
    linarith
  have hu_pos : ∀ k, 0 < u k := fun k => by linarith [hu_half k]
  have hu_ne : ∀ k, u k ≠ 0 := fun k => (hu_pos k).ne'
  have hw_eq : ∀ k, w k = u k * (2:ℝ)^(q:ℝ) := by
    intro k
    rw [hu k, div_mul_cancel₀ _ hb.ne']
  have hw_ne : ∀ k, w k ≠ 0 := fun k => by rw [hw_eq k]; exact mul_ne_zero (hu_ne k) hb.ne'
  have hP_ne : (∏ k, w k) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun k _ => hw_ne k)
  have hy₂ : y₂ ≠ 0 := by rw [hy]; exact mul_ne_zero (mul_ne_zero hy₁ hP_ne) hL
  -- Logarithm of the product of the `w k`.
  have hlogP : Real.log (∏ k, w k) = (∑ k, Real.log (u k)) + (K:ℝ) * ((q:ℝ) * Real.log 2) := by
    rw [Real.log_prod (fun k _ => hw_ne k)]
    have h1 : ∀ k : Fin K, Real.log (w k) = Real.log (u k) + Real.log ((2:ℝ)^(q:ℝ)) := by
      intro k
      rw [hw_eq k, Real.log_mul (hu_ne k) hb.ne']
    rw [Finset.sum_congr rfl (fun k _ => h1 k), Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hlogb]
  -- The "remainder" `r` measuring how far `logb 2 (x₂/x₁)` is below `K`.
  have hx2x1 : Real.log (x₂ / x₁) = Real.log x₂ - Real.log x₁ := Real.log_div hx₂.ne' hx₁.ne'
  have hKle' : Real.log (x₂ / x₁) ≤ (K:ℝ) * Real.log 2 := by
    rw [Real.logb] at hKle
    rw [div_le_iff₀ hc_pos] at hKle
    exact hKle
  have hKlt' : (K:ℝ) * Real.log 2 ≤ Real.log (x₂ / x₁) + Real.log 2 := by
    rw [Real.logb] at hKlt
    have h : ((K:ℝ) - 1) ≤ Real.log (x₂ / x₁) / Real.log 2 := by linarith
    rw [le_div_iff₀ hc_pos] at h
    linarith
  obtain ⟨r, hr_def⟩ : ∃ r : ℝ, r = (K:ℝ) * Real.log 2 - Real.log (x₂ / x₁) := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := by rw [hr_def]; linarith [hKle']
  have hrc : r ≤ Real.log 2 := by rw [hr_def]; linarith [hKlt']
  -- Logarithmic expansions of the two sides.
  have hA : Real.log (|y₂| * x₁ ^ (q:ℝ)) = Real.log |y₂| + (q:ℝ) * Real.log x₁ := by
    rw [Real.log_mul (abs_ne_zero.mpr hy₂) hxp₁.ne', Real.log_rpow hx₁]
  have hB : Real.log (|y₁| * x₂ ^ (q:ℝ)) = Real.log |y₁| + (q:ℝ) * Real.log x₂ := by
    rw [Real.log_mul (abs_ne_zero.mpr hy₁) hxp₂.ne', Real.log_rpow hx₂]
  have hlogy2 : Real.log |y₂| = Real.log |y₁| + Real.log (∏ k, w k) + Real.log L := by
    calc Real.log |y₂| = Real.log (y₁ * (∏ k, w k) * L) := by rw [hy, Real.log_abs]
      _ = Real.log (y₁ * (∏ k, w k)) + Real.log L := by
            rw [Real.log_mul (mul_ne_zero hy₁ hP_ne) hL]
      _ = (Real.log y₁ + Real.log (∏ k, w k)) + Real.log L := by rw [Real.log_mul hy₁ hP_ne]
      _ = Real.log |y₁| + Real.log (∏ k, w k) + Real.log L := by rw [Real.log_abs y₁]
  -- The key identity: the log-ratio is `∑ log (u k) + log L + q r`.
  have hE : Real.log (|y₂| * x₁ ^ (q:ℝ)) - Real.log (|y₁| * x₂ ^ (q:ℝ))
      = (∑ k, Real.log (u k)) + Real.log L + (q:ℝ) * r := by
    rw [hA, hB, hlogy2, hlogP, hr_def, hx2x1]
    ring
  -- Bound on the sum of the logarithms of the `u k`.
  have hsum_le : |∑ k, Real.log (u k)| ≤ 2 * (∑ k, ε k) := by
    have h1 : |∑ k, Real.log (u k)| ≤ ∑ k, |Real.log (u k)| :=
      Finset.abs_sum_le_sum_abs (fun k => Real.log (u k)) Finset.univ
    have h2 : ∑ k, |Real.log (u k)| ≤ ∑ k, 2 * ε k := by
      apply Finset.sum_le_sum
      intro k _
      have h3 : |Real.log (u k)| ≤ 2 * |u k - 1| := abs_log_le_two_mul_abs_sub_one (hu_half k)
      have h4 : 2 * |u k - 1| ≤ 2 * ε k := mul_le_mul_of_nonneg_left (hu_le k) (by norm_num)
      linarith
    have h5 : ∑ k, 2 * ε k = 2 * (∑ k, ε k) := by rw [Finset.mul_sum]
    calc |∑ k, Real.log (u k)| ≤ ∑ k, |Real.log (u k)| := h1
      _ ≤ ∑ k, 2 * ε k := h2
      _ = 2 * (∑ k, ε k) := h5
  -- Translate the key hypothesis into a `log N` bound (multiply by `log 2`).
  have hkey' : 4 * (∑ k, ε k) * Real.log 2 + |Real.log L| + |(q:ℝ)| * Real.log 2 ≤ Real.log N := by
    have h1 : |Real.logb 2 L| * Real.log 2 = |Real.log L| := by
      rw [← abs_of_nonneg hc_pos.le, ← abs_mul, Real.logb, div_mul_cancel₀ _ hc_pos.ne']
    have hN1 : Real.logb 2 N * Real.log 2 = Real.log N := by
      rw [Real.logb, div_mul_cancel₀ _ hc_pos.ne']
    have h := mul_le_mul_of_nonneg_right hkey hc_pos.le
    rw [hN1, add_mul, add_mul, h1] at h
    linarith [h]
  have hS_nn : 0 ≤ ∑ k, ε k := Finset.sum_nonneg (fun k _ => hε0 k)
  -- We have slack: `2 ∑ ε k ≤ 4 (log 2) ∑ ε k` since `log 2 ≥ 1/2` and `∑ ε k ≥ 0`.
  have h2S : 2 * (∑ k, ε k) ≤ 4 * (∑ k, ε k) * Real.log 2 := by
    have hcoef : (2:ℝ) ≤ 4 * Real.log 2 := by linarith [Real.log_two_gt_d9]
    have h := mul_le_mul_of_nonneg_right hcoef hS_nn
    nlinarith [h]
  -- Assemble: the log-ratio is bounded by `log N`.
  have hfinal : |Real.log (|y₂| * x₁ ^ (q:ℝ)) - Real.log (|y₁| * x₂ ^ (q:ℝ))| ≤ Real.log N := by
    rw [hE]
    have h1 : |(∑ k, Real.log (u k)) + Real.log L + (q:ℝ) * r| ≤
        |∑ k, Real.log (u k)| + |Real.log L| + |(q:ℝ) * r| := by
      have a := abs_add_le ((∑ k, Real.log (u k)) + Real.log L) ((q:ℝ) * r)
      have b := abs_add_le (∑ k, Real.log (u k)) (Real.log L)
      linarith
    have h2 : |∑ k, Real.log (u k)| + |Real.log L| + |(q:ℝ) * r| ≤
        2 * (∑ k, ε k) + |Real.log L| + |(q:ℝ)| * Real.log 2 := by
      have h3 : |(q:ℝ) * r| ≤ |(q:ℝ)| * Real.log 2 := by
        rw [abs_mul, abs_of_nonneg hr0]
        exact mul_le_mul_of_nonneg_left hrc (abs_nonneg _)
      linarith [hsum_le, h3]
    linarith [h1, h2, h2S, hkey']
  -- Conclude both multiplicative inequalities.
  exact le_mul_of_abs_log_sub_le (mul_pos (abs_pos.mpr hy₂) hxp₁)
    (mul_pos (abs_pos.mpr hy₁) hxp₂) (by linarith) hfinal

end Work.WilC4
