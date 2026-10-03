import Mathlib

namespace Work.Analysis.SingleScale

/-- A lacunary (geometrically growing) sequence `a` of nonnegative reals with ratio `Λ > 1`,
starting at `a 0 ≥ 1`, has `∑_{n < K} (max 1 (logb 2 (a n))) ^ (-c)` bounded uniformly in `K`
whenever `c > 1`.

This is the summability input for the single-scale (lacunary) part of the
pointwise ergodic theorem: the `n`-th summand decays like `(n log Λ) ^ (-c)`. -/
theorem lacunary_logb_rpow_summable (Λ : NNReal) (hΛ : 1 < Λ) (c : ℝ) (hc : 1 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → NNReal) (K : ℕ), (∀ n, Λ * a n ≤ a (n + 1)) → 1 ≤ a 0 →
      ∑ n ∈ Finset.range K, (max 1 (Real.logb 2 (a n : ℝ))) ^ (-c) ≤ C := by
  -- `lam = logb 2 Λ > 0`
  set lam : ℝ := Real.logb 2 (Λ : ℝ) with hlam
  have hΛ1 : (1 : ℝ) < (Λ : ℝ) := by exact_mod_cast hΛ
  have hlampos : 0 < lam := by rw [hlam]; exact Real.logb_pos (by norm_num) hΛ1
  have hnegc : -c < 0 := by linarith
  -- summability of the `p`-series `∑ n ^ (-c)`, `c > 1`
  have hsumm : Summable (fun n : ℕ => (n : ℝ) ^ (-c)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have htsum_nn : 0 ≤ ∑' n : ℕ, (n : ℝ) ^ (-c) :=
    tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _
  refine ⟨1 + lam ^ (-c) * (∑' n : ℕ, (n : ℝ) ^ (-c)), ?_, ?_⟩
  · have h1 : 0 < lam ^ (-c) := Real.rpow_pos_of_pos hlampos _
    have h2 : 0 ≤ lam ^ (-c) * (∑' n : ℕ, (n : ℝ) ^ (-c)) := mul_nonneg h1.le htsum_nn
    linarith
  · intro a K hrec ha0
    -- `x ↦ (max 1 x) ^ (-c)` is antitone
    have hmono : ∀ {M L : ℝ}, M ≤ L → (max 1 L) ^ (-c) ≤ (max 1 M) ^ (-c) := by
      intro M L hML
      exact (Real.rpow_le_rpow_iff_of_neg
        (lt_of_lt_of_le zero_lt_one (le_max_left 1 L))
        (lt_of_lt_of_le zero_lt_one (le_max_left 1 M))
        hnegc).mpr (max_le_max le_rfl hML)
    -- geometric growth: `Λ ^ n ≤ a n`
    have growth : ∀ n : ℕ, Λ ^ n ≤ a n := by
      intro n
      induction n with
      | zero => simpa using ha0
      | succ n ih =>
          calc Λ ^ (n + 1) = Λ * Λ ^ n := pow_succ' Λ n
            _ ≤ Λ * a n := mul_le_mul_of_nonneg_left ih bot_le
            _ ≤ a (n + 1) := hrec n
    -- logarithmic growth: `n * logb 2 Λ ≤ logb 2 (a n)`
    have keylog : ∀ n : ℕ, (n : ℝ) * lam ≤ Real.logb 2 (a n : ℝ) := by
      intro n
      have h1 : ((Λ ^ n : NNReal) : ℝ) ≤ ((a n : NNReal) : ℝ) := by exact_mod_cast growth n
      rw [NNReal.coe_pow] at h1
      have h2 : Real.logb 2 ((Λ : ℝ) ^ n) ≤ Real.logb 2 ((a n : ℝ)) :=
        Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
          (pow_pos (by linarith : (0 : ℝ) < (Λ : ℝ)) n) h1
      rw [Real.logb_pow] at h2
      rwa [← hlam] at h2
    have hterm : ∀ n : ℕ,
        (max 1 (Real.logb 2 (a n : ℝ))) ^ (-c) ≤ (max 1 ((n : ℝ) * lam)) ^ (-c) :=
      fun n => hmono (keylog n)
    -- the `n = 0` term contributes at most `1`
    have hsum0 : ∑ n ∈ (Finset.range K).filter (fun n => n = 0),
        (max 1 (Real.logb 2 (a n : ℝ))) ^ (-c) ≤ 1 := by
      calc ∑ n ∈ (Finset.range K).filter (fun n => n = 0),
              (max 1 (Real.logb 2 (a n : ℝ))) ^ (-c)
          ≤ ∑ _n ∈ (Finset.range K).filter (fun n => n = 0), (1 : ℝ) :=
            Finset.sum_le_sum (fun n _ =>
              Real.rpow_le_one_of_one_le_of_nonpos (le_max_left 1 _) (by linarith))
        _ = ((Finset.range K).filter (fun n => n = 0)).card := by simp
        _ ≤ 1 := by
            have hsub : (Finset.range K).filter (fun n => n = 0) ⊆ ({0} : Finset ℕ) := by
              intro x hx
              simp only [Finset.mem_filter, Finset.mem_singleton] at hx ⊢
              exact hx.2
            have hcard : ((Finset.range K).filter (fun n => n = 0)).card ≤ 1 := by
              simpa using Finset.card_le_card hsub
            exact_mod_cast hcard
    -- the `n ≥ 1` terms are dominated by the `p`-series
    have hsum1 : ∑ n ∈ (Finset.range K).filter (fun n => ¬ (n = 0)),
        (max 1 (Real.logb 2 (a n : ℝ))) ^ (-c) ≤ lam ^ (-c) * (∑' n : ℕ, (n : ℝ) ^ (-c)) := by
      have hstep : ∀ n ∈ (Finset.range K).filter (fun n => ¬ (n = 0)),
          (max 1 (Real.logb 2 (a n : ℝ))) ^ (-c) ≤ lam ^ (-c) * (n : ℝ) ^ (-c) := by
        intro n hn
        have hn0 : n ≠ 0 := (Finset.mem_filter.mp hn).2
        have hnpos : 0 < (n : ℝ) * lam :=
          mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hn0) hlampos
        have h1 : (max 1 ((n : ℝ) * lam)) ^ (-c) ≤ ((n : ℝ) * lam) ^ (-c) :=
          (Real.rpow_le_rpow_iff_of_neg
            (lt_of_lt_of_le zero_lt_one (le_max_left 1 ((n : ℝ) * lam)))
            hnpos hnegc).mpr (le_max_right 1 _)
        calc (max 1 (Real.logb 2 (a n : ℝ))) ^ (-c)
            ≤ (max 1 ((n : ℝ) * lam)) ^ (-c) := hterm n
          _ ≤ ((n : ℝ) * lam) ^ (-c) := h1
          _ = lam ^ (-c) * (n : ℝ) ^ (-c) := by
              rw [Real.mul_rpow (x := (n : ℝ)) (y := lam) (Nat.cast_nonneg n) hlampos.le, mul_comm]
      calc ∑ n ∈ (Finset.range K).filter (fun n => ¬ (n = 0)),
              (max 1 (Real.logb 2 (a n : ℝ))) ^ (-c)
          ≤ ∑ n ∈ (Finset.range K).filter (fun n => ¬ (n = 0)),
              lam ^ (-c) * (n : ℝ) ^ (-c) :=
            Finset.sum_le_sum hstep
        _ = lam ^ (-c) * ∑ n ∈ (Finset.range K).filter (fun n => ¬ (n = 0)), (n : ℝ) ^ (-c) :=
            (Finset.mul_sum _ _ _).symm
        _ ≤ lam ^ (-c) * ∑' n : ℕ, (n : ℝ) ^ (-c) :=
            mul_le_mul_of_nonneg_left
              (Summable.sum_le_tsum _ (fun i _ => Real.rpow_nonneg (Nat.cast_nonneg i) _) hsumm)
              (Real.rpow_pos_of_pos hlampos _).le
    calc ∑ n ∈ Finset.range K, (max 1 (Real.logb 2 (a n : ℝ))) ^ (-c)
        = ∑ n ∈ (Finset.range K).filter (fun n => n = 0),
            (max 1 (Real.logb 2 (a n : ℝ))) ^ (-c)
          + ∑ n ∈ (Finset.range K).filter (fun n => ¬ (n = 0)),
            (max 1 (Real.logb 2 (a n : ℝ))) ^ (-c) :=
            (Finset.sum_filter_add_sum_filter_not (Finset.range K) (fun n => n = 0) _).symm
      _ ≤ 1 + lam ^ (-c) * (∑' n : ℕ, (n : ℝ) ^ (-c)) := add_le_add hsum0 hsum1

end Work.Analysis.SingleScale
