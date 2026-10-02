/-
# `‖B_c z‖ ≤ (‖c‖² + 3‖c‖ + 1)/‖z‖²` far out

The Böttcher series `B_c z = Σ_n 4^{-(n+1)} log (p_c^n z / (p_c^n z)^4)` is
`O(1/‖z‖²)`.  The point of this file is a *quantitative* form with the small
constant `‖c‖² + 3‖c‖ + 1` and the explicit radius `64 (1 + ‖c‖) + 64`.

The estimate is obtained exactly as in `Core.norm_bottcherSeries_le`, but keeping
the factor `Σ_n 4^{-(n+1)} = 1/3` instead of discarding it: the crude bound
`(3/2)(‖c‖²+3‖c‖)/‖z‖²` becomes `(1/2)(‖c‖²+3‖c‖)/‖z‖²`, which is below
`(‖c‖²+3‖c‖+1)/‖z‖²`.

The only genuinely new input is that the explicit radius `64(1+‖c‖)+64` (which is
*much* smaller than `Core.normRadius c` when `‖c‖` is large, or rather grows only
linearly in `‖c‖`) still forces the `p_c`-orbit to be monotonically increasing in
norm: on `{‖w‖ ≥ 64(1+‖c‖)+64}` one has `(3/4)‖w‖⁴ ≤ ‖p_c w‖`, hence
`‖w‖ ≤ ‖p_c w‖`.  Consequently `‖z‖ ≤ ‖p_c^n z‖` for all `n ≥ 0`, which is all
that is needed to replace `‖z_n‖` by `‖z‖` in the terms of the series.
-/
import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Bottcher.Core.analyticAt_bottcher
import Submission.Work.Bottcher.Core.bottcher_tendsto_atTop
import Submission.Work.Bottcher.Core.norm_iterate_pMap_ge

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Bottcher.Inverse

/-! ## The `p_c`-orbit grows in norm on the far region -/

/-- On `{‖w‖ ≥ 64(1+‖c‖)+64}` the monic quartic `p_c w = w⁴ + 2 c̄ w² + c̄² + c`
dominates its perturbation term: `(3/4)‖w‖⁴ ≤ ‖p_c w‖`. -/
private lemma three_quarters_pow_four_le_norm_pMap (c w : ℂ)
    (hw : 64 * (1 + ‖c‖) + 64 ≤ ‖w‖) :
    (3 / 4) * ‖w‖ ^ 4 ≤ ‖Work.Bottcher.pMap c w‖ := by
  have hj0 : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  have hw0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  have h64 : 64 * ‖c‖ ≤ ‖w‖ := by linarith
  have hw2 : (2 : ℝ) ≤ ‖w‖ := by linarith
  have hw1 : (1 : ℝ) ≤ ‖w‖ := by linarith
  -- The perturbation `2 c̄ w² + c̄² + c`.
  have hpert : ‖2 * (starRingEnd ℂ c) * w ^ 2 + (starRingEnd ℂ c) ^ 2 + c‖
      ≤ 2 * ‖c‖ * ‖w‖ ^ 2 + ‖c‖ ^ 2 + ‖c‖ := by
    have h1' := norm_add_le (2 * (starRingEnd ℂ c) * w ^ 2 + (starRingEnd ℂ c) ^ 2) c
    have h2' := norm_add_le (2 * (starRingEnd ℂ c) * w ^ 2) ((starRingEnd ℂ c) ^ 2)
    have hrw : ‖2 * (starRingEnd ℂ c) * w ^ 2‖ + ‖(starRingEnd ℂ c) ^ 2‖
        = 2 * ‖c‖ * ‖w‖ ^ 2 + ‖c‖ ^ 2 := by
      simp only [norm_mul, Complex.norm_conj, norm_pow, Complex.norm_ofNat]
    linarith
  -- Numerically the perturbation is at most `(1/4)‖w‖⁴`.
  have hjle : ‖c‖ ≤ ‖w‖ / 64 := by linarith
  have hnum : 2 * ‖c‖ * ‖w‖ ^ 2 + ‖c‖ ^ 2 + ‖c‖ ≤ (1 / 4) * ‖w‖ ^ 4 := by
    have h2j : 2 * ‖c‖ * ‖w‖ ^ 2 ≤ (1 / 12 : ℝ) * ‖w‖ ^ 4 := by
      have h1 : 2 * ‖c‖ ≤ 2 * (‖w‖ / 64) :=
        mul_le_mul_of_nonneg_left hjle (by norm_num : (0 : ℝ) ≤ 2)
      have h2 : 2 * ‖c‖ * ‖w‖ ^ 2 ≤ (2 * (‖w‖ / 64)) * ‖w‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      have h3 : (2 * (‖w‖ / 64)) * ‖w‖ ^ 2 = ‖w‖ ^ 3 / 32 := by ring
      have h4 : ‖w‖ ^ 3 / 32 ≤ (1 / 12 : ℝ) * ‖w‖ ^ 4 := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 32)]
        have h5 : ‖w‖ ^ 3 * 1 ≤ ‖w‖ ^ 3 * (8 / 3 * ‖w‖) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        linarith
      linarith
    have h2c : ‖c‖ ^ 2 ≤ (1 / 12 : ℝ) * ‖w‖ ^ 4 := by
      have h1 : ‖c‖ ^ 2 ≤ (‖w‖ / 64) ^ 2 := by nlinarith [hjle, hj0, hw0]
      have h2 : (‖w‖ / 64) ^ 2 = ‖w‖ ^ 2 / 4096 := by ring
      have h3 : ‖w‖ ^ 2 / 4096 ≤ (1 / 12 : ℝ) * ‖w‖ ^ 4 := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4096)]
        have h5 : ‖w‖ ^ 2 * 1 ≤ ‖w‖ ^ 2 * (1024 / 3 * ‖w‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (by nlinarith [hw2]) (by positivity)
        linarith
      linarith
    have hc : ‖c‖ ≤ (1 / 12 : ℝ) * ‖w‖ ^ 4 := by
      have h3 : ‖w‖ / 64 ≤ (1 / 12 : ℝ) * ‖w‖ ^ 4 := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 64)]
        have h5 : ‖w‖ * 1 ≤ ‖w‖ * (16 / 3 * ‖w‖ ^ 3) :=
          mul_le_mul_of_nonneg_left (by nlinarith [hw2]) (by positivity)
        linarith
      linarith
    linarith
  have hexp : Work.Bottcher.pMap c w
      = w ^ 4 + (2 * (starRingEnd ℂ c) * w ^ 2 + (starRingEnd ℂ c) ^ 2 + c) := by
    rw [Work.Bottcher.pMap_apply]; ring
  rw [hexp]
  have hbound : ‖w ^ 4‖ - ‖2 * (starRingEnd ℂ c) * w ^ 2 + (starRingEnd ℂ c) ^ 2 + c‖
      ≤ ‖w ^ 4 + (2 * (starRingEnd ℂ c) * w ^ 2 + (starRingEnd ℂ c) ^ 2 + c)‖ := by
    have h := norm_sub_norm_le (w ^ 4)
      (-(2 * (starRingEnd ℂ c) * w ^ 2 + (starRingEnd ℂ c) ^ 2 + c))
    rw [sub_neg_eq_add, norm_neg] at h
    exact h
  rw [norm_pow] at hbound
  linarith

/-- On the far region the norm of the `p_c`-orbit increases:
`‖w‖ ≤ ‖p_c w‖` for `‖w‖ ≥ 64 (1 + ‖c‖) + 64`. -/
private lemma norm_le_norm_pMap_far (c w : ℂ)
    (hw : 64 * (1 + ‖c‖) + 64 ≤ ‖w‖) :
    ‖w‖ ≤ ‖Work.Bottcher.pMap c w‖ := by
  have h34 := three_quarters_pow_four_le_norm_pMap c w hw
  have hw2 : (2 : ℝ) ≤ ‖w‖ := by have := norm_nonneg c; linarith
  have hwpos : (0 : ℝ) < ‖w‖ := by linarith
  have h3 : (2 : ℝ) ≤ ‖w‖ ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2 : ℝ)) hw2 3
    norm_num at h
    linarith
  have h34' : ‖w‖ ≤ (3 / 4) * ‖w‖ ^ 4 := by
    have h : 2 * ‖w‖ ≤ ‖w‖ ^ 4 := by
      have := mul_le_mul_of_nonneg_left h3 (le_of_lt hwpos)
      nlinarith [this]
    linarith
  linarith

/-- The far region is invariant, and the orbit is monotone in norm: for
`‖z‖ ≥ 64 (1 + ‖c‖) + 64` and every `n`, `‖z‖ ≤ ‖p_c^n z‖`. -/
private lemma le_norm_iterate_pMap_far (c z : ℂ) (hz : 64 * (1 + ‖c‖) + 64 ≤ ‖z‖) (n : ℕ) :
    ‖z‖ ≤ ‖(Work.Bottcher.pMap c)^[n] z‖ := by
  have hR : ∀ w : ℂ, 64 * (1 + ‖c‖) + 64 ≤ ‖w‖ →
      (64 * (1 + ‖c‖) + 64 ≤ ‖Work.Bottcher.pMap c w‖) ∧
        ‖w‖ ≤ ‖Work.Bottcher.pMap c w‖ := by
    intro w hw
    refine ⟨?_, norm_le_norm_pMap_far c w hw⟩
    have h1 := norm_le_norm_pMap_far c w hw
    exact le_trans hw h1
  exact (Work.Bottcher.Core.norm_iterate_pMap_ge c (64 * (1 + ‖c‖) + 64) hR z hz n).2

/-! ## The logarithmic factor on the far region -/

/-- `‖log (normFactor c w)‖ ≤ (3/2)(‖c‖²+3‖c‖)/‖w‖²` as soon as `‖w‖ ≥ 1` and
`2(‖c‖²+3‖c‖) ≤ ‖w‖²` (so that `normFactor c w` is within `1/2` of `1`). -/
private lemma norm_log_normFactor_le_far (c w : ℂ) (h1 : 1 ≤ ‖w‖)
    (h2 : 2 * (‖c‖ ^ 2 + 3 * ‖c‖) ≤ ‖w‖ ^ 2) :
    ‖Complex.log (Work.Bottcher.normFactor c w)‖
      ≤ (3 / 2) * (‖c‖ ^ 2 + 3 * ‖c‖) / ‖w‖ ^ 2 := by
  have hz := Work.Bottcher.Core.norm_normFactor_sub_one_le_of_one_le c w h1
  have hz2 : ‖Work.Bottcher.normFactor c w - 1‖ ≤ 1 / 2 := by
    refine le_trans hz ?_
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < ‖w‖ ^ 2)]
    linarith
  have hlog := Complex.norm_log_one_add_half_le_self (z := Work.Bottcher.normFactor c w - 1) hz2
  have hsum : (1 : ℂ) + (Work.Bottcher.normFactor c w - 1) = Work.Bottcher.normFactor c w := by ring
  rw [hsum] at hlog
  calc ‖Complex.log (Work.Bottcher.normFactor c w)‖
      ≤ 3 / 2 * ‖Work.Bottcher.normFactor c w - 1‖ := hlog
    _ ≤ 3 / 2 * ((‖c‖ ^ 2 + 3 * ‖c‖) / ‖w‖ ^ 2) := by gcongr
    _ = (3 / 2) * (‖c‖ ^ 2 + 3 * ‖c‖) / ‖w‖ ^ 2 := by ring

/-! ## Geometric bookkeeping -/

private lemma tsum_quarter_pow_succ : (∑' n : ℕ, (1 / 4 : ℝ) ^ (n + 1)) = 1 / 3 := by
  have h0 : HasSum (fun n : ℕ => (1 / 4 : ℝ) ^ n) ((1 : ℝ) - 1 / 4)⁻¹ :=
    hasSum_geometric_of_norm_lt_one (by norm_num)
  have h1 : HasSum (fun n : ℕ => (1 / 4 : ℝ) * (1 / 4) ^ n)
      ((1 / 4 : ℝ) * ((1 : ℝ) - 1 / 4)⁻¹) := h0.mul_left (1 / 4 : ℝ)
  have h2 : (∑' n : ℕ, (1 / 4 : ℝ) ^ (n + 1)) = (1 / 4 : ℝ) * ((1 : ℝ) - 1 / 4)⁻¹ := by
    rw [← h1.tsum_eq]
    exact tsum_congr (fun n => by rw [pow_succ'])
  rw [h2]; norm_num

private lemma summable_quarter_pow_succ : Summable (fun n : ℕ => (1 / 4 : ℝ) ^ (n + 1)) := by
  have h0 : Summable (fun n : ℕ => (1 / 4 : ℝ) ^ n) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  simpa [pow_succ] using h0.mul_right (1 / 4 : ℝ)

/-! ## The main estimate -/

theorem norm_bottcherSeries_le_far (c z : ℂ) (hz : 64 * (1 + ‖c‖) + 64 ≤ ‖z‖) :
    ‖Work.Bottcher.bottcherSeries c z‖ ≤ (‖c‖ ^ 2 + 3 * ‖c‖ + 1) / ‖z‖ ^ 2 := by
  have hj0 : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  have hz2 : (2 : ℝ) ≤ ‖z‖ := by linarith
  have hz1 : (1 : ℝ) ≤ ‖z‖ := by linarith
  have hzpos : (0 : ℝ) < ‖z‖ := by linarith
  have h64 : 64 * ‖c‖ ≤ ‖z‖ := by linarith
  -- The key numeric consequence of the hypothesis: `2(‖c‖²+3‖c‖) ≤ ‖z‖²`.
  have h2k : 2 * (‖c‖ ^ 2 + 3 * ‖c‖) ≤ ‖z‖ ^ 2 := by
    nlinarith [h64, hj0, hz2, sq_nonneg ‖c‖, sq_nonneg ‖z‖, sq_nonneg (‖z‖ - 64 * ‖c‖)]
  -- The orbit of `z` is monotone far out.
  have hmono : ∀ n : ℕ, ‖z‖ ≤ ‖(Work.Bottcher.pMap c)^[n] z‖ :=
    le_norm_iterate_pMap_far c z hz
  -- Termwise logarithmic estimate, with `‖z_n‖` replaced by `‖z‖`.
  have hlog : ∀ n : ℕ,
      ‖Complex.log (Work.Bottcher.normFactor c ((Work.Bottcher.pMap c)^[n] z))‖
        ≤ (3 / 2) * (‖c‖ ^ 2 + 3 * ‖c‖) / ‖z‖ ^ 2 := by
    intro n
    have hzn : ‖z‖ ≤ ‖(Work.Bottcher.pMap c)^[n] z‖ := hmono n
    have h1 : 1 ≤ ‖(Work.Bottcher.pMap c)^[n] z‖ := le_trans hz1 hzn
    have h2 : 2 * (‖c‖ ^ 2 + 3 * ‖c‖) ≤ ‖(Work.Bottcher.pMap c)^[n] z‖ ^ 2 := by
      nlinarith [h2k, hzn, norm_nonneg ((Work.Bottcher.pMap c)^[n] z)]
    refine le_trans (norm_log_normFactor_le_far c _ h1 h2) ?_
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
  -- Termwise bound of the series.
  set K : ℝ := (3 / 2) * (‖c‖ ^ 2 + 3 * ‖c‖) / ‖z‖ ^ 2 with hKdef
  have hK0 : 0 ≤ K := by rw [hKdef]; positivity
  have hterm : ∀ n : ℕ, ‖Work.Bottcher.bottcherTerm c n z‖ ≤ (1 / 4 : ℝ) ^ (n + 1) * K := by
    intro n
    have hb : ‖Work.Bottcher.bottcherTerm c n z‖
        = (1 / 4 : ℝ) ^ (n + 1)
          * ‖Complex.log (Work.Bottcher.normFactor c ((Work.Bottcher.pMap c)^[n] z))‖ := by
      rw [Work.Bottcher.bottcherTerm, norm_mul]
      congr 1
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by norm_num)]
    rw [hb, hKdef]
    exact mul_le_mul_of_nonneg_left (hlog n) (by positivity)
  have hmaj : Summable (fun n : ℕ => (1 / 4 : ℝ) ^ (n + 1) * K) :=
    summable_quarter_pow_succ.mul_right K
  have hf : Summable (fun n : ℕ => ‖Work.Bottcher.bottcherTerm c n z‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hmaj
  -- Sum the comparison series *without* discarding the factor `1/3`.
  have hsum : (∑' n : ℕ, (1 / 4 : ℝ) ^ (n + 1) * K) = (1 / 3) * K := by
    rw [summable_quarter_pow_succ.tsum_mul_right, tsum_quarter_pow_succ]
  have hkey : (1 / 3) * K ≤ (‖c‖ ^ 2 + 3 * ‖c‖ + 1) / ‖z‖ ^ 2 := by
    have h1 : (1 / 3 : ℝ) * ((3 / 2) * (‖c‖ ^ 2 + 3 * ‖c‖)) ≤ ‖c‖ ^ 2 + 3 * ‖c‖ + 1 := by
      nlinarith [hj0]
    calc (1 / 3) * K
        = ((1 / 3) * ((3 / 2) * (‖c‖ ^ 2 + 3 * ‖c‖))) / ‖z‖ ^ 2 := by rw [hKdef]; ring
      _ ≤ (‖c‖ ^ 2 + 3 * ‖c‖ + 1) / ‖z‖ ^ 2 :=
          div_le_div_of_nonneg_right h1 (by positivity)
  calc ‖Work.Bottcher.bottcherSeries c z‖
      = ‖∑' n : ℕ, Work.Bottcher.bottcherTerm c n z‖ := rfl
    _ ≤ ∑' n : ℕ, ‖Work.Bottcher.bottcherTerm c n z‖ := norm_tsum_le_tsum_norm hf
    _ ≤ ∑' n : ℕ, (1 / 4 : ℝ) ^ (n + 1) * K := hf.tsum_le_tsum hterm hmaj
    _ = (1 / 3) * K := hsum
    _ ≤ (‖c‖ ^ 2 + 3 * ‖c‖ + 1) / ‖z‖ ^ 2 := hkey

end Work.Bottcher.Inverse
