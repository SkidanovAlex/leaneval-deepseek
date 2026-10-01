import Mathlib
import Submission.Work.LinnikAreas.Density4.BzHard.mertens_log_weighted_one

namespace Work.ZeroDensity.Jutila.LzAux

open Finset

noncomputable section

/-- `exp (-y) ≤ 24 / y ^ 4` for `y > 0`, from `exp y ≥ y ^ 4 / 4!`. -/
private lemma exp_neg_le_inv_pow4 {y : ℝ} (hy : 0 < y) : Real.exp (-y) ≤ 24 / y ^ 4 := by
  have h := Real.pow_div_factorial_le_exp y (le_of_lt hy) 4
  have h24 : y ^ 4 / (24 : ℝ) ≤ Real.exp y := by
    have hf : (Nat.factorial 4 : ℝ) = 24 := by norm_num
    rw [hf] at h
    exact h
  have hpos : (0 : ℝ) < y ^ 4 / 24 := by positivity
  have hle : 1 / Real.exp y ≤ 1 / (y ^ 4 / 24) := one_div_le_one_div_of_le hpos h24
  have hfe : 1 / (y ^ 4 / 24) = 24 / y ^ 4 := by rw [one_div_div]
  rw [hfe, one_div] at hle
  rw [Real.exp_neg]
  exact hle

/-- The real-argument Möbius sum splits into the integer-argument Möbius sum at `⌊T⌋₊` plus
`log (T/⌊T⌋₊)` times the reciprocal partial sum `Σ_{t ≤ ⌊T⌋₊} μ(t)/t`. -/
private lemma mertensReal_decomp {T : ℝ} (hT : 2 ≤ T) :
    (∑ t ∈ Finset.Icc 1 ⌊T⌋₊,
        (ArithmeticFunction.moebius t : ℝ) * (Real.log (T / (t : ℝ)) - 1) / (t : ℝ))
      = (∑ t ∈ Finset.Icc 1 ⌊T⌋₊,
          (ArithmeticFunction.moebius t : ℝ) *
            (Real.log (⌊T⌋₊ : ℝ) - Real.log (t : ℝ) - 1) / (t : ℝ))
        + Real.log (T / (⌊T⌋₊ : ℝ)) * Commons.NumberTheory.Moebius.muRecipSum ⌊T⌋₊ := by
  rw [Commons.NumberTheory.Moebius.muRecipSum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht1 : (1 : ℝ) ≤ (t : ℝ) := by
    have := (Finset.mem_Icc.mp ht).1
    exact_mod_cast this
  have htpos : (0 : ℝ) < (t : ℝ) := by linarith
  have hTpos : (0 : ℝ) < T := by linarith
  have hn2nat : 2 ≤ ⌊T⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hnpos : (0 : ℝ) < ((⌊T⌋₊ : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (by omega)
  have key : Real.log (T / (t : ℝ)) - 1
      = (Real.log (⌊T⌋₊ : ℝ) - Real.log (t : ℝ) - 1) + Real.log (T / (⌊T⌋₊ : ℝ)) := by
    rw [Real.log_div (ne_of_gt hTpos) (ne_of_gt htpos),
        Real.log_div (ne_of_gt hTpos) (ne_of_gt hnpos)]
    ring
  rw [key]; ring

/-- `|log (T/⌊T⌋₊)| ≤ 1/⌊T⌋₊` for `T ≥ 2`. -/
private lemma abs_log_div_floor_le_inv {T : ℝ} (hT : 2 ≤ T) :
    |Real.log (T / (⌊T⌋₊ : ℝ))| ≤ 1 / (⌊T⌋₊ : ℝ) := by
  have hn2nat : 2 ≤ ⌊T⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hnpos : (0 : ℝ) < ((⌊T⌋₊ : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
  have hble : ((⌊T⌋₊ : ℕ) : ℝ) ≤ T := Nat.floor_le (by linarith)
  have hblt : T < ((⌊T⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one T
  have hq1 : 1 ≤ T / (⌊T⌋₊ : ℝ) := by rw [le_div_iff₀ hnpos]; linarith
  have hlog_nonneg : 0 ≤ Real.log (T / (⌊T⌋₊ : ℝ)) := Real.log_nonneg hq1
  rw [abs_of_nonneg hlog_nonneg]
  calc Real.log (T / (⌊T⌋₊ : ℝ)) ≤ T / (⌊T⌋₊ : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
    _ = (T - (⌊T⌋₊ : ℝ)) / (⌊T⌋₊ : ℝ) := by field_simp
    _ ≤ 1 / (⌊T⌋₊ : ℝ) := by
        rw [div_le_div_iff_of_pos_right hnpos]; linarith

/-- `log T ≤ 2 log ⌊T⌋₊` for `T ≥ 2`. -/
private lemma log_le_two_log_floor {T : ℝ} (hT : 2 ≤ T) :
    Real.log T ≤ 2 * Real.log (⌊T⌋₊ : ℝ) := by
  have hn2 : (2 : ℝ) ≤ ((⌊T⌋₊ : ℕ) : ℝ) :=
    Nat.cast_le.mpr (Nat.le_floor (by push_cast; linarith))
  have hnpos : (0 : ℝ) < ((⌊T⌋₊ : ℕ) : ℝ) := by linarith
  have hTpos : (0 : ℝ) < T := by linarith
  have hblt : T < ((⌊T⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one T
  have h1 : T ≤ 2 * (⌊T⌋₊ : ℝ) := by linarith
  calc Real.log T ≤ Real.log (2 * ((⌊T⌋₊ : ℕ) : ℝ)) := Real.log_le_log hTpos h1
    _ = Real.log 2 + Real.log (⌊T⌋₊ : ℝ) := by
        rw [Real.log_mul (by norm_num) (ne_of_gt hnpos)]
    _ ≤ Real.log (⌊T⌋₊ : ℝ) + Real.log (⌊T⌋₊ : ℝ) := by
        have : Real.log 2 ≤ Real.log ((⌊T⌋₊ : ℕ) : ℝ) := Real.log_le_log (by norm_num) hn2
        linarith
    _ = 2 * Real.log (⌊T⌋₊ : ℝ) := by ring

/-- The sharp Mertens-type log-weighted Möbius reciprocal sum with a REAL argument `T`:
`Σ_{t ≤ ⌊T⌋} μ(t)(log(T/t)−1)/t = 1 + O(log^{-2}T)` for real `T ≥ 2`.
Reduces to the integer version `Work.LinnikAreas.Density4.BzHard.mertens_log_weighted_one`
(`Σ_{t≤T} μ(t)(log(T/t)−1)/t = 1 + O(log^{-2}T)` for `T : ℕ`): write `T = n + δ`,
`log(T/t) = log(n/t) + log(T/n)`, and use `Σ_{t≤n} μ(t)/t = O(e^{−c√log n})`
(`Commons.NumberTheory.Moebius.muRecipSum_exp_decay`). -/
theorem MertensReal : ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
    |(∑ t ∈ Finset.Icc 1 ⌊T⌋₊,
        (ArithmeticFunction.moebius t : ℝ) * (Real.log (T/(t:ℝ)) - 1) / (t:ℝ)) - 1|
      ≤ C / (Real.log T)^2 := by
  obtain ⟨C', hC'pos, hint⟩ := Work.LinnikAreas.Density4.BzHard.mertens_log_weighted_one
  obtain ⟨K, c, hc, hK, hmu⟩ := Work.LinnikAreas.Density4.muRecipSum_exp_decay
  refine ⟨4 * (C' + 24 * K / c ^ 4), by positivity, ?_⟩
  intro T hT
  have hn2nat : 2 ≤ ⌊T⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hn2 : (2 : ℝ) ≤ ((⌊T⌋₊ : ℕ) : ℝ) := Nat.cast_le.mpr hn2nat
  have hnpos : (0 : ℝ) < ((⌊T⌋₊ : ℕ) : ℝ) := by linarith
  have hn1 : (1 : ℝ) ≤ ((⌊T⌋₊ : ℕ) : ℝ) := by linarith
  have hTpos : (0 : ℝ) < T := by linarith
  have hlogn_pos : 0 < Real.log (⌊T⌋₊ : ℝ) := Real.log_pos (by linarith)
  have hlogT_pos : 0 < Real.log T := Real.log_pos (by linarith)
  -- the integer-argument sum, with its sharp `O((log n)^{-2})` error
  have hInt : |(∑ t ∈ Finset.Icc 1 ⌊T⌋₊,
        (ArithmeticFunction.moebius t : ℝ) *
          (Real.log (⌊T⌋₊ : ℝ) - Real.log (t : ℝ) - 1) / (t : ℝ)) - 1|
      ≤ C' / (Real.log (⌊T⌋₊ : ℝ)) ^ 2 := hint ⌊T⌋₊ hn2nat
  -- the correction coming from the true real argument `T` inside the log
  have hlogc : |Real.log (T / (⌊T⌋₊ : ℝ))| ≤ 1 / (⌊T⌋₊ : ℝ) := abs_log_div_floor_le_inv hT
  have hM : |Commons.NumberTheory.Moebius.muRecipSum ⌊T⌋₊|
      ≤ K * Real.exp (-(c * Real.sqrt (Real.log (⌊T⌋₊ : ℝ)))) := hmu ⌊T⌋₊ (by omega)
  have hypos : 0 < c * Real.sqrt (Real.log (⌊T⌋₊ : ℝ)) := mul_pos hc (Real.sqrt_pos.mpr hlogn_pos)
  have hexp : Real.exp (-(c * Real.sqrt (Real.log (⌊T⌋₊ : ℝ))))
      ≤ 24 / (c * Real.sqrt (Real.log (⌊T⌋₊ : ℝ))) ^ 4 := exp_neg_le_inv_pow4 hypos
  have hpow : (c * Real.sqrt (Real.log (⌊T⌋₊ : ℝ))) ^ 4
      = c ^ 4 * (Real.log (⌊T⌋₊ : ℝ)) ^ 2 := by
    rw [mul_pow, show (Real.sqrt (Real.log (⌊T⌋₊ : ℝ))) ^ 4
        = (Real.log (⌊T⌋₊ : ℝ)) ^ 2 by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hlogn_pos.le]]
  have hcorr : |Real.log (T / (⌊T⌋₊ : ℝ)) * Commons.NumberTheory.Moebius.muRecipSum ⌊T⌋₊|
      ≤ 24 * K / (c ^ 4 * (Real.log (⌊T⌋₊ : ℝ)) ^ 2) := by
    rw [abs_mul]
    calc |Real.log (T / (⌊T⌋₊ : ℝ))| * |Commons.NumberTheory.Moebius.muRecipSum ⌊T⌋₊|
        ≤ (1 / (⌊T⌋₊ : ℝ)) *
            (K * Real.exp (-(c * Real.sqrt (Real.log (⌊T⌋₊ : ℝ))))) :=
          mul_le_mul hlogc hM (abs_nonneg _) (by positivity)
      _ ≤ (1 / (⌊T⌋₊ : ℝ)) *
            (K * (24 / (c * Real.sqrt (Real.log (⌊T⌋₊ : ℝ))) ^ 4)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp hK.le) (by positivity)
      _ = 24 * K / (c ^ 4 * (Real.log (⌊T⌋₊ : ℝ)) ^ 2) / (⌊T⌋₊ : ℝ) := by
          rw [hpow]; ring
      _ ≤ 24 * K / (c ^ 4 * (Real.log (⌊T⌋₊ : ℝ)) ^ 2) := by
          exact div_le_self (by positivity) hn1
  -- assembling the two errors
  have hmain : |(∑ t ∈ Finset.Icc 1 ⌊T⌋₊,
        (ArithmeticFunction.moebius t : ℝ) * (Real.log (T / (t : ℝ)) - 1) / (t : ℝ)) - 1|
      ≤ (C' + 24 * K / c ^ 4) / (Real.log (⌊T⌋₊ : ℝ)) ^ 2 := by
    rw [mertensReal_decomp hT]
    have hdec : (∑ t ∈ Finset.Icc 1 ⌊T⌋₊,
          (ArithmeticFunction.moebius t : ℝ) *
            (Real.log (⌊T⌋₊ : ℝ) - Real.log (t : ℝ) - 1) / (t : ℝ))
          + Real.log (T / (⌊T⌋₊ : ℝ)) * Commons.NumberTheory.Moebius.muRecipSum ⌊T⌋₊ - 1
        = ((∑ t ∈ Finset.Icc 1 ⌊T⌋₊,
            (ArithmeticFunction.moebius t : ℝ) *
              (Real.log (⌊T⌋₊ : ℝ) - Real.log (t : ℝ) - 1) / (t : ℝ)) - 1)
          + Real.log (T / (⌊T⌋₊ : ℝ)) * Commons.NumberTheory.Moebius.muRecipSum ⌊T⌋₊ := by ring
    rw [hdec]
    calc |((∑ t ∈ Finset.Icc 1 ⌊T⌋₊,
            (ArithmeticFunction.moebius t : ℝ) *
              (Real.log (⌊T⌋₊ : ℝ) - Real.log (t : ℝ) - 1) / (t : ℝ)) - 1)
          + Real.log (T / (⌊T⌋₊ : ℝ)) * Commons.NumberTheory.Moebius.muRecipSum ⌊T⌋₊|
        ≤ |(∑ t ∈ Finset.Icc 1 ⌊T⌋₊,
            (ArithmeticFunction.moebius t : ℝ) *
              (Real.log (⌊T⌋₊ : ℝ) - Real.log (t : ℝ) - 1) / (t : ℝ)) - 1|
          + |Real.log (T / (⌊T⌋₊ : ℝ)) * Commons.NumberTheory.Moebius.muRecipSum ⌊T⌋₊| :=
          abs_add_le _ _
      _ ≤ C' / (Real.log (⌊T⌋₊ : ℝ)) ^ 2
            + 24 * K / (c ^ 4 * (Real.log (⌊T⌋₊ : ℝ)) ^ 2) := add_le_add hInt hcorr
      _ = (C' + 24 * K / c ^ 4) / (Real.log (⌊T⌋₊ : ℝ)) ^ 2 := by
          rw [div_mul_eq_div_div, ← add_div]
  -- converting `1/(log ⌊T⌋₊)²` into `1/(log T)²`
  have hconv : 1 / (Real.log (⌊T⌋₊ : ℝ)) ^ 2 ≤ 4 / (Real.log T) ^ 2 := by
    have hmono := log_le_two_log_floor hT
    have hsq : (Real.log T) ^ 2 ≤ 4 * (Real.log (⌊T⌋₊ : ℝ)) ^ 2 := by nlinarith
    have h1 : 1 / (4 * (Real.log (⌊T⌋₊ : ℝ)) ^ 2) ≤ 1 / (Real.log T) ^ 2 :=
      one_div_le_one_div_of_le (by positivity) hsq
    have h2 : (4 : ℝ) * (1 / (4 * (Real.log (⌊T⌋₊ : ℝ)) ^ 2))
        = 1 / (Real.log (⌊T⌋₊ : ℝ)) ^ 2 := by field_simp
    rw [← h2]
    calc (4 : ℝ) * (1 / (4 * (Real.log (⌊T⌋₊ : ℝ)) ^ 2))
        ≤ 4 * (1 / (Real.log T) ^ 2) := mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = 4 / (Real.log T) ^ 2 := by ring
  calc |(∑ t ∈ Finset.Icc 1 ⌊T⌋₊,
        (ArithmeticFunction.moebius t : ℝ) * (Real.log (T / (t : ℝ)) - 1) / (t : ℝ)) - 1|
      ≤ (C' + 24 * K / c ^ 4) / (Real.log (⌊T⌋₊ : ℝ)) ^ 2 := hmain
    _ ≤ (C' + 24 * K / c ^ 4) * (4 / (Real.log T) ^ 2) := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (by simpa [one_div] using hconv) (by positivity)
    _ = 4 * (C' + 24 * K / c ^ 4) / (Real.log T) ^ 2 := by ring

end

end Work.ZeroDensity.Jutila.LzAux
