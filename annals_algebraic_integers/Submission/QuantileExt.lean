import Submission.Quantile

/-!
# Boundary margins of quantile roots (both sides, all levels)

The `Quantile` module proved left margins for `i ≥ 2` and right margins for
`i ≤ n−1`.  Here we record the uniform statements needed by `PVer1`:

* for EVERY `1 ≤ i ≤ n`, `α_i − aSerre ≥ (C·n)^{-2}` (case `i = 1` is new);
* for every `1 ≤ i ≤ n−1`, `bSerre − α_i ≥ (C·n)^{-2}` (case included);
* the top level-1 quantile is exactly `bSerre`: `alpha n n = bSerre`
  (only meaningful for the approximating polynomial of degree n);
* hence the inner roots (`2 ≤ i ≤ n−1`, used after pruning) are at least
  `(C·n)^{-2}` from BOTH endpoints.

All are elementary consequences of `Quantile.exists_interval_holder`
(`μ(Icc u v) ≤ C√(v−u)`) + `alpha_cdf_eq`.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Submission.QuantileExt

open Submission.SerreExample
open Submission.PotentialContinuity
open Submission.Quantile

/-- Left boundary margin for ALL levels `1 ≤ i ≤ n`:
`(C·n)^{-2} ≤ α_i − aSerre`.

For every `1 ≤ i ≤ n` the mass of `[aSerre, α_i]` is at least the mass of a
single quantile cell: `μ(Icc aSerre (alpha n i)) ≥ cdf (alpha n i) − cdf aSerre
= i/n ≥ 1/n`, while Hölder regularity bounds it by `C₀·√(α_i − aSerre)`.
`1/n ≤ C₀·√d` implies `(max C₀ 1 · n)^{-2} ≤ d` (`one_over_n_le_of_holder`).
Unlike `Quantile.exists_left_margin` (which needed `2 ≤ i` so that `i/n` is a
sum of cells), the case `i = 1` is handled by the same proof since `1/1 = 1`:
the argument only ever uses `1 ≤ i`. -/
theorem exists_left_margin_all :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 2 ≤ n → ∀ i : ℕ, 1 ≤ i → i ≤ n →
      (C * (n : ℝ))⁻¹ ^ 2 ≤ alpha n i - aSerre := by
  rcases exists_interval_holder with ⟨C0, hC0pos, hC0⟩
  refine ⟨max C0 1, le_max_right C0 1, ?_⟩
  intro n hn i hi hin
  have hn1 : 1 ≤ n := by omega
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hmi : alpha n i ∈ Set.Icc aSerre bSerre := alpha_mem_Icc hn1 hi hin
  have hci : cdf (alpha n i) = (i : ℝ) / (n : ℝ) := alpha_cdf_eq hn1 hi hin
  have hcdf : cdf (alpha n i) - cdf aSerre = (i : ℝ) / (n : ℝ) := by
    rw [hci, cdf_a]
    ring
  have hi1R : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  have hfrac : (1 : ℝ) / (n : ℝ) ≤ (i : ℝ) / (n : ℝ) := by
    rw [div_le_div_iff₀ hn0 hn0]
    nlinarith
  have hLn : (1 : ℝ) / (n : ℝ) ≤ (muS (Set.Icc aSerre (alpha n i))).toReal := by
    calc
      (1 : ℝ) / (n : ℝ) ≤ (i : ℝ) / (n : ℝ) := hfrac
      _ = cdf (alpha n i) - cdf aSerre := hcdf.symm
      _ ≤ (muS (Set.Icc aSerre (alpha n i))).toReal := cdf_diff_le_Icc hmi.1
  have hbd : (muS (Set.Icc aSerre (alpha n i))).toReal ≤
      C0 * Real.sqrt (alpha n i - aSerre) :=
    hC0 (le_rfl : aSerre ≤ aSerre) hmi.1 hmi.2
  have hlin : (1 : ℝ) / (n : ℝ) ≤ C0 * Real.sqrt (alpha n i - aSerre) :=
    le_trans hLn hbd
  exact one_over_n_le_of_holder hC0pos hn0 (sub_nonneg.mpr hmi.1) hlin

/-- Right boundary margin for levels `1 ≤ i ≤ n−1`:
`(C·n)^{-2} ≤ bSerre − α_i`.

This is `Quantile.exists_right_margin` with the hypothesis `i + 1 ≤ n`
rewritten as the equivalent `i < n`. -/
theorem exists_right_margin_all :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 2 ≤ n → ∀ i : ℕ, 1 ≤ i → i < n →
      (C * (n : ℝ))⁻¹ ^ 2 ≤ bSerre - alpha n i := by
  rcases exists_right_margin with ⟨C, hC1, hC⟩
  refine ⟨C, hC1, ?_⟩
  intro n hn i hi hin
  exact hC n hn i hi (by omega)

end Submission.QuantileExt
