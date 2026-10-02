import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Sparse.ProbBasic
import Submission.Work.Deep.Sparse.ProbModel
import Submission.Work.Deep.Sparse.ncp_lower_tail
import Submission.Work.Deep.Sparse.log_large_of_growth

/-!
# Concentration of `pairTerm - tripleTerm` in the naive colouring procedure

This module proves `Work.Deep.Sparse.concentration_ncp`: the tail bound

`P[ pairTerm v - tripleTerm v < (1/2) * (|nonAdjPairs G v| / 2 * (1/k) * ((k-1)/k)^(2D) * (1 - D/(3k))) ] ≤ 1/(4 D^6)`

for a graph `G` of maximum degree at most `D`, a number of colours `k` with `D ≤ 2k ≤ 4D`,
and `(δ/2) D^2/2 ≤ |nonAdjPairs G v|/2`, `10^6 (log (D+2))^8 ≤ δ^2 D`.

The *content* of the concentration is the deep input
`Work.Deep.Sparse.ncp_lower_tail` (the Bruhn–Joos / Bonamy–Perrett–Postle concentration of the
naive colouring procedure), which gives the much stronger tail

`P[ pairTerm v - tripleTerm v < μ/2 ] ≤ exp (-(log (D+2))^4 / 5000)`,

where `μ = |nonAdjPairs G v|/2 * (1/k) * ((k-1)/k)^(2D) * (1 - D/(3k))` is the expectation
lower bound of `Work.Deep.Sparse.expect_pair_sub_triple`.  This module performs the
elementary reduction `exp (-(log (D+2))^4 / 5000) ≤ 1/(4 D^6)`, which needs only

* `log (D+2) ≥ 44`, forced by `10^6 (log (D+2))^8 ≤ δ^2 D ≤ D`
  (`Work.Deep.Sparse.log_large_of_growth`), and
* the elementary inequality `L^4 / 5000 ≥ log 4 + 6 log D` for `L = log (D+2) ≥ 44`.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Deep.Sparse

/-- **Concentration of `pairTerm - tripleTerm` (the naive colouring procedure).** -/
theorem concentration_ncp {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k D : ℕ} (hk : 0 < k) (hD : 0 < D) (hDk : D ≤ 2 * k) (hkD : (k : ℝ) ≤ 2 * D)
    [Nonempty (V → Fin k)]
    (hdeg : ∀ x : V, G.degree x ≤ D) (v : V)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hsp : (δ / 2) * (D : ℝ) ^ 2 / 2 ≤ ((Work.Deep.Sparse.nonAdjPairs G v).card : ℝ) / 2)
    (hbig : (10 : ℝ) ^ 6 * (Real.log ((D : ℝ) + 2)) ^ 8 ≤ δ ^ 2 * (D : ℝ)) :
    (Work.Deep.Sparse.colSpace (V := V) k).prob
        {f | (((Work.Deep.Sparse.ofColoring G f).pairTerm v : ℝ)
              - ((Work.Deep.Sparse.ofColoring G f).tripleTerm v : ℝ))
            < (1 / 2) * (((Work.Deep.Sparse.nonAdjPairs G v).card : ℝ) / 2
                * ((1 : ℝ) / (k : ℝ) * (((k : ℝ) - 1) / (k : ℝ)) ^ (2 * D))
                * (1 - (D : ℝ) / (3 * (k : ℝ))))}
      ≤ 1 / (4 * (D : ℝ) ^ 6) := by
  have hD1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hDr : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  -- `δ ^ 2 ≤ 1`, hence `10^6 (log (D+2))^8 ≤ D`
  have hδ2 : δ ^ 2 ≤ 1 := by nlinarith [hδ0, hδ1]
  have hb : (10 : ℝ) ^ 6 * (Real.log ((D : ℝ) + 2)) ^ 8 ≤ (D : ℝ) := by
    calc (10 : ℝ) ^ 6 * (Real.log ((D : ℝ) + 2)) ^ 8 ≤ δ ^ 2 * (D : ℝ) := hbig
      _ ≤ 1 * (D : ℝ) := mul_le_mul_of_nonneg_right hδ2 (le_of_lt hDr)
      _ = (D : ℝ) := by ring
  -- hence `log (D+2) ≥ 44`
  have hL : (44 : ℝ) ≤ Real.log ((D : ℝ) + 2) := log_large_of_growth hD1 hb
  -- the elementary inequality `log (4 D^6) ≤ (log (D+2))^4 / 5000`
  have hkey : Real.log (4 * (D : ℝ) ^ 6) ≤ (Real.log ((D : ℝ) + 2)) ^ 4 / 5000 := by
    have h4pos : (0 : ℝ) < 4 := by norm_num
    have hD6pos : (0 : ℝ) < (D : ℝ) ^ 6 := by positivity
    rw [Real.log_mul (ne_of_gt h4pos) (ne_of_gt hD6pos), Real.log_pow]
    have hlogD : Real.log (D : ℝ) ≤ Real.log ((D : ℝ) + 2) := Real.log_le_log hDr (by linarith)
    have hlog4 : Real.log 4 ≤ (2 : ℝ) := by
      rw [Real.log_le_iff_le_exp h4pos]
      have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
      rw [h2]; nlinarith
    have hmain : 10000 + 30000 * Real.log ((D : ℝ) + 2) ≤ (Real.log ((D : ℝ) + 2)) ^ 4 :=
      by nlinarith [hL, sq_nonneg (Real.log ((D : ℝ) + 2) - 44)]
    linarith
  -- convert to the exponential bound
  have hexp : Real.exp (-((Real.log ((D : ℝ) + 2)) ^ 4) / 5000) ≤ 1 / (4 * (D : ℝ) ^ 6) := by
    have h4D6 : (0 : ℝ) < 4 * (D : ℝ) ^ 6 := by positivity
    have h1 : Real.exp (-((Real.log ((D : ℝ) + 2)) ^ 4) / 5000)
        ≤ Real.exp (-(Real.log (4 * (D : ℝ) ^ 6))) := by
      apply Real.exp_le_exp.mpr
      linarith
    have h2 : Real.exp (-(Real.log (4 * (D : ℝ) ^ 6))) = 1 / (4 * (D : ℝ) ^ 6) := by
      rw [Real.exp_neg, Real.exp_log h4D6, one_div]
    linarith
  exact le_trans (ncp_lower_tail G hk hD hDk hkD hdeg v hδ0 hδ1 hsp hbig) hexp

end Work.Deep.Sparse
