import Mathlib
import Submission.Work.Cert.Spec

/-!
# The `log 2` enclosure used by the `expLo` certificate (`Work.Cert.ExpLoSound`)

This is the one transcendental input of the Theorem-A numeric certificate: the scale mantissas
`LN2LO/S < log 2 < LN2HI/S` with `S = 2^40·10^8` and `LN2HI - LN2LO = 2` (two ulps), i.e. an
enclosure of `Real.log 2` of width `2/S ≈ 1.8·10⁻²⁰`.

Route. Use Mathlib's Taylor estimate for the logarithm
`Real.abs_log_sub_add_sum_range_le` with `x = 1/2`: it bounds the error of the alternating
series for `log (1 - 1/2) = -log 2` at cutoff `n` by `|x|^(n+1)/(1-|x|) = 2^{-n}`.  With `n = 80`
this gives `|P - log 2| ≤ 2^{-80}` where `P = Σ_{i<80} 2^{-(i+1)}/(i+1)` is an explicit rational,
and `norm_num` evaluates the resulting rational comparisons
`LN2LO/S ≤ P - 2^{-80}` and `P + 2^{-80} ≤ LN2HI/S`
(the slack at `n = 80` is about `0.71/S` resp. `1.28/S`, in units of the ulp `1/S ≈ 9.1·10⁻²¹`).
-/

namespace Work.Cert

theorem log_two_bounds : (LN2LO : ℝ) / (S : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ (LN2HI : ℝ) / (S : ℝ) := by
  -- the partial sum `P = Σ_{i<80} 2^{-(i+1)}/(i+1)` of the series `log 2 = Σ_{j≥1} 2^{-j}/j`,
  set P : ℝ := ∑ i ∈ Finset.range 80, ((1 / 2 : ℝ)) ^ (i + 1) / (i + 1) with hP
  -- Mathlib's Taylor estimate for `log (1 - x)` at `x = 1/2`, cutoff `80`
  have hab := Real.abs_log_sub_add_sum_range_le (x := (1 / 2 : ℝ)) (by norm_num) 80
  rw [← hP] at hab
  -- `log (1 - 1/2) = log 2⁻¹ = -log 2`, and `|1/2|^(80+1)/(1-|1/2|) = 2^{-80}`
  have h1 : (1 : ℝ) - 1 / 2 = (2 : ℝ)⁻¹ := by norm_num
  rw [h1, Real.log_inv] at hab
  have h2 : |(1 / 2 : ℝ)| = 1 / 2 := by norm_num
  rw [h2] at hab
  have h3 : (1 / 2 : ℝ) ^ (80 + 1) / (1 - 1 / 2) = (1 / 2) ^ 80 := by norm_num
  rw [h3] at hab
  -- hence `P - 2^{-80} ≤ log 2 ≤ P + 2^{-80}`
  obtain ⟨hlo, hhi⟩ := abs_le.mp hab
  -- the two rational comparisons pinning `P` against the certificate endpoints
  have hnum1 : (LN2LO : ℝ) / (S : ℝ) ≤ P - (1 / 2) ^ 80 := by
    norm_num [P, LN2LO, S]
  have hnum2 : P + (1 / 2) ^ 80 ≤ (LN2HI : ℝ) / (S : ℝ) := by
    norm_num [P, LN2HI, S]
  constructor <;> linarith

end Work.Cert
