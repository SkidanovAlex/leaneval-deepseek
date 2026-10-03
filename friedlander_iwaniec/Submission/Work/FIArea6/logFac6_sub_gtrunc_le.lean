import Mathlib
import Submission.Work.FIArea6.S16UDefs
import Submission.Work.FIArea7.LogFacFourier
import Submission.Work.FIArea7.LogFacArg
import Submission.Work.FIArea7.logFac6_eq_sum_freq

namespace Work.FIArea6

open Finset
open scoped BigOperators

noncomputable section

/-- `log 16 = 2 log 2 + log 4`, the identity that reconciles the classical constant term
`2log2` of the log-sine expansion with the constant `log 16` of `gtrunc` (and the round-6
normalisation `logFac6 = logFac + log 4` of the main-term weight). -/
lemma FIA6_log_sixteen : Real.log 16 = 2 * Real.log 2 + Real.log 4 := by
  rw [show (16 : ℝ) = 4 * 4 by norm_num, Real.log_mul (by norm_num) (by norm_num),
    show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  ring

/-- **(16.7)–(16.9) in the `logFac6` normalisation**: the truncated classical Fourier series
(with constant term `log 16`) approximates `logFac6` with the explicit remainder
`4/(K|sin α|)`, `α = arg z₂ − arg z₁`.  This is *FI*'s (16.9) restated for the round-6 weight
`logFac6 = log(8|z₁z₂|/|Δ|)`, obtained from `logFac_eq_sum_cos` for
`logFac = log(2|z₁z₂|/|Δ|)` by the identity `logFac6 = logFac + log 4` (which shifts both the
weight and the constant term by `log 4`). -/
theorem FIA6_logFac6_eq_log16_add_sum (z1 z2 : GaussianInt) (K : ℕ) (hK : 1 ≤ K)
    (h : Work.FIPlan.Delta z1 z2 ≠ 0) :
    |Work.FITop4.logFac6 z1 z2
        - (Real.log 16 + ∑ n ∈ Finset.Icc 1 K,
            Real.cos (2 * (n : ℝ) * (Complex.arg z2.toComplex - Complex.arg z1.toComplex))
              / (n : ℝ))|
      ≤ 4 / ((K : ℝ)
        * |Real.sin (Complex.arg z2.toComplex - Complex.arg z1.toComplex)|) := by
  have hlf := Work.FIArea7.fi_logFac6_eq_logFac_add_log4 z1 z2 h
  have hmain := Work.FIArea7.logFac_eq_sum_cos z1 z2 K hK h
  rw [hlf, FIA6_log_sixteen]
  have hkey : Work.FITop3.logFac z1 z2 + Real.log 4
        - ((2 * Real.log 2 + Real.log 4)
            + ∑ n ∈ Finset.Icc 1 K,
                Real.cos (2 * (n : ℝ)
                  * (Complex.arg z2.toComplex - Complex.arg z1.toComplex)) / (n : ℝ))
      = Work.FITop3.logFac z1 z2
        - (2 * Real.log 2
            + ∑ n ∈ Finset.Icc 1 K,
                Real.cos (2 * (n : ℝ)
                  * (Complex.arg z2.toComplex - Complex.arg z1.toComplex)) / (n : ℝ)) := by
    ring
  rw [hkey]
  exact hmain

/-- *FI* (16.7)-(16.9): the truncated classical Fourier series of the log-sine approximates the logarithmic factor `logFac6` of the `U`-cut with the explicit remainder `4/(K|sin α|)`, `K = X³`, `α = arg z₂ − arg z₁`. -/
theorem logFac6_sub_gtrunc_le (z1 z2 : GaussianInt) (X : ℕ) (hX : 1 ≤ X)
    (h : Work.FIPlan.Delta z1 z2 ≠ 0) :
    |Work.FITop4.logFac6 z1 z2
        - Work.FIArea6.gtrunc X (Complex.arg z2.toComplex - Complex.arg z1.toComplex)|
      ≤ 4 / ((Work.FIArea6.Kcut X : ℝ)
          * |Real.sin (Complex.arg z2.toComplex - Complex.arg z1.toComplex)|) := by
  have hK : 1 ≤ Kcut X := by
    unfold Kcut
    exact one_le_pow₀ hX
  unfold gtrunc
  exact FIA6_logFac6_eq_log16_add_sum z1 z2 (Kcut X) hK h

end

end Work.FIArea6
