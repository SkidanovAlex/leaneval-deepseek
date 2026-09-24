import Mathlib
import Submission.Work.NumberTheory.Chen.BTermCount.cbarHalfDefs

namespace Work.NumberTheory.Chen.BTermCount

open MeasureTheory intervalIntegral

/-! ## Rational constants for the *sharp* BJS bound at the sift limit `1/10`

This file sharpens the certificate of `cbarHalfDefs.lean`.  There the last piece

`∫_{3/10}^1 log (1 − y/2)/y dy`

of the `P2` integral is bounded with the four term Taylor majorant of `−log (1 − z)/z`
(`cbarHalfR4`, value `0.42420…`), which is only enough to certify `∫_{1/10}^{1/3} ≤ 1/2`.
Using instead the *ten* term truncation of the series `−log (1 − z) = ∑_{m ≥ 1} z^m/m`
(value `cbarS = 0.42619…`) certifies the sharp bound

`∫_{1/10}^{1/3} log (2 − 3β)/(β(1 − β)) dβ ≤ 0.496`,

the true value of the integral being `0.490995…`. -/

/-- The exact value of `∫_{3/10}^1 ∑_{m<10} y^m/((m+1) 2^{m+1}) dy`, i.e. the integral of the
ten term truncation of `−log (1 − y/2)/y` over `[3/10, 1]`:
`cbarS = ∑_{m<10} (1 − (3/10)^{m+1})/(2^{m+1}(m+1)²)` (`= 0.426198…`). -/
noncomputable def cbarS : ℝ :=
  ∑ m ∈ Finset.range 10, (1 - (3/10:ℝ)^(m+1))/((2:ℝ)^(m+1) * ((m:ℝ)+1)^2)

theorem cbarS_nonneg : 0 ≤ cbarS := by
  rw [cbarS]
  refine Finset.sum_nonneg fun m _ => ?_
  apply div_nonneg _ (by positivity)
  have h : (3/10:ℝ)^(m+1) ≤ 1 := by
    apply pow_le_one₀ (by norm_num) (by norm_num)
  linarith

/-- The sharp rational certificate.  With `cbarS` in place of the four term `cbarHalfR4` the
numerical left hand side drops from `0.4975090…` to `0.4955740…`, which is below the requested
`0.496`. -/
theorem cbarSharp_cert :
    cbarHalfC1*cbarHalfC2 - cbarS + (17/54)*cbarHalfC3^2 - (25/594)*cbarHalfLb1^2
      ≤ (0.496 : ℝ) := by
  norm_num [cbarHalfC1, cbarHalfC2, cbarHalfC3, cbarHalfLb1, cbarHalfLb2, cbarS,
    Finset.sum_range_succ]

end Work.NumberTheory.Chen.BTermCount
