import Mathlib
import Submission.Work.BMF.halasz_series_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- The `n`th term `f n / n ^ z` of an L-series, as a function of `z`, has derivative
`-f n · log n · n^{-s}` at `s` (for `n ≠ 0`). -/
lemma hasDerivAt_LSeries_term (f : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) (s : ℂ) :
    HasDerivAt (fun z : ℂ => LSeries.term f z n)
      (f n * (-(Real.log n : ℂ)) * (n : ℂ) ^ (-s)) s := by
  have h := LSeries.hasDerivAt_term f n s
  refine h.congr_deriv ?_
  rw [LSeries.term_of_ne_zero hn, LSeries.logMul, Complex.cpow_neg, ← Complex.natCast_log]
  ring

end Work.BMF
