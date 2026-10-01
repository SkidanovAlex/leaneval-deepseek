import Mathlib
import Submission.Work.LinnikAreas.FarRepel.reTermLogMulIterate

namespace Work.LinnikAreas.TuranOther

open Work.LinnikAreas.FarRepel (reTermLogMulIterate)

/-- The `k`-fold `log`-weighted real-part series of `f` at `s` is summable, provided the
abscissa of absolute convergence of `f` is at most `1` and `re s > 1`.

Indeed, `abscissaOfAbsConv (logMul^[k] f) = abscissaOfAbsConv f ≤ 1 < re s`, so the
`k`-fold `log`-multiplied L-series of `f` converges absolutely at `s`; taking real parts
gives the claim (the `n = 0` term vanishes because `k ≥ 1`). -/
theorem summableLogMulTermRe {f : ℕ → ℂ} (hab : LSeries.abscissaOfAbsConv f ≤ 1) {k : ℕ} (hk : 1 ≤ k) {s : ℂ} (hs : 1 < s.re) : Summable (fun n : ℕ => (Real.log n) ^ k * (f n * (n : ℂ) ^ (-s)).re) := by
  have hs' : LSeries.abscissaOfAbsConv f < (s.re : EReal) :=
    hab.trans_lt (EReal.coe_lt_coe_iff.mpr hs)
  have hsumm : LSeriesSummable (LSeries.logMul ^[k] f) s :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re
      (by rw [LSeries.absicssaOfAbsConv_logPowMul]; exact hs')
  have hre : Summable (fun n => (LSeries.term (LSeries.logMul ^[k] f) s n).re) :=
    (Complex.hasSum_re hsumm.hasSum).summable
  exact hre.congr fun n => by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [Real.log_zero, zero_pow (by omega : k ≠ 0)]
    · exact reTermLogMulIterate (f := f) k s hn

end Work.LinnikAreas.TuranOther
