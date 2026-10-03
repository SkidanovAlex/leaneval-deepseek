/-
# `Submission.Work.FIArea6Road.TailLogNStep`

**The logarithmic comparison `(log x)/4 < log N`.**

The `Params` set-up of `Work.FITop.Defs` records the lower end of the range (4.6) as
`hNlo : x^{1/4+η} < N` with `η > 0` (`hη`) and `x ≥ 3` (`hx`).  Taking logarithms,
`log N > (1/4 + η)·log x > (1/4)·log x`, since `log x > 0`.  This is the "tail logarithm"
step used when comparing the tail of the exponential series in the §16 heart with the
factor `N^{-1/4} = e^{-(log N)/4} ≪ x^{-1/4}`.

The proof is pure real analysis: `Real.log_lt_log` (monotonicity of `log`), `Real.log_rpow`
and `Real.log_pos`.
-/
import Mathlib
import Submission.Work.FITop.Defs

namespace Work.FIArea6Road

open Work.FITop

theorem TailLogNStep (Pa : Work.FITop.Params) :
    Real.log (Pa.x : ℝ) / 4 < Real.log Pa.N := by
  -- `x ≥ 3 > 1`, so `log x > 0` and `x > 0`.
  have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
  have hx1 : (1 : ℝ) < (Pa.x : ℝ) := by linarith
  have hxpos : (0 : ℝ) < (Pa.x : ℝ) := by linarith
  have hlogx : 0 < Real.log (Pa.x : ℝ) := Real.log_pos hx1
  -- (4.6), lower end: `x^{1/4+η} < N`, and `x^{1/4+η} > 0`, so `log` is monotone.
  have hpos : (0 : ℝ) < (Pa.x : ℝ) ^ ((1 : ℝ) / 4 + Pa.η) := Real.rpow_pos_of_pos hxpos _
  have hlt : Real.log ((Pa.x : ℝ) ^ ((1 : ℝ) / 4 + Pa.η)) < Real.log (Pa.N) :=
    Real.log_lt_log hpos Pa.hNlo
  rw [Real.log_rpow hxpos] at hlt
  -- `log N > (1/4 + η)·log x > (1/4)·log x`.
  nlinarith [hlt, hlogx, Pa.hη]

end Work.FIArea6Road
