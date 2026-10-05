import Mathlib
import Submission.Work.RPB.Defs
import Submission.Work.RPB.B2.chordVec_circle

namespace Work.RPB.B5

/-- At time `τ = 0` the curve family is the unit circle, so the chord `(c 0 (t+r), c 0 (t-r))` has
direction `t + π/2`; hence the phase `a 0 t r` differs from `t + π/2` by an integer multiple of
`2π`, which is what the vanishing of `Complex.exp ((a 0 t r - (t + π/2)) * I)` says.  Only the
positive range `r ∈ (0, π/2)` is needed (there the chord is nonzero and `sin r > 0`). -/
theorem exp_chordPhase_zero_sub (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) {t r : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Complex.exp (((a 0 t r - (t + Real.pi / 2)) : ℝ) * Complex.I) = 1 := by
  have hr0 : 0 < r := hr.1
  have hrπ : r < Real.pi := by linarith [hr.2, Real.pi_pos]
  have hmem : r ∈ Set.Ioo (0 : ℝ) Real.pi := ⟨hr0, hrπ⟩
  have hsin : 0 < Real.sin r := Real.sin_pos_of_pos_of_lt_pi hr0 hrπ
  -- the chord of the unit circle, as an explicit multiple of `exp ((t + π/2) * I)`
  have hval : ((2 * Real.sin r : ℝ) : ℂ) * Complex.exp (((t + Real.pi / 2) : ℝ) * Complex.I)
      = Work.RPB.chordVec CI.c 0 t r := by
    rw [Work.RPB.B2.chordVec_circle CI.c CI.start t r]
    push_cast
    ring
  -- whose norm is `2 sin r`
  have hnorm : ‖Work.RPB.chordVec CI.c 0 t r‖ = 2 * Real.sin r := by
    rw [← hval, norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one,
      Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < 2 * Real.sin r)]
  have hne : ((2 * Real.sin r : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; linarith
  -- `IsChordPhase` says the chord is `‖chord‖ * exp (a * I)`; cancelling the positive factor
  -- identifies the two exponential directions
  have hdir := ha.2.1 0 (by norm_num) t r hmem
  rw [hnorm, ← hval] at hdir
  have hexp : Complex.exp (((t + Real.pi / 2) : ℝ) * Complex.I)
      = Complex.exp (a 0 t r * Complex.I) := mul_left_cancel₀ hne hdir
  have hsub : (((a 0 t r - (t + Real.pi / 2)) : ℝ) : ℂ) * Complex.I
      = a 0 t r * Complex.I - ((t + Real.pi / 2) : ℝ) * Complex.I := by
    push_cast; ring
  rw [hsub, Complex.exp_sub, hexp, div_self (Complex.exp_ne_zero _)]

end Work.RPB.B5
