import Mathlib
import Submission.Work.RPV.Defs
import Submission.Work.RPV.chordPS_circle_stdZ

/-!
# The chord of the unit circle at any phase lift lies on the zero section

`chordPS z w a` keeps the phase `a` as the angle coordinate `q₂`, but the zero section
`Zsec` is the set of points with zero momentum `(p₁, p₂)`.  Here `p₁ = Re (e^{-ia} u)`
with `u = (z+w)/√2` and `p₂ = (‖z‖² + ‖w‖²)/2 - 1`.

For the chord `(e^{i(t+r)}, e^{i(t-r)})` of the unit circle the momentum part is zero
exactly at the phases `a ≡ t + π/2 (mod 2π)`.  Indeed the direction of this chord is
`π/2` off the midpoint direction `t`, so the shifted midpoint `e^{-ia} u` is purely
imaginary.  `Work.RPV.chordPS_circle_stdZ` computes this at the specific lift
`a = t + π/2`; the present lemma shows the same conclusion for *any* real lift `a` of
that phase, i.e. any `a` with `e^{ia} = e^{i(t+π/2)}`, which is what callers of the
generating-function route actually have in hand.
-/

open Complex Real

namespace Work.RPV

theorem chordPS_unit_phase_mem_Zsec (t r a : ℝ)
    (h : Complex.exp ((a : ℂ) * Complex.I) = Complex.exp (((t + Real.pi / 2 : ℝ)) * Complex.I)) :
    Work.RPV.chordPS (Complex.exp (((t + r : ℝ)) * Complex.I))
      (Complex.exp (((t - r : ℝ)) * Complex.I)) a ∈ Work.RPV.Zsec := by
  -- Two phase lifts `a` and `t + π/2` of the same angle give the same inverse phase.
  have hphase : Complex.exp (-(a : ℂ) * Complex.I)
      = Complex.exp (-(((t + Real.pi / 2 : ℝ)) : ℂ) * Complex.I) := by
    have hl : Complex.exp (-(a : ℂ) * Complex.I) =
        (starRingEnd ℂ) (Complex.exp ((a : ℂ) * Complex.I)) := by
      rw [← Complex.exp_conj]
      congr 1
      rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
    have hr : Complex.exp (-(((t + Real.pi / 2 : ℝ)) : ℂ) * Complex.I) =
        (starRingEnd ℂ) (Complex.exp ((((t + Real.pi / 2 : ℝ)) : ℂ) * Complex.I)) := by
      rw [← Complex.exp_conj]
      congr 1
      rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
    rw [hl, hr, h]
  -- At the canonical lift `t + π/2`, the shifted midpoint is purely imaginary.
  have hre' : (Complex.exp (-(((t + Real.pi / 2 : ℝ)) : ℂ) * Complex.I) *
      ((Complex.exp (((t + r : ℝ)) * Complex.I) + Complex.exp (((t - r : ℝ)) * Complex.I)) /
        (Real.sqrt 2 : ℂ))).re = 0 := by
    have h1 := Work.RPV.chordPS_circle_stdZ t r
    have h2 := congrArg (fun x : Work.RPV.PS => x.2.1) h1
    simpa only [Work.RPV.chordPS, Work.RPV.stdZ] using h2
  have hp2 : (‖Complex.exp (((t + r : ℝ)) * Complex.I)‖ ^ 2 +
      ‖Complex.exp (((t - r : ℝ)) * Complex.I)‖ ^ 2) / 2 - 1 = 0 := by
    rw [Complex.norm_exp, Complex.norm_exp]
    norm_num
  simp only [Work.RPV.Zsec, Set.mem_ofPred_eq, Work.RPV.chordPS, Prod.mk_eq_zero]
  constructor
  · rw [hphase]; exact hre'
  · exact hp2

end Work.RPV
