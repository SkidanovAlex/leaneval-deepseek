import Mathlib
import ChallengeDeps
import Submission.Work.Interfaces.Basic

/-!
# PARAM area: the basic conjugacy

`cOfLam λ = λ/2 - λ²/4` is the parameter `c` for which `Tc c` has a fixed point of multiplier
`λ`.  Under the change of variable `z = x + λ/2` the map `Tc (cOfLam λ)` becomes
`Q λ x = λ x + x²`.  The critical point `0` of `Tc c` corresponds to `x = -λ/2`.

This file collects the (purely algebraic) bookkeeping used by every other module of the
PARAM area.
-/

namespace Work.Param

open MandelDim Filter Topology
open LeanEval.Dynamics.MandelbrotBoundary

noncomputable section

/-- The quadratic map in Koenigs coordinates: `Q λ x = λ x + x²`. -/
def Q (l : ℂ) (x : ℂ) : ℂ := l * x + x ^ 2

/-- The parameter whose fixed point has multiplier `λ`: `cOfLam λ = λ/2 - λ²/4`. -/
def cOfLam (l : ℂ) : ℂ := l / 2 - l ^ 2 / 4

/-- `cOfAlpha` is `cOfLam` applied to `exp (2πiα)`. -/
theorem cOfAlpha_eq (α : ℂ) :
    cOfAlpha α = cOfLam (Complex.exp (2 * Real.pi * Complex.I * α)) := by
  have h : Complex.exp (4 * Real.pi * Complex.I * α)
      = Complex.exp (2 * Real.pi * Complex.I * α) ^ 2 := by
    have harg : (4 : ℂ) * Real.pi * Complex.I * α
        = (2 : ℕ) * (2 * Real.pi * Complex.I * α) := by ring
    rw [harg, Complex.exp_nat_mul]
  simp only [cOfAlpha, cOfLam, h]

/-- The conjugacy: `Tc (cOfLam λ) (x + λ/2) = Q λ x + λ/2`. -/
theorem Tc_cOfLam_apply (l x : ℂ) : Tc (cOfLam l) (x + l / 2) = Q l x + l / 2 := by
  simp only [Tc, Q, cOfLam]; ring

/-- Iterated version of the conjugacy. -/
theorem Tc_cOfLam_iterate (l x : ℂ) (n : ℕ) :
    (Tc (cOfLam l))^[n] (x + l / 2) = (Q l)^[n] x + l / 2 := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply', Tc_cOfLam_apply]

/-- The critical orbit of `Tc (cOfLam λ)` is the orbit of `-λ/2` under `Q λ`, shifted by `λ/2`. -/
theorem Tc_cOfLam_iterate_zero (l : ℂ) (n : ℕ) :
    (Tc (cOfLam l))^[n] 0 = (Q l)^[n] (-(l / 2)) + l / 2 := by
  have h : (-(l / 2)) + l / 2 = (0 : ℂ) := by ring
  conv_lhs => rw [← h]
  exact Tc_cOfLam_iterate l (-(l/2)) n

end

end Work.Param
