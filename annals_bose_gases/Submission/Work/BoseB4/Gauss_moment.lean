import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.BoseB4.Coherent
import Submission.Work.BoseB4.polarPow
import Submission.Work.BoseB4.radialMoment
import Submission.Work.BoseB4.thetaInt
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.Gauss_moment` — the moments of the Gaussian measure `dν(z) = e^{-|z|²} d²z/π`

FS §8.3 resolve the identity on the condensate mode in coherent states
`|z⟩ = e^{z a₀†}Ω`, with `dν(z) = e^{-|z|²} d²z/π`.  The `c`-number substitution
turns `a₀` into `z` and `a₀†` into `z̄`, so the integrals FS need are the *moments*

    `∫_ℂ z^A z̄^B dν(z) = δ_{A,B} A!`.

This file computes them.  The computation is polar coordinates: with `z = r e^{iθ}`,

    `∫_ℂ z^A z̄^B dν(z) = (1/π) (∫_{r>0} r^{A+B+1} e^{-r²} dr)
                                  (∫_{-π}^{π} e^{i(A-B)θ} dθ)`,

the angular integral vanishing unless `A = B`, and the radial one being `A!/2`.
The three ingredients are proved separately:
`Work.BoseB4.thetaInt` (angular), `Work.BoseB4.radialMoment` (radial) and
`Work.BoseB4.polarPow` (the purely algebraic rewriting `z^A z̄^B = r^{A+B} e^{i(A-B)θ}`
on the polar-coordinate side).
-/

noncomputable section

open MeasureTheory

namespace Work.BoseB4

/-- On the polar-coordinate side, the Gaussian weight only depends on the radius:
`e^{-‖r e^{iθ}‖²}/π = e^{-r²}/π`. -/
lemma gaussWeight_polarCoord_symm (p : ℝ × ℝ) :
    (gaussWeight (Complex.polarCoord.symm p) : ℝ) = Real.exp (-(p.1 ^ 2)) / Real.pi := by
  change Real.exp (-‖(Complex.polarCoord.symm p : ℂ)‖ ^ 2) / Real.pi
      = Real.exp (-(p.1 ^ 2)) / Real.pi
  rw [Complex.norm_polarCoord_symm, sq_abs]

/-- **The moments of the Gaussian measure** `dν(z) = e^{-|z|²} d²z/π`: only the "diagonal"
moments survive, and `∫ z^A z̄^A dν = A!`. -/
theorem Gauss_moment (A B : ℕ) :
    ∫ z : ℂ, z ^ A * (starRingEnd ℂ z) ^ B ∂(Work.BoseB4.gauss)
      = if A = B then ((A.factorial : ℕ) : ℂ) else 0 := by
  -- Write the integral against `gauss` as an integral against Lebesgue measure.
  rw [integral_gauss]
  set F : ℂ → ℂ := fun z => (gaussWeight z : ℝ) • (z ^ A * (starRingEnd ℂ z) ^ B) with hF
  -- The two one-variable factors of the polar-coordinate integrand.
  set f : ℝ → ℂ := fun r => (r : ℂ) ^ (A + B + 1) * ((Real.exp (-(r ^ 2)) / Real.pi : ℝ) : ℂ)
    with hf
  set g : ℝ → ℂ := fun θ => Complex.exp (((A : ℂ) - (B : ℂ)) * (θ : ℂ) * Complex.I) with hg
  -- Polar coordinates.
  rw [← Complex.integral_comp_polarCoord_symm F]
  rw [polarCoord_target]
  -- The integrand is a product of a function of `r` and a function of `θ`.
  have hpt : Set.EqOn (fun p : ℝ × ℝ => p.1 • F (Complex.polarCoord.symm p))
      (fun p : ℝ × ℝ => f p.1 * g p.2) (Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi) := by
    intro p hp
    change p.1 • ((gaussWeight (Complex.polarCoord.symm p) : ℝ) •
        ((Complex.polarCoord.symm p) ^ A * (starRingEnd ℂ (Complex.polarCoord.symm p)) ^ B))
      = f p.1 * g p.2
    rw [Complex.real_smul, Complex.real_smul, gaussWeight_polarCoord_symm p, polarPow A B p,
      hf, hg, pow_succ]
    ring_nf
  rw [setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) hpt]
  rw [MeasureTheory.Measure.volume_eq_prod, setIntegral_prod_mul]
  -- Angular integral: `∫_{-π}^{π} e^{i(A-B)θ} dθ`.
  have htheta : (∫ θ : ℝ in Set.Ioo (-Real.pi) Real.pi, g θ)
      = if A = B then ((2 * Real.pi : ℝ) : ℂ) else 0 := by
    rw [hg]
    have hk : ((A : ℂ) - (B : ℂ)) = (((A : ℤ) - (B : ℤ) : ℤ) : ℂ) := by push_cast; ring
    rw [hk, thetaInt]
    by_cases h : A = B
    · subst h
      simp
    · have h0 : ((A : ℤ) - (B : ℤ)) ≠ 0 := by omega
      simp [h0, h]
  -- Radial integral: pull out the constant `1/π`.
  have hrad : (∫ r : ℝ in Set.Ioi 0, f r)
      = (∫ r : ℝ in Set.Ioi 0, (r : ℂ) ^ (A + B + 1) * Complex.exp (-(r : ℂ) ^ 2))
        * ((Real.pi : ℂ))⁻¹ := by
    rw [hf]
    rw [show (fun r : ℝ => (r : ℂ) ^ (A + B + 1) * ((Real.exp (-(r ^ 2)) / Real.pi : ℝ) : ℂ))
        = (fun r : ℝ => ((r : ℂ) ^ (A + B + 1) * Complex.exp (-(r : ℂ) ^ 2))
            * ((Real.pi : ℂ))⁻¹) from by
      funext r
      rw [Complex.ofReal_div, Complex.ofReal_exp, div_eq_mul_inv]
      push_cast
      ring]
    rw [MeasureTheory.integral_mul_const]
  rw [htheta, hrad]
  by_cases h : A = B
  · rw [if_pos h, if_pos h]
    rw [show A + B + 1 = 2 * A + 1 by omega, radialMoment A]
    push_cast
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
  · simp [h]

end Work.BoseB4
