import Mathlib
import Submission.Work.FIArea6Hecke.R.levelHeckeDefs

namespace Work.FIArea6Hecke.R

set_option linter.unusedVariables false

/-- Given the Mellin identity `mellin f s = Γ(s) π^{-s} L(s - m/2)` on the half plane
`re s > 1 + m/2` and the identification `Ξ(t) = mellin f t` of the completed integral
`thetaXi` with the Mellin transform of `f`, the completed `L`-function `thetaLam` agrees with
`(√B/π)^s Γ(s + m/2) L(s)` there. This is the arithmetic heart of the converse direction of
Hecke's functional equation: the theta law supplies the Mellin identity for `f`, and the
theta/Mellin engine (`thetaLam = (√B)^s π^{m/2} Ξ(s + m/2)`) converts it into the completed
`L`-function.

The proof is a direct computation. Put `t = s + m/2`, so that `re t = re s + m/2 > 1 + m/2`
and both hypotheses may be evaluated at `t`. Then

  `Λ(s) = (√B)^s π^{m/2} Ξ(t) = (√B)^s π^{m/2} · Γ(t) π^{-t} L(s)`,

and the two complex-power identities `π^{m/2} π^{-t} = π^{-s} = ((π)^s)⁻¹` together with
`(√B/π)^s = (√B)^s ((π)^s)⁻¹` (from `div_cpow_ofReal_nonneg`) collapse this to
`(√B/π)^s Γ(s + m/2) L(s)`. -/
theorem thetaLamAgree (B : ℝ) (hB : 0 < B) (f : ℝ → ℂ) (m : ℕ) (A : ℂ) (L : ℂ → ℂ)
    (hmellin : ∀ s : ℂ, 1 + (m : ℝ) / 2 < s.re →
      mellin f s = Complex.Gamma s * ((Real.pi : ℂ) ^ (-s)) * L (s - (m : ℂ) / 2))
    (hXi : ∀ t : ℂ, thetaXi B f m A t = mellin f t) :
    ∀ s : ℂ, 1 + (m : ℝ) / 2 < s.re →
      thetaLam B f m A s = ((Real.sqrt B / Real.pi : ℝ) : ℂ) ^ s *
        Complex.Gamma (s + (m : ℂ) / 2) * L s := by
  intro s hs
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  -- Real part of `t = s + m/2`.
  have hre : (s + (m : ℂ) / 2).re = s.re + (m : ℝ) / 2 := by
    rw [Complex.add_re]
    congr 1
    rw [show (m : ℂ) / 2 = ((m : ℝ) / 2 : ℂ) by push_cast; ring]
    simp
  have hm0 : (0 : ℝ) ≤ (m : ℝ) / 2 := by positivity
  have ht : 1 + (m : ℝ) / 2 < (s + (m : ℂ) / 2).re := by rw [hre]; linarith
  have hmem := hmellin (s + (m : ℂ) / 2) ht
  have hx := hXi (s + (m : ℂ) / 2)
  have hsub : s + (m : ℂ) / 2 - (m : ℂ) / 2 = s := by ring
  -- `π^{m/2} · π^{-(s+m/2)} = (π^s)⁻¹`.
  have hkey : (Real.pi : ℂ) ^ ((m : ℂ) / 2) * (Real.pi : ℂ) ^ (-(s + (m : ℂ) / 2))
      = ((Real.pi : ℂ) ^ s)⁻¹ := by
    have h1 : (Real.pi : ℂ) ^ ((m : ℂ) / 2 + (-(s + (m : ℂ) / 2)))
        = (Real.pi : ℂ) ^ ((m : ℂ) / 2) * (Real.pi : ℂ) ^ (-(s + (m : ℂ) / 2)) :=
      Complex.cpow_add _ _ hpi
    rw [← h1]
    rw [show (m : ℂ) / 2 + (-(s + (m : ℂ) / 2)) = -s by ring]
    exact Complex.cpow_neg _ _
  -- `(√B/π)^s = (√B)^s · ((π)^s)⁻¹`.
  have hR : ((Real.sqrt B / Real.pi : ℝ) : ℂ) ^ s
      = ((Real.sqrt B : ℝ) : ℂ) ^ s * (((Real.pi : ℂ) ^ s))⁻¹ := by
    rw [Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg (Real.sqrt_nonneg B) Real.pi_pos.le s,
      div_eq_mul_inv]
  rw [thetaLam, hx, hmem, hsub, hR, ← hkey]
  ring

end Work.FIArea6Hecke.R
