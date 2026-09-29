import Mathlib
import Submission.Work.CNum.Basic
import Submission.Work.CNum.Wfun_exp
import Submission.Work.CNum.AlpBound

namespace Work.CNum

/-- `Wfun` on the unit circle, on the arc around `θ = 2π`: for `θ` with
`θ - 2π ∈ (-alpR, alpR)`, i.e. on the cusp arc but reached from the other side,
`Wfun (e^{iθ}) = ((P(θ) - iQ(θ)) e^{iθ/2})/d`.

This is `Wfun_exp` at `θ - 2π`, using
`e^{iθ} = e^{i(θ-2π)}`, `P(θ) = P(θ-2π)`, `Q(θ) = -Q(θ-2π)` and `e^{iθ/2} = -e^{i(θ-2π)/2}`. -/
theorem WfunArc4 {θ : ℝ} (h : θ - 2 * Real.pi ∈ Set.Ioo (-Work.CNum.alpR) Work.CNum.alpR) :
    Work.CNum.Wfun (Complex.exp (Complex.I * (θ : ℂ))) =
      (((Work.CNum.PR θ : ℂ) - Complex.I * (Work.CNum.QR θ : ℂ)) *
        Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ))) / (Work.CNum.dR : ℂ) := by
  set φ : ℝ := θ - 2 * Real.pi with hφdef
  have hφ : φ ∈ Set.Ioo (-Work.CNum.alpR) Work.CNum.alpR := by rw [hφdef]; exact h
  have hφθ : θ = φ + 2 * Real.pi := by rw [hφdef]; ring
  have hcos : Real.cos θ = Real.cos φ := by rw [hφθ, Real.cos_add_two_pi]
  have hsinθ : Real.sin θ = Real.sin φ := by rw [hφθ, Real.sin_add_two_pi]
  have hexp : Complex.exp (Complex.I * (θ : ℂ)) = Complex.exp (Complex.I * (φ : ℂ)) := by
    rw [mul_comm Complex.I (θ : ℂ), mul_comm Complex.I (φ : ℂ)]
    rw [Complex.exp_ofReal_mul_I θ, Complex.exp_ofReal_mul_I φ, hcos, hsinθ]
  have hPR : Work.CNum.PR θ = Work.CNum.PR φ := by unfold Work.CNum.PR; rw [hcos]
  have hQR : Work.CNum.QR θ = -Work.CNum.QR φ := by
    unfold Work.CNum.QR
    rw [show θ / 2 = φ / 2 + Real.pi by rw [hφθ]; ring, Real.sin_add_pi]
    ring
  have hexp2 : Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ)) =
      - Complex.exp (Complex.I * ((φ / 2 : ℝ) : ℂ)) := by
    have hhalf : θ / 2 = φ / 2 + Real.pi := by rw [hφθ]; ring
    rw [hhalf]
    have hsplit : Complex.I * (((φ / 2 + Real.pi : ℝ)) : ℂ)
        = Complex.I * ((φ / 2 : ℝ) : ℂ) + ((Real.pi : ℂ) * Complex.I) := by
      push_cast; ring
    rw [hsplit, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  rw [hexp, Work.CNum.Wfun_exp hφ]
  rw [hPR, hQR, hexp2]
  push_cast
  ring

end Work.CNum
