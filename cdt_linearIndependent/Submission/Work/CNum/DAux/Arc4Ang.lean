import Mathlib
import Submission.Work.CNum.Basic
import Submission.Work.CNum.WfunArc4
import Submission.Work.CNum.Wfun_exp
import Submission.Work.CNum.CuspPoints
import Submission.Work.CNum.exp_phi_eq
import Submission.Work.CNum.Arc4Angle

/-!
# `Work.CNum.DAux.Arc4Ang`

The value of the Theorem-C contour map `ψ_C` on the fourth arc, i.e. for `z = e^{iθ}`
with `θ - 2π ∈ (-α, α)` (`α = alpR` the cusp half-angle):

`ψ_C (e^{iθ}) = (3/4) · e^{i(4π - φ(2π - θ))}`.

Proof.  Put `s = θ - 2π ∈ (-α, α)`.  Since `e^{iθ} = e^{is}` and `ψ_C = (3/4) Wfun`, the left
side is `(3/4) Wfun(e^{is}) = (3/4) e^{iφ(s)}` by `exp_phi_eq`.  On the other side
`2π - θ = -s` and `φ(-s) = 2π - φ(s)` (`phiR_neg`, from `P(-s) = P(s)`, `Q(-s) = -Q(s)` and
`arctan` odd), so `4π - φ(2π - θ) = 2π + φ(s)`, and `e^{i(2π + φ(s))} = e^{iφ(s)}`.
-/

namespace Work.CNum.DAux

open Work.CNum

/-- `e^{i(x + 2π)} = e^{ix}`. -/
lemma exp_I_add_two_pi (x : ℝ) :
    Complex.exp (Complex.I * ((x + 2 * Real.pi : ℝ) : ℂ)) = Complex.exp (Complex.I * (x : ℂ)) := by
  have h : Complex.I * ((x + 2 * Real.pi : ℝ) : ℂ)
      = Complex.I * (x : ℂ) + 2 * Real.pi * Complex.I := by
    push_cast; ring
  rw [h, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- `φ(-θ) + φ(θ) = 2π`: it suffices that `P` is even and `Q` is odd. -/
lemma phiR_neg (θ : ℝ) : phiR (-θ) = 2 * Real.pi - phiR θ := by
  have hPR : PR (-θ) = PR θ := by rw [PR, PR, Real.cos_neg]
  have hQR : QR (-θ) = -QR θ := by
    rw [QR, QR, show -θ / 2 = -(θ / 2) by ring, Real.sin_neg]
    ring
  simp only [phiR]
  rw [hPR, hQR]
  rw [show -QR θ / PR θ = -(QR θ / PR θ) by rw [neg_div]]
  rw [Real.arctan_neg]
  ring

theorem Arc4Ang {θ : ℝ} (h : θ - 2 * Real.pi ∈ Set.Ioo (-Work.CNum.alpR) Work.CNum.alpR) : Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ : ℂ))) = (3 / 4 : ℂ) * Complex.exp (Complex.I * ((4 * Real.pi - Work.CNum.phiR (2 * Real.pi - θ) : ℝ) : ℂ)) := by
  set s : ℝ := θ - 2 * Real.pi with hs
  have hsIoo : s ∈ Set.Ioo (-Work.CNum.alpR) Work.CNum.alpR := by rw [hs]; exact h
  have hθs : θ = s + 2 * Real.pi := by rw [hs]; ring
  have h2pi : 2 * Real.pi - θ = -s := by rw [hθs]; ring
  have hexp : Complex.exp (Complex.I * (θ : ℂ)) = Complex.exp (Complex.I * (s : ℂ)) := by
    rw [hθs]; exact exp_I_add_two_pi s
  have harg : (4 * Real.pi - Work.CNum.phiR (2 * Real.pi - θ) : ℝ)
      = 2 * Real.pi + Work.CNum.phiR s := by
    rw [h2pi, phiR_neg]; ring
  rw [hexp, harg, psiC_eq_threequarters_Wfun, ← exp_phi_eq hsIoo]
  congr 1
  rw [show Complex.I * ((2 * Real.pi + Work.CNum.phiR s : ℝ) : ℂ)
      = Complex.I * (Work.CNum.phiR s : ℂ) + 2 * Real.pi * Complex.I by push_cast; ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

end Work.CNum.DAux
