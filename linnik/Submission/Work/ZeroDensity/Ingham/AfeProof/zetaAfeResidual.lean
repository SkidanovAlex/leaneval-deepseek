import Mathlib
import Submission.Work.ZeroDensity.Ingham.zetaAfeDefs
import Submission.Work.ZeroDensity.Ingham.AfeProof.afeResidualBound

/-!
# The residual of the approximate functional equation for `ζ` at the balanced point

`Work.ZeroDensity.Ingham.AfeProof.zetaAfeResidual`:

`∃ C, ∀ t ≥ 1, ‖ζ(1/2+it) - Σ_{n ≤ afeNt t} n^{-(1/2+it)} - χ(1/2+it)·Σ_{m ≤ afeMt t} m^{(1/2+it)-1}‖ ≤ C`,

the sharp approximate functional equation in *residual* form.  The proof is assembled in
`afeResidualBound` from the exact Euler–Maclaurin/Fourier identity `afeIdentity` and the
resonance estimate `afeResonanceSumBound`.
-/

namespace Work.ZeroDensity.Ingham.AfeProof

theorem zetaAfeResidual : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
    ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)
      - (∑ n ∈ Finset.Icc 1 (Work.ZeroDensity.Ingham.afeNt t),
            (n : ℂ) ^ (-((1 / 2 : ℂ) + (t : ℂ) * Complex.I)))
      - Work.ZeroDensity.Ingham.zetaChi ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)
          * (∑ m ∈ Finset.Icc 1 (Work.ZeroDensity.Ingham.afeMt t),
              (m : ℂ) ^ (((1 / 2 : ℂ) + (t : ℂ) * Complex.I) - 1))‖ ≤ C :=
  afeResidual_bound

end Work.ZeroDensity.Ingham.AfeProof
