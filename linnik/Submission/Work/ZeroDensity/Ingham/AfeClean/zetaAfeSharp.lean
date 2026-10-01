import Mathlib
import Submission.Work.ZeroDensity.Ingham.AfeProof.zetaAfeSharp

namespace Work.ZeroDensity.Ingham.AfeClean

/-- **The sharp approximate functional equation for `ζ` on the critical line** (Titchmarsh,
*The Theory of the Riemann Zeta-Function*, Thm 4.11): `∃ C > 0, ∀ t ≥ 1`,
`‖ζ(1/2+it)‖ ≤ C (1 + ‖Σ_{n ≤ ⌊√(t/2π)⌋₊+1} n^{-(1/2+it)}‖)`.  Proved (axiom-clean) in
`Submission.Work.ZeroDensity.Ingham.AfeProof.zetaAfeSharp`. -/
theorem zetaAfeSharp : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
    ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      C * (1 + ‖∑ n ∈ Finset.Icc 1 (⌊Real.sqrt (t / (2 * Real.pi))⌋₊ + 1),
        (n : ℂ) ^ (-((1 / 2 : ℂ) + (t : ℂ) * Complex.I))‖) :=
  Work.ZeroDensity.Ingham.AfeProof.zetaAfeSharp

end Work.ZeroDensity.Ingham.AfeClean
