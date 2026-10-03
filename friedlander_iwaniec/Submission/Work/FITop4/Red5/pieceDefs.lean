/-
# `Submission.Work.FITop4.Red5.pieceDefs` — the (4.13)+(5.13) piece coefficient

The coefficient `β_z` of the Friedlander–Iwaniec §§4–5.2 reduction at one polar cell: the product
of the angular mollifier `q` (at the cell's angle), the radial mollifier `p` (at `|z|²`), the
Möbius factor `μ(|z|²)` and the truncated divisor factor `γ(|z|²;C)`, supported on the polar box
(5.14) with `(z,Π)=1` (5.8) and `τ(|z|²) ≤ τ` (5.9).  This is the `β` of `IsBetaCoeff`.
-/
import Mathlib
import Submission.Work.FITop4.Red5.Vocab

set_option autoImplicit false

namespace Work.FITop4.Red5

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The (4.13)+(5.13) coefficient built from the angular mollifier `q` and the radial mollifier
`p`, at the polar cell `(Pa, φ)`. -/
def pieceCoeff (Pa : Work.FITop.Params) (φ : ℝ) (q p : ℝ → ℝ) : GaussianInt → ℂ :=
  fun z => if InPolarBox Pa φ z ∧ NoSmallPrimes Pa z ∧
      (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ)
    then ((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
            * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
            * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
    else 0

/-- `pieceCoeff` is an `IsBetaCoeff` as soon as `q, p` satisfy the mollifier clauses. -/
lemma pieceCoeff_isBetaCoeff {Pa : Work.FITop.Params} {φ : ℝ} {q p : ℝ → ℝ}
    (hq : ContDiff ℝ 2 q) (hq0 : ∀ α, 0 ≤ q α) (hq1 : ∀ α, q α ≤ 1)
    (hqsup : ∀ α, q α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * Pa.θ)
    (hqd : ∀ j, j ≤ 2 → ∀ α, |iteratedDeriv j q α| ≤ cMoll j * Pa.θ ^ (-(j : ℝ)))
    (hp : ContDiff ℝ 2 p) (hp0 : ∀ u, 0 ≤ p u) (hp1 : ∀ u, p u ≤ 1)
    (hpsup : ∀ u, p u ≠ 0 → Pa.N < u ∧ u ≤ (1 + Pa.θ) * Pa.N)
    (hpd : ∀ j, j ≤ 2 → ∀ u, |iteratedDeriv j p u| ≤ cMoll j * (Pa.θ * Pa.N) ^ (-(j : ℝ))) :
    IsBetaCoeff Pa φ (pieceCoeff Pa φ q p) := by
  refine ⟨q, p, hq, hp, hq0, hq1, hqsup, hqd, hp0, hp1, hpsup, hpd, ?_⟩
  intro z
  rfl

end
end Work.FITop4.Red5
