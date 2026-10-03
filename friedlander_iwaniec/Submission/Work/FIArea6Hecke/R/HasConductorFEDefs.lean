import Mathlib
import Submission.Work.FIArea5.S16Hecke.Defs

/-! The conclusion of the conductor-normalised Hecke functional equation, as a `Prop`. -/

namespace Work.FIArea6Hecke.R

open scoped BigOperators

/-- The conclusion of the target: there are `X ∈ [1,4d]`, a finite set `S` of primes `p | 4d`,
numbers `c₁,c₂` with `‖cᵢ(p)‖ = 1` or `cᵢ(p) = 0` on `S`, and an entire `Φ` with
`Φ(s) = W*conj(Φ(conj(1-s)))`, `W ≠ 0`, agreeing with
`(X/π)^s Γ(s+|m|/2) L(s,ψ_χ) ∏_{p∈S}((1-c₁(p)p^{-s})(1-c₂(p)p^{-s}))^{-1}`
on `re s > 1+|m|/2`. -/
def HasConductorFE (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) : Prop :=
  ∃ (X : ℝ) (c₁ c₂ : ℕ → ℂ) (S : Finset ℕ) (Phi : ℂ → ℂ) (W : ℂ),
    1 ≤ X ∧ X ≤ 4 * (d : ℝ) ∧
    (∀ p ∈ S, Nat.Prime p ∧ p ∣ 4 * d ∧ (‖c₁ p‖ = 1 ∨ c₁ p = 0) ∧ (‖c₂ p‖ = 1 ∨ c₂ p = 0)) ∧
    W ≠ 0 ∧ AnalyticOn ℂ Phi Set.univ ∧
    (∀ s : ℂ, Phi s = W * star (Phi (star (1 - s)))) ∧
    (∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
      Phi s = ((X / Real.pi : ℝ) : ℂ) ^ s *
        Complex.Gamma (s + ((|(m : ℝ)| / 2 : ℝ) : ℂ)) *
        Work.FIArea5.S16Hecke.heckeLSeries chi m s *
        ∏ p ∈ S, ((1 - c₁ p * ((p : ℂ) ^ (-s))) * (1 - c₂ p * ((p : ℂ) ^ (-s))))⁻¹)

end Work.FIArea6Hecke.R
