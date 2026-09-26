import Mathlib
import Submission.Work.Asymptotics.HalfFunnel.lowBadDefs
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.KfunAuxDefs
import Submission.Work.Rigidity.LambdaBasic

/-!
# Definitions for the spike bound `lowBad_Tspike_bound`

This file collects the definitions used by the statement and proof of
`Work.Asymptotics.HalfFunnel.lowBad_Tspike_bound`: the translate-pole location `zpole τ = τ - n`
(`n = tsign τ`), and the explicit auxiliary functions `TpF`, `PsiF` in the exact factorization
of the difference of the modular `j`-invariant in terms of `λ`-differences.

The two analytic inputs about the bad-line region are

* `Work.Asymptotics.HalfFunnel.jBranch_lower` : the two-branch lower bound
  `c ‖z - z₀‖ ‖z - S z₀‖ ≤ ‖j z - j z₀‖` on the region, and
* `Work.Asymptotics.HalfFunnel.AfunFun_window_bound` : uniform boundedness of `AfunFun`
  on the region.
-/

noncomputable section

namespace Work.Asymptotics.HalfFunnel

open Work.Kernels
open UpperHalfPlane

/-- The translate-pole location `z₀ = τ - n` (`n = tsign τ`) attached to a point `τ` of the
half-plane: the pole of `z ↦ K^{(d)}(τ,z)` crossed by the contour point `it ≈ i·Im τ`. -/
def zpole (τ : ℍ) : ℍ := (-(tsign τ : ℝ)) +ᵥ τ

/-- The auxiliary polynomial `T` of the exact factorization of the `j`-difference in terms of
`λ`-differences: `(A - B) T(A,B) = (3/4+A)³(1/4-B)² - (3/4+B)³(1/4-A)²`. -/
def TpF (A B : ℂ) : ℂ :=
  81 / 256 - 9 / 32 * (A + B) + 1 / 16 * (A ^ 2 + B ^ 2) - 11 / 4 * (A * B)
    - 1 / 2 * (A * B * (A + B)) + A ^ 2 * B ^ 2

/-- The explicit factor `Ψ` in the exact factorization
`j u - j v = (λ u - λ v) (λ u + λ v - 1) Ψ (λ u - 1/2) (λ v - 1/2)` of the `j`-difference;
`Ψ 0 0 = 20736 ≠ 0`. -/
def PsiF (a b : ℂ) : ℂ :=
  256 * TpF (a ^ 2) (b ^ 2) / ((1 / 4 - a ^ 2) ^ 2 * (1 / 4 - b ^ 2) ^ 2)

/-- The numerator
`M(z) = A(τ,z)(z - z₀) + (n/2π)(j z - j z₀)`, `z₀ = zpole τ = τ - tsign τ`, `z = i t`:
the pole-subtracted kernel is `-M / ((j z - j z₀)(z - z₀))`, and `M` vanishes to second order at
`z₀` and to first order at `S z₀`. -/
def Mnum (ℓ : LogLambdaData) (d : ℕ) (τ : ℍ) (t : ℝ) (ht : 0 < t) : ℂ :=
  AfunFun ℓ d τ (imagAxis t ht)
      * (((imagAxis t ht : ℍ) : ℂ) - ((zpole τ : ℍ) : ℂ))
    + ((tsign τ : ℂ) / (2 * (Real.pi : ℂ)))
      * (jInvariantFun (imagAxis t ht) - jInvariantFun (zpole τ))

end Work.Asymptotics.HalfFunnel
