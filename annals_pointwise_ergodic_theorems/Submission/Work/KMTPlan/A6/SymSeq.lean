/-
# The symbol of a kernel as a `1`-periodic function of the frequency

This module fixes the "sequence symbol" of a one-dimensional kernel `κ : ℤ → ℂ`,

  `symSeq κ x = ∑' p : ℤ, κ p * e(p x)`,   `e(z) = exp(2πiz)`,

i.e. the `1`-periodic function of the frequency `x` whose `j`-th Fourier coefficient
`coeff1 (symSeq κ) j = ∫₀¹ symSeq κ x * e(-j x) dx` is `κ j`
(`Work.KMTPlan.A6.SymToolbox.coeff1`).  For a bilinear convolution operator
`bilinOp K u v` (`Work.KMTAreas.A7.ModelOps`) with kernel `K`, the symbol of the corresponding
bilinear Fourier multiplier is the product of the symbols of its factors; this is the dictionary in
which the §6 model approximation of Krause--Mirek--Tao (Proposition `mod-approx`) is an estimate of
the *symbol* of the difference of the concrete kernel and the model kernel.

The concrete side of §6 is `bilinOp (kernComp (khalf N P) κ_F κ_G)`, whose symbol is
`symSeq κ_F(x) * symSeq κ_G(y) * (N⁻¹ ∑_{N/2 < n ≤ N} e(n x + P(n) y))`
(`SymConc_coeff` below): the last factor is precisely the discrete part of the paper's `M₀`
(`Work.KMTAreas.A7.M0`), and is to be compared with `m_Ẑ · m̃_N` on the model side.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.SymToolbox

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

open MeasureTheory intervalIntegral Polynomial
open scoped BigOperators ENNReal

noncomputable section

/-- The symbol of a one-dimensional kernel `κ : ℤ → ℂ`: the `1`-periodic function
`x ↦ ∑' p, κ p * e(p x)`. -/
noncomputable def symSeq (κ : ℤ → ℂ) (x : ℝ) : ℂ :=
  ∑' p : ℤ, κ p * eeC (p * x)

/-- The symbol of a two-dimensional kernel `K : ℤ → ℤ → ℂ`: the function
`(x,y) ↦ ∑' p, ∑' q, K p q * e(p x + q y)`, `1`-periodic in each variable. -/
noncomputable def symSeq2 (K : ℤ → ℤ → ℂ) (x y : ℝ) : ℂ :=
  ∑' p : ℤ, ∑' q : ℤ, K p q * eeC (p * x + q * y)

/-- The (discrete part of the) symbol of the halved average `Ã_N`: the trigonometric polynomial
`(x,y) ↦ N⁻¹ ∑_{N/2 < n ≤ N} e(n x + P(n) y)`.  This is the `ξ`-part of the paper's discrete
average `E_{n ∈ [N]} e(α₁n+α₂P(n)) e(ξ₁n+ξ₂P(n)) 1_{n>N/2}` at `α₁ = α₂ = 0`. -/
noncomputable def halfSym (N : ℕ) (P : ℤ[X]) (x y : ℝ) : ℂ :=
  ((N : ℂ))⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N, eeC ((n : ℝ) * x + ((P.eval (n : ℤ) : ℤ) : ℝ) * y)

end

end Work.KMTPlan.A6
