/-
# The fibre vocabulary of the §6 single-scale mass bound (`HiMassBound`)

This module fixes the objects in which the *single-scale* `ℓ¹(ℤ²)` mass bound
`Work.KMTAreas.A7.HiMassBound` of the §6 model approximation is proved:

* `bumpFT φ x = ∫ θ, φ θ · e(xθ)` — the inverse Fourier transform of a bump (the paper's `φ̂`,
  `φ̃̂`); it is the object whose lattice samples carry the bump's mass;
* `psiP P φ₁ φ₂ p u = φ̂₁(u − p₁) · φ̂₂(P(u) − p₂)` — the `p`-th *fibre function* of the two bumps
  along the polynomial curve `u ↦ (u, P(u))`;
* `acCoefW` — the arithmetic character `n ↦ e(α₁n + α₂P(n))` (the `arithW` of
  `ModelApproxCore_M0_defs`, recalled here to keep the statements self-contained).

The per-fibre Fourier coefficient of the single-scale symbol difference `M₀ = weylAvg − m_Ẑ m̃`
(`ModelApproxDefs.M0`) is

  `∫∫ φ_N(θ₁) φ̃_N(θ₂) M₀(θ₁,θ₂) e(−p·θ) dθ`
     `= N⁻¹ Σ_{r<q} a(r) · ( Σ_{n ≡ r (q), N/2<n≤N} Ψ_p(n) − q⁻¹ ∫_{N/2}^N Ψ_p )`,

the *arithmetic-quadrature identity* `Work.KMTAreas.A7.hiFibreCoeff_ident`, whose right-hand side
is a discrepancy between a Riemann sum and an integral — that is where the gain `N⁻¹` of the §6
approximation comes from.  The lemmas `Work.KMTAreas.A7.sharpBumpMassSum` (the `ℓ¹(ℤ)` mass of
the lattice samples of `bumpFT φ_N`, `bumpFT φ_N'`, `bumpFT φ_N''` and their `φ̃` analogues) are
the only analytic input besides the elementary quadrature comparison.

The normalisation: the bump `varphiN N k₁` has frequency support of width `2^{k₁}/N` (so
`a := 2^{k₁}/N ≤ 1` under `mainRegime`, which is what makes the mass sums of the derivatives small);
the bump `varphitildeN d N k₂` has support of width `2^{d k₂}/N^d` (so `w := 2^{d k₂}/N^d ≤ 1`).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.ModelApproxHiKernels
import Submission.Work.A7.ModelApproxCore_M0_defs
import Submission.Work.KMTAreas.A7.ModelApproxM0Deriv

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger

/-- **The inverse Fourier transform of a bump**: `bumpFT φ x = ∫ θ, φ θ * e(x θ)`.
For `φ = varphiN N k₁` this is the paper's `φ̂_N`. -/
noncomputable def bumpFT (φ : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ θ : ℝ, φ θ * ee (x * θ)

/-- **The `p`-th fibre function** of the two bumps along the curve `u ↦ (u, P(u))`:
`psiP P φ₁ φ₂ p u = bumpFT φ₁ (u − p₁) · bumpFT φ₂ (P(u) − p₂)`. -/
noncomputable def psiP (P : ℤ[X]) (φ₁ φ₂ : ℝ → ℂ) (p : ℤ × ℤ) (u : ℝ) : ℂ :=
  bumpFT φ₁ (u - (p.1 : ℝ)) * bumpFT φ₂ (PevalR P u - (p.2 : ℝ))

/-- The arithmetic character `n ↦ e(α₁ n + α₂ P(n))` (the `arithW` of
`ModelApproxCore_M0_defs`, in the `acCoef` form of `KMTPlan.A6`). -/
noncomputable def acCoefW (P : ℤ[X]) (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) (n : ℤ) : ℂ :=
  fourier (T := 1) n α₁ * fourier (T := 1) (P.eval n) α₂

/-- The `psiP` of the two bumps of the §6 approximation, in the exact form used by the mass
bound: `φ₁ = varphiN N k₁`, `φ₂ = varphitildeN P.natDegree N k₂`. -/
noncomputable def psiHi (P : ℤ[X]) (N k₁ k₂ : ℕ) (p : ℤ × ℤ) (u : ℝ) : ℂ :=
  psiP P (varphiN N k₁) (varphitildeN P.natDegree N k₂) p u

end

end Work.KMTAreas.A7
