/-
# `Work.FIArea6Hecke.R.ConductorThetaDefs`

Vocabulary for **Hecke's functional equation at general conductor** (see
`R/NOTES_FEStrictConductor.md` §12, which corrects §2/§11).

A strict character `χ` mod `4d` has a Hecke conductor `M ∣ (4d)` and a primitive partner `χ₀` on
`(ℤ[i]/M)^*` (`R/heckeConductorData`).  The Größencharacter is `ψ(z) = χ₀(z)(z/|z|)^m`, and the
target's normalisation is `X = √(N M)` — *not* `√(N(lcm((1+i)^3, M)))` — together with the finite
Euler correction at the primes `𝔭 ∣ (4d)`, `𝔭 ∤ M`.

The theta series whose Mellin transform is Hecke's completed `L`-function is the sum over **all**
of `ℤ[i] ∖ {0}` (and not over the primary coset `1 + (1+i)³ℤ[i]`, which omits the prime `(1+i)`):

  `allZTheta chi₀ m u = Σ_z χ₀(z) z^m e^{-πu|z|²}`,  `∫_0^∞ Θ(u)u^{s-1}du = 4π^{-s}Γ(s)L̃(s - m/2)`,

where `L̃(s) = ∏_{all 𝔭}(1 - ψ(𝔭)N𝔭^{-s})^{-1}` is the complete Hecke `L`-function.  Its theta
transformation law is at level `N M`, and its finite input is the Gauss sum `condGaussSum M chi₀`
(supported on `M ℤ[i]`, with the self-duality `conj(χ₀(γ̄))`).
-/
import Mathlib
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Work.FIArea5.S16Hecke.Defs
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea6Hecke.R.StrictConductorDefs

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open scoped BigOperators

noncomputable section

open Work.FIPlan

/-- `χ₀` is a **multiplicative character of `(ℤ[i]/M)^*` extended by zero off the units**:
multiplicative, `χ₀ 1 = 1`, bounded by `1`, `M`-periodic, and vanishing off `IsUnitMod M`.
This is `IsConductorPartner`'s partner clauses, isolated from the agreement clause. -/
def IsCharModStrict (M : GaussianInt) (chi₀ : GaussianInt → ℂ) : Prop :=
  chi₀ 1 = 1 ∧
  (∀ z w : GaussianInt, chi₀ (z * w) = chi₀ z * chi₀ w) ∧
  (∀ z : GaussianInt, ‖chi₀ z‖ ≤ 1) ∧
  (∀ z w : GaussianInt, M ∣ (z - w) → chi₀ z = chi₀ w) ∧
  (∀ z : GaussianInt, ¬ IsUnitMod M z → chi₀ z = 0)

/-- The conjugate Gaussian integer `γ̄ = γ.re - γ.im·i`. -/
def gconjInt (γ : GaussianInt) : GaussianInt := ⟨γ.re, -γ.im⟩

/-- **The all-`z` theta series** of the Größencharacter of `χ₀` and weight `m`:
`Θ(u) = Σ_{z ∈ ℤ[i]} χ₀(z)·z^m·e^{-πu|z|²}`.  Its Mellin transform is `4π^{-s}Γ(s)L̃(s-m/2)`,
`L̃` Hecke's *complete* `L`-function (sum over all ideals); the `z = 0` term vanishes for `m ≥ 1`
and contributes `χ₀ 0 = 0` for `m = 0`. -/
def allZTheta (chi₀ : GaussianInt → ℂ) (m : ℕ) (u : ℝ) : ℂ :=
  ∑' z : GaussianInt,
    chi₀ z * (z.toComplex) ^ m * Complex.exp (-(Real.pi * u * (gnorm z : ℝ)))

/-- **The Gauss sum of the weight `χ₀` at the conductor `M`**, presented on the residue ring
`ℤ[i]/(N M) ⊇ ℤ[i]/M` as the square `[0, N M)²`:

  `condGaussSum M chi₀ ξ = Σ_{α ∈ [0,N M)²} χ₀(α)·e^{2πi(α.re·ξ.re + α.im·ξ.im)/(N M)}`.

It is the finite Fourier transform of the `(N M)`-periodic weight `χ₀`; the conductor enters only
through the periodicity (`M ∣ N M`). -/
def condGaussSum (M : GaussianInt) (chi₀ : GaussianInt → ℂ) (ξ : GaussianInt) : ℂ :=
  ∑ a ∈ Finset.range (gnorm M), ∑ b ∈ Finset.range (gnorm M),
    chi₀ (⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt) *
      Complex.exp (2 * Real.pi * Complex.I *
        (((((a : ℤ) * ξ.re + (b : ℤ) * ξ.im : ℤ)) : ℂ) / ((gnorm M : ℕ) : ℂ)))

/-- **The conclusion of `heckeFEStrictConductor` for a character of conductor `M`** (with the base
forced to `X = √(N M) ∈ [1, 4d]`): an entire `Φ` with the reflected functional equation agreeing on
`re s > 1 + |m|/2` with `(X/π)^s Γ(s+|m|/2) L(s,ψ_χ)` times a finite product of inverse Euler
factors at the rational primes `p ∣ 4d`. -/
def HasConductorFEleAt (d : ℕ) (M : GaussianInt) (chi : GaussianInt → ℂ) (m : ℤ) : Prop :=
  ∃ (c₁ c₂ : ℕ → ℂ) (S : Finset ℕ) (Phi : ℂ → ℂ) (W : ℂ),
    (∀ p ∈ S, Nat.Prime p ∧ p ∣ 4 * d ∧ ‖c₁ p‖ ≤ 1 ∧ ‖c₂ p‖ ≤ 1) ∧
    W ≠ 0 ∧ AnalyticOn ℂ Phi Set.univ ∧
    (∀ s : ℂ, Phi s = W * star (Phi (star (1 - s)))) ∧
    (∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
      Phi s = (((Real.sqrt ((gnorm M : ℕ) : ℝ)) / Real.pi : ℝ) : ℂ) ^ s *
        Complex.Gamma (s + ((|(m : ℝ)| / 2 : ℝ) : ℂ)) *
        Work.FIArea5.S16Hecke.heckeLSeries chi m s *
        ∏ p ∈ S, ((1 - c₁ p * ((p : ℂ) ^ (-s))) * (1 - c₂ p * ((p : ℂ) ^ (-s))))⁻¹)

/-- **Primitivity of a character of `(ℤ[i]/M)^*`, with a *unit* witness.**  For every proper
non-unit divisor `M' ∣ M` there is a unit `u` modulo `M` with `u ≡ 1 (mod M')` and `χ₀ u ≠ 1`
(equivalently: `χ₀` does not factor through `(ℤ[i]/M')^*`).

This is `IsPrimitiveAt` with the witness required to be a unit modulo `M`; the unit condition is
what makes the Gauss-sum duality usable (a non-unit witness only tests that `χ₀` *vanishes*). -/
def IsPrimitiveCharAt (M : GaussianInt) (chi₀ : GaussianInt → ℂ) : Prop :=
  ∀ M' : GaussianInt, M' ∣ M → ¬ (M ∣ M') → ¬ IsUnit M' →
    ∃ z : GaussianInt, IsUnitMod M z ∧ M' ∣ (z - 1) ∧ chi₀ z ≠ 1

/-- **The complete (all-`z`) Hecke `L`-series** of the Größencharacter of `χ₀` and weight `m`:

  `fullHeckeLSeries chi₀ m s = Σ_{z ∈ ℤ[i]} χ₀(z)·(z/|z|)^m·N(z)^{-s}`.

It equals `4·L̃(s)`, `L̃(s) = ∏_{all 𝔭}(1 - ψ(𝔭)N𝔭^{-s})^{-1}` Hecke's *complete* `L`-function
(the factor `4` counts the units; the `z = 0` term vanishes because `χ₀ 0 = 0` for `M` not a unit).
This — and not `heckeLSeries chi₀ m`, which is the sum over the *primary* coset and equals
`L(ψ_{χ₀}) = L̃·∏_{𝔭 ∣ (4d), 𝔭 ∤ M}(1 - ψ(𝔭)N𝔭^{-s})` — is the `L`-function whose completion at
`X = √(N M)` is the `Φ` of the target. -/
def fullHeckeLSeries (chi₀ : GaussianInt → ℂ) (m : ℤ) (s : ℂ) : ℂ :=
  ∑' z : GaussianInt,
    chi₀ z * ((z.toComplex / ((Real.sqrt ((gnorm z : ℕ) : ℝ) : ℂ))) ^ m) *
      (((gnorm z : ℕ) : ℂ) ^ (-s))

end

end Work.FIArea6Hecke.R
