/-
# Definitions for the `d = 24` decaying funnel bound

This file collects the definitions used by
`Submission/Work/Asymptotics/KMinusFunnelMainBoundDecay.lean`:
the reference values of the `z`-atoms (`kmfd_E4refc`, `kmfd_jref`, `kmfd_Shref`),
the reference bracket `kmfd_BR` and the coefficients `kmfd_c1, …, kmfd_c8` of its
expansion in powers of `Ept z`.
-/
import Mathlib
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.Compact.tailDefs
import Submission.Work.Asymptotics.Compact.kminus_tail_core
import Submission.Work.Asymptotics.Compact.kminus_tail_aux
import Submission.Work.FunnelNumerics.Lamb_funnel_bound
import Submission.Work.FunnelNumerics.E4_funnel_bounds
import Submission.Work.Residues.KMinusCuspDefs

set_option maxHeartbeats 4000000

namespace Work.Asymptotics

open UpperHalfPlane
open Work.Kernels

noncomputable section

/-! ## Reference values for the `z`-atoms in dimension 24 -/

/-- Reference value of `E₄(z)³`: `(1 + 240 E²)³` with `E = Ept z`. -/
def kmfd_E4refc (z : ℍ) : ℂ := (1 + 240 * (Work.Residues.Ept z) ^ 2) ^ 3

/-- Reference value of `j(z)`: `(1 + 240 E²)³ (E⁻² + 24)`. -/
def kmfd_jref (z : ℍ) : ℂ := kmfd_E4refc z * Compact.Dref z

/-- Reference value of `Sh τ z = E₄(z)³ - Δ(z)j(τ)`. -/
def kmfd_Shref (τ z : ℍ) : ℂ := kmfd_E4refc z - (Work.Residues.Ept z) ^ 2 * jInvariantFun τ

/-- The reference expression for the bracket `brMinus 24 + Sh · br0 24`. -/
def kmfd_BR (ℓ : LogLambdaData) (τ z : ℍ) : ℂ :=
  Compact.Dref z * Compact.A24ref ℓ τ z + Compact.C24 ℓ τ * Compact.Wref z
    + (jInvariantFun τ - kmfd_jref z) * Compact.Wref z * Compact.B24 ℓ τ
    + kmfd_Shref τ z * Compact.br0 24 ℓ τ z

/-! ## The coefficients of `kmfd_BR = Σ_{k=1}^{8} c_k E^k` -/

/-- `c₁`: coefficient of `Ept z` in the reference expansion. -/
def kmfd_c1 (ℓ : LogLambdaData) (τ z : ℍ) : ℂ :=
  27648 * (jInvariantFun τ * DeltaFun τ)
    - 24 * (jInvariantFun τ * (psi2 ℓ τ * E10Fun τ))
    + 24 * (jInvariantFun τ * (psi4 ℓ τ * E8Fun τ))
    - 20570112 * DeltaFun τ + 15744 * (psi2 ℓ τ * E10Fun τ)
    - 29568 * (psi4 ℓ τ * E8Fun τ)

/-- `c₂`: coefficient of `(Ept z)²`. -/
def kmfd_c2 (ℓ : LogLambdaData) (τ z : ℍ) : ℂ :=
  -3456 * (Compact.Xc ℓ z * (jInvariantFun τ ^ 2 * DeltaFun τ))
    + 4976640 * (Compact.Xc ℓ z * (jInvariantFun τ * DeltaFun τ))
    - 1192402944 * (Compact.Xc ℓ z * DeltaFun τ)
    + 41472 * (jInvariantFun τ * DeltaFun τ)
    + 1080 * (jInvariantFun τ * (psi2 ℓ τ * E10Fun τ))
    + 648 * (jInvariantFun τ * (psi4 ℓ τ * E8Fun τ))
    + 31850496 * DeltaFun τ - 651456 * (psi2 ℓ τ * E10Fun τ)
    - 551232 * (psi4 ℓ τ * E8Fun τ)

/-- `c₃`: coefficient of `(Ept z)³`. -/
def kmfd_c3 (ℓ : LogLambdaData) (τ z : ℍ) : ℂ :=
  -5271257088 * DeltaFun τ + 3142656 * (psi2 ℓ τ * E10Fun τ)
    - 3142656 * (psi4 ℓ τ * E8Fun τ)

/-- `c₄`: coefficient of `(Ept z)⁴`. -/
def kmfd_c4 (ℓ : LogLambdaData) (τ z : ℍ) : ℂ :=
  597196800 * (Compact.Xc ℓ z * (jInvariantFun τ * DeltaFun τ))
    - 382205952000 * (Compact.Xc ℓ z * DeltaFun τ)
    + 8623521792 * DeltaFun τ - 178689024 * (psi2 ℓ τ * E10Fun τ)
    - 119909376 * (psi4 ℓ τ * E8Fun τ)

/-- `c₅`: coefficient of `(Ept z)⁵`. -/
def kmfd_c5 (ℓ : LogLambdaData) (τ z : ℍ) : ℂ :=
  -496867737600 * DeltaFun τ + 287539200 * (psi2 ℓ τ * E10Fun τ)
    - 287539200 * (psi4 ℓ τ * E8Fun τ)

/-- `c₆`: coefficient of `(Ept z)⁶`. -/
def kmfd_c6 (ℓ : LogLambdaData) (τ z : ℍ) : ℂ :=
  47775744000 * (Compact.Xc ℓ z * (jInvariantFun τ * DeltaFun τ))
    - 34398535680000 * (Compact.Xc ℓ z * DeltaFun τ)
    + 917294284800 * DeltaFun τ - 15460761600 * (psi2 ℓ τ * E10Fun τ)
    - 8427110400 * (psi4 ℓ τ * E8Fun τ)

/-- `c₇`: coefficient of `(Ept z)⁷`. -/
def kmfd_c7 (ℓ : LogLambdaData) (τ z : ℍ) : ℂ :=
  -9172942848000 * DeltaFun τ + 5308416000 * (psi2 ℓ τ * E10Fun τ)
    - 5308416000 * (psi4 ℓ τ * E8Fun τ)

/-- `c₈`: coefficient of `(Ept z)⁸`. -/
def kmfd_c8 (ℓ : LogLambdaData) (τ z : ℍ) : ℂ :=
  27518828544000 * DeltaFun τ - 15925248000 * (psi2 ℓ τ * E10Fun τ)
    + 15925248000 * (psi4 ℓ τ * E8Fun τ)


/-! ## The deviation of the bracket from its reference expression -/

/-- The deviation `A24 - A24ref` of the `Δ(z)⁻¹`-coefficient, written in terms of the cusp
deviations `dE14`, `dL`, `dE10`, `dD2`. -/
def kmfd_dA (ℓ : LogLambdaData) (τ z : ℍ) : ℂ :=
  -3456 * DeltaFun τ * (Compact.dE14 z * ℓ.L z + Compact.E14ref z * Compact.dL ℓ z)
    - (psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ)
        * (Compact.dE10 z * (UFun z ^ 2 - VFun z ^ 2) + Compact.E10ref z * Compact.dD2 z)

/-- `Sh τ z - Shref τ z = (E₄(z)³ - (1+240E²)³) - j(τ)(Δ(z) - E²)`. -/
def kmfd_dSh (τ z : ℍ) : ℂ :=
  (E4Fun z ^ 3 - kmfd_E4refc z)
    - jInvariantFun τ * (DeltaFun z - (Work.Residues.Ept z) ^ 2)

/-- The total deviation of the bracket from its reference expression. -/
def kmfd_dev (ℓ : LogLambdaData) (τ z : ℍ) : ℂ :=
  Compact.Dref z * kmfd_dA ℓ τ z + Compact.dDelta z * Compact.A24 ℓ τ z
    + Compact.C24 ℓ τ * Compact.dW z
    + (jInvariantFun τ - kmfd_jref z) * Compact.dW z * Compact.B24 ℓ τ
    - (jInvariantFun z - kmfd_jref z) * WFun z * Compact.B24 ℓ τ
    + kmfd_dSh τ z * Compact.br0 24 ℓ τ z

/-! ## Growth of the `τ`-atoms on the funnel -/

/-- Growth bounds for the `τ`-atoms on the funnel `{τ ∈ 𝒟 : 2 ≤ Im τ}`.  Every atom is
bounded by a constant times a power of `scale τ`, possibly times `e^{2π Im τ}` (the
`j`-monomials) or times `e^{-2π Im τ}` (the cusp-small atoms); each bound carries its own
constant and exponent, so the structure is easy to instantiate. -/
structure KMFDAtoms (ℓ : LogLambdaData) : Prop where
  j : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, Funnel τ →
    ‖jInvariantFun τ‖ ≤ C * Real.exp (2 * Real.pi * τ.im)
  Delta : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, Funnel τ →
    ‖DeltaFun τ‖ ≤ C * Real.exp (-(2 * Real.pi * τ.im))
  E4cube : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, Funnel τ → ‖E4Fun τ ^ 3‖ ≤ C
  E4 : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, Funnel τ → ‖E4Fun τ‖ ≤ C
  E6 : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, Funnel τ → ‖E6Fun τ‖ ≤ C
  psi2b : ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, Funnel τ →
    ‖psi2 ℓ τ‖ ≤ C * (Work.Kernels.scale τ) ^ N
  psi4b : ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, Funnel τ →
    ‖psi4 ℓ τ‖ ≤ C * (Work.Kernels.scale τ) ^ N
  psi2E10 : ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, Funnel τ →
    ‖psi2 ℓ τ * E10Fun τ‖ ≤ C * (Work.Kernels.scale τ) ^ N
  psi4E8 : ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, Funnel τ →
    ‖psi4 ℓ τ * E8Fun τ‖ ≤ C * (Work.Kernels.scale τ) ^ N
  psi : ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, Funnel τ →
    ‖psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ‖
      ≤ C * (Work.Kernels.scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im))
  jpsi : ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, Funnel τ →
    ‖jInvariantFun τ * (psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ)‖
      ≤ C * (Work.Kernels.scale τ) ^ N
  j2Delta : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, Funnel τ →
    ‖jInvariantFun τ ^ 2 * DeltaFun τ‖ ≤ C * Real.exp (2 * Real.pi * τ.im)
  jDelta : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, Funnel τ → ‖jInvariantFun τ * DeltaFun τ‖ ≤ C
  jpsi2E10 : ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, Funnel τ →
    ‖jInvariantFun τ * (psi2 ℓ τ * E10Fun τ)‖
      ≤ C * (Work.Kernels.scale τ) ^ N * Real.exp (2 * Real.pi * τ.im)
  jpsi4E8 : ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, Funnel τ →
    ‖jInvariantFun τ * (psi4 ℓ τ * E8Fun τ)‖
      ≤ C * (Work.Kernels.scale τ) ^ N * Real.exp (2 * Real.pi * τ.im)

/-! ## The two algebraic identities -/

/-- **The reference expansion.**  The reference bracket is a polynomial in `E = Ept z` whose
lowest order is `E¹`. -/
theorem kmfd_BR_expansion (ℓ : LogLambdaData) (τ z : ℍ) :
    kmfd_BR ℓ τ z
      = Work.Residues.Ept z * kmfd_c1 ℓ τ z + (Work.Residues.Ept z) ^ 2 * kmfd_c2 ℓ τ z
        + (Work.Residues.Ept z) ^ 3 * kmfd_c3 ℓ τ z + (Work.Residues.Ept z) ^ 4 * kmfd_c4 ℓ τ z
        + (Work.Residues.Ept z) ^ 5 * kmfd_c5 ℓ τ z + (Work.Residues.Ept z) ^ 6 * kmfd_c6 ℓ τ z
        + (Work.Residues.Ept z) ^ 7 * kmfd_c7 ℓ τ z + (Work.Residues.Ept z) ^ 8 * kmfd_c8 ℓ τ z := by
  have he : Work.Residues.Ept z ≠ 0 := Work.Residues.Ept_ne_zero z
  have hD : DeltaFun τ ≠ 0 := ClassicalFacts.DeltaFun_ne_zero τ
  simp only [kmfd_BR]
  rw [Compact.br0_24]
  simp only [kmfd_jref, kmfd_Shref, kmfd_E4refc, kmfd_c1, kmfd_c2, kmfd_c3, kmfd_c4,
    kmfd_c5, kmfd_c6, kmfd_c7, kmfd_c8, Compact.A24ref, Compact.Dref, Compact.Wref,
    Compact.D2ref, Compact.Lref, Compact.E14ref, Compact.E10ref, Compact.C24, Compact.B24,
    Compact.Xc, Compact.Nf, Compact.Mf, Compact.einv2]
  field_simp
  ring

/-- **The bracket decomposition.**  The bracket `brMinus 24 + Sh · br0 24` equals its reference
expression plus the deviation `kmfd_dev`. -/
theorem kmfd_bracket_decomp (ℓ : LogLambdaData) (τ z : ℍ) :
    Compact.brMinus ℓ 24 τ z + Compact.Sh τ z * Compact.br0 24 ℓ τ z
      = kmfd_BR ℓ τ z + kmfd_dev ℓ τ z := by
  rw [Compact.brMinus_24_decomp]
  simp only [kmfd_BR, kmfd_dev, kmfd_dA, kmfd_dSh, kmfd_jref, kmfd_Shref, kmfd_E4refc,
    Compact.A24, Compact.A24ref, Compact.C24, Compact.B24, Compact.Dref, Compact.Wref,
    Compact.D2ref, Compact.Lref, Compact.E14ref, Compact.E10ref, Compact.Sh,
    Compact.dDelta, Compact.dW, Compact.dD2, Compact.dL, Compact.dE14, Compact.dE10]
  ring

end

end Work.Asymptotics
