import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.StripAtoms
import Submission.Work.Asymptotics.KhatE1Core.PhiCleared
import Submission.Work.Asymptotics.Compact.kminus_tail_main

/-!
# The elementary cancellations of the cleared residual

The cleared residual `Δ(τ)Sh(τ,z)·(Kdev8Bracket - 2·KdevE2·E(z)²)` is a polynomial in the atoms
(`PhiCleared`), of `j(τ)`-degree `≤ 1` once every product `Δ(τ)·j(τ)` has been replaced by
`E₄(τ)³`.  Its monomials still carry *large* combinations of the reference atoms, which cancel
exactly.  This module records those elementary cancellations in the form in which the `e = Ept z`
(order) bookkeeping needs them:

* `E8ref z·Wref z - E6ref z·D2ref z = e·(-24 + 1152e + 4224e² - 61056e³)` (`e = Ept z`),
  i.e. the combination is divisible by `e` (it is the `E₈W - E₆D₂` combination of `br8ref`);
* the `j(τ)`-free regrouping of the `ψ₄`-block of `br8ref`, using `Δ(τ)j(τ) = E₄(τ)³`;
* the `q`-orders of `E₈(z) - E₄(z)³`, `E₁₀(z) - E₄(z)³` and `Δ(z)j(τ)` (from `StripAtoms`),
  which is what makes the `Φ₃`-piece divisible by `q = (Ept z)²`.

All of them are identities in the atoms, so they hold for every `τ, z ∈ ℍ`. -/

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

open Work.Kernels

/-- `E₈ref·Wref - E₆ref·D2ref = e·(-24 + 1152e + 4224e² - 61056e³)` with `e = Ept z`. -/
theorem E8ref_mul_sub (z : ℍ) :
    Work.Asymptotics.Compact.E8ref z * Work.Asymptotics.Compact.Wref z
        - Work.Asymptotics.Compact.E6ref z * Work.Asymptotics.Compact.D2ref z
      = Work.Residues.Ept z * (-24 + 1152 * Work.Residues.Ept z
          + 4224 * (Work.Residues.Ept z) ^ 2 - 61056 * (Work.Residues.Ept z) ^ 3) := by
  rw [Work.Asymptotics.Compact.E8ref, Work.Asymptotics.Compact.Wref,
    Work.Asymptotics.Compact.E6ref, Work.Asymptotics.Compact.D2ref]
  ring

/-- The `e¹`-coefficient identity: `1728·E₈ref·Wref - (E₈ref·Wref - E₆ref·D2ref)` equals
`1728 - 13800e + 869760e² - 6639744e³ + 19967616e⁴`. -/
theorem E8ref_Wref_1728 (z : ℍ) :
    (1728 : ℂ) * Work.Asymptotics.Compact.E8ref z * Work.Asymptotics.Compact.Wref z
        - (Work.Asymptotics.Compact.E8ref z * Work.Asymptotics.Compact.Wref z
            - Work.Asymptotics.Compact.E6ref z * Work.Asymptotics.Compact.D2ref z)
      = 1728 - 13800 * Work.Residues.Ept z + 869760 * (Work.Residues.Ept z) ^ 2
        - 6639744 * (Work.Residues.Ept z) ^ 3
        + 19967616 * (Work.Residues.Ept z) ^ 4 := by
  rw [Work.Asymptotics.Compact.E8ref, Work.Asymptotics.Compact.Wref,
    Work.Asymptotics.Compact.E6ref, Work.Asymptotics.Compact.D2ref]
  ring

/-- `E₁₀ref·𝓛ref = Xc - 8e + (12 - 264Xc)e² + 2112e³ - 3168e⁴`. -/
theorem E10ref_mul_Lref (ℓ : Work.Kernels.LogLambdaData) (z : ℍ) :
    Work.Asymptotics.Compact.E10ref z * Work.Asymptotics.Compact.Lref ℓ z
      = Work.Asymptotics.Compact.Xc ℓ z - 8 * Work.Residues.Ept z
        + (12 - 264 * Work.Asymptotics.Compact.Xc ℓ z) * (Work.Residues.Ept z) ^ 2
        + 2112 * (Work.Residues.Ept z) ^ 3
        - 3168 * (Work.Residues.Ept z) ^ 4 := by
  rw [Work.Asymptotics.Compact.E10ref, Work.Asymptotics.Compact.Lref]
  ring

/-- **The `j(τ)`-free regrouping of the `ψ₄`-block of `br8ref`.**
`Δ(τ)·((1728 - j(τ))·E₈ref·Wref + j(τ)·E₆ref·D2ref) = (1728Δ(τ) - E₄(τ)³)·E₈ref·Wref
+ E₄(τ)³·E₆ref·D2ref`. -/
theorem Delta_mul_psi4block (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    DeltaFun τ * ((1728 - jInvariantFun τ) * Work.Asymptotics.Compact.E8ref z
          * Work.Asymptotics.Compact.Wref z
        + jInvariantFun τ * Work.Asymptotics.Compact.E6ref z
          * Work.Asymptotics.Compact.D2ref z)
      = (1728 * DeltaFun τ - E4Fun τ ^ 3) * Work.Asymptotics.Compact.E8ref z
          * Work.Asymptotics.Compact.Wref z
        + E4Fun τ ^ 3 * Work.Asymptotics.Compact.E6ref z
          * Work.Asymptotics.Compact.D2ref z := by
  rw [← ClassicalFacts.DeltaFun_mul_jInvariantFun τ]
  ring

/-- **`Δ(τ)·br8ref` in `j(τ)`-free form.** -/
theorem Delta_mul_br8ref (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    DeltaFun τ * Work.Asymptotics.Compact.br8ref ℓ τ z
      = DeltaFun τ * (-3456 * E4Fun τ * Work.Asymptotics.Compact.E10ref z
            * Work.Asymptotics.Compact.Lref ℓ z)
        + psi2 ℓ τ * E14Fun τ
            * (Work.Asymptotics.Compact.E8ref z * Work.Asymptotics.Compact.Wref z
              - Work.Asymptotics.Compact.E6ref z * Work.Asymptotics.Compact.D2ref z)
        + psi4 ℓ τ * ((1728 * DeltaFun τ - E4Fun τ ^ 3)
              * Work.Asymptotics.Compact.E8ref z * Work.Asymptotics.Compact.Wref z
            + E4Fun τ ^ 3 * Work.Asymptotics.Compact.E6ref z
              * Work.Asymptotics.Compact.D2ref z) := by
  have hΔ : DeltaFun τ ≠ 0 := ClassicalFacts.DeltaFun_ne_zero τ
  rw [Work.Asymptotics.Compact.br8ref]
  rw [← ClassicalFacts.DeltaFun_mul_jInvariantFun τ]
  field_simp

/-- `Δ(τ)·(Δ(z)·j(τ)) = Δ(z)·E₄(τ)³` (the product `Δ(τ)j(τ)` is cleared). -/
theorem Delta_mul_Delta_mul_j (τ z : ℍ) :
    DeltaFun τ * (DeltaFun z * jInvariantFun τ) = DeltaFun z * E4Fun τ ^ 3 := by
  rw [← ClassicalFacts.DeltaFun_mul_jInvariantFun τ]
  ring

/-- **The `j(τ)`-free form of `Δ(τ)·Dev8Raw`.**  Only the three `DevC`-terms of `Dev8Raw` carry
`j(τ)`, and `Δ(τ)j(τ) = E₄(τ)³` removes it. -/
theorem Delta_mul_Dev8Raw (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    DeltaFun τ * Work.Asymptotics.Compact.Dev8Raw ℓ τ z
      = DeltaFun τ * (Work.Asymptotics.Compact.DevA1 ℓ τ z
            + Work.Asymptotics.Compact.DevA2 ℓ τ z
            + Work.Asymptotics.Compact.DevA3 ℓ τ z)
        + psi2 ℓ τ * E14Fun τ
            * ((Work.Asymptotics.Compact.E8ref z * Work.Asymptotics.Compact.dW z
                  - Work.Asymptotics.Compact.E6ref z * Work.Asymptotics.Compact.dD2 z)
              + (Work.Asymptotics.Compact.dE8 z * Work.Asymptotics.Compact.Wref z
                  - Work.Asymptotics.Compact.dE6 z * Work.Asymptotics.Compact.D2ref z)
              + (Work.Asymptotics.Compact.dE8 z * Work.Asymptotics.Compact.dW z
                  - Work.Asymptotics.Compact.dE6 z * Work.Asymptotics.Compact.dD2 z))
        + psi4 ℓ τ * ((1728 * DeltaFun τ - E4Fun τ ^ 3)
              * Work.Asymptotics.Compact.E8ref z * Work.Asymptotics.Compact.dW z
            + E4Fun τ ^ 3 * Work.Asymptotics.Compact.E6ref z
              * Work.Asymptotics.Compact.dD2 z)
        + psi4 ℓ τ * ((1728 * DeltaFun τ - E4Fun τ ^ 3)
              * Work.Asymptotics.Compact.dE8 z * Work.Asymptotics.Compact.Wref z
            + E4Fun τ ^ 3 * Work.Asymptotics.Compact.dE6 z
              * Work.Asymptotics.Compact.D2ref z)
        + psi4 ℓ τ * ((1728 * DeltaFun τ - E4Fun τ ^ 3)
              * Work.Asymptotics.Compact.dE8 z * Work.Asymptotics.Compact.dW z
            + E4Fun τ ^ 3 * Work.Asymptotics.Compact.dE6 z
              * Work.Asymptotics.Compact.dD2 z) := by
  have hΔ : DeltaFun τ ≠ 0 := ClassicalFacts.DeltaFun_ne_zero τ
  rw [Work.Asymptotics.Compact.Dev8Raw, Work.Asymptotics.Compact.DevA1,
    Work.Asymptotics.Compact.DevA2, Work.Asymptotics.Compact.DevA3,
    Work.Asymptotics.Compact.DevB1, Work.Asymptotics.Compact.DevB2,
    Work.Asymptotics.Compact.DevB3, Work.Asymptotics.Compact.DevC1,
    Work.Asymptotics.Compact.DevC2, Work.Asymptotics.Compact.DevC3]
  rw [← ClassicalFacts.DeltaFun_mul_jInvariantFun τ]
  field_simp
  ring

/-- **`Δ(τ)·Sh(τ,z)·Sinvref(τ,z)` with the `j(τ)`-occurrences minimised.**  Using
`Δ(τ)j(τ) = E₄(τ)³` and `Δ(τ)Sh = Δ(τ)E₄(z)³ - Δ(z)E₄(τ)³`, only the single `Δ(z)j(τ)·e²` term
survives (`e = Ept z`). -/
theorem Delta_mul_Sh_mul_Sinvref (τ z : ℍ) :
    DeltaFun τ * Work.Asymptotics.Compact.Sh τ z * Work.Asymptotics.Compact.Sinvref τ z
      = (DeltaFun τ * E4Fun z ^ 3 - DeltaFun z * E4Fun τ ^ 3)
        + (E4Fun τ ^ 3 * E4Fun z ^ 3 - 720 * DeltaFun τ * E4Fun z ^ 3
            - DeltaFun z * E4Fun τ ^ 3 * jInvariantFun τ
            + 720 * DeltaFun z * E4Fun τ ^ 3) * (Work.Residues.Ept z) ^ 2 := by
  have hj : E4Fun τ ^ 3 = DeltaFun τ * jInvariantFun τ :=
    (ClassicalFacts.DeltaFun_mul_jInvariantFun τ).symm
  rw [Work.Asymptotics.Compact.Sinvref, Work.Asymptotics.Compact.Sh, hj]
  ring

/-- The same for `Δ(τ)·Sh(τ,z)·dSinv τ z = Δ(τ) - Δ(τ)Sh·Sinvref`. -/
theorem Delta_mul_Sh_mul_dSinv (τ z : ℍ) (hSh : Work.Asymptotics.Compact.Sh τ z ≠ 0) :
    DeltaFun τ * Work.Asymptotics.Compact.Sh τ z * Work.Asymptotics.Compact.dSinv τ z
      = DeltaFun τ
        - ((DeltaFun τ * E4Fun z ^ 3 - DeltaFun z * E4Fun τ ^ 3)
          + (E4Fun τ ^ 3 * E4Fun z ^ 3 - 720 * DeltaFun τ * E4Fun z ^ 3
              - DeltaFun z * E4Fun τ ^ 3 * jInvariantFun τ
              + 720 * DeltaFun z * E4Fun τ ^ 3) * (Work.Residues.Ept z) ^ 2) := by
  have h := Delta_mul_Sh_mul_Sinvref τ z
  have h1 : DeltaFun τ * Work.Asymptotics.Compact.Sh τ z
      * (Work.Asymptotics.Compact.Sh τ z)⁻¹ = DeltaFun τ := by
    rw [mul_assoc, mul_inv_cancel₀ hSh, mul_one]
  rw [Work.Asymptotics.Compact.dSinv, mul_sub, h1, h]

end

end Work.Asymptotics.KhatE1Core
