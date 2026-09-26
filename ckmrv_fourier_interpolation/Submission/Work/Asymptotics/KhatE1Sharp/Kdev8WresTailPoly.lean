import Submission.Work.Asymptotics.KhatE1Sharp.Kdev8WresZAtoms

/-!
# `Kdev8WresTailPoly`: the polynomial/deviations split of the cleared residual

`KdevWresClearedPoly_decomp` writes the cleared residual of the sharp tail bound as

`Δ(τ)·(Δ(τ)·Sh(τ,z)·R) = WresPoly + (three deviation aggregates)`,  `R = Kdev8Bracket - 2·KdevE2·u²`

with `WresPoly = (kdevA2JFZtr - 2u²Δ·KdevE2)·ShDeltaZtr + kdevSig2JFZtr`.  `WresPoly` is *almost*
a polynomial in `u = Ept z`: the only non-polynomial pieces are the deviations `dW, dD2, dE8, dE6,
dE10, dL` appearing inside `Dev8RawJF`, and `kdevNum0` inside `kdevSig2JFZtr`.

This file performs the last split: every deviation is replaced by its *proved-order* truncation
(`WrefHi - Wref`, `D2refHi - D2ref`, `E8refHi - E8ref`, `E6refHi - E6ref`, `E10refHi - E10ref`,
`LrefHi - Lref`), the difference being the explicit remainders
`rW = W - WrefHi = O(u⁶)`, `rD2 = (U²-V²) - D2refHi = O(u⁶)`, `rE8 = E₄² - E8refHi = O(u⁶)`,
`rE6 = E₆ - E6refHi = O(u⁶)`, `rE10 = E₄E₆ - E10refHi = O(u⁶)`, `rL = 𝓛 - LrefHi = O(u⁵)`.

The result is the identity `Kdev8Cleared_eq_pol_add`: the cleared residual equals an explicit
*polynomial in `u`* plus an explicit remainder built from the `r…`.
-/

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane
open Work.Kernels

noncomputable section

/-- The polynomial truncation of the deviation `dW = W(z) - Wref(z)`: `WrefHi - Wref`. -/
def dWpol (z : ℍ) : ℂ := WrefHi z - Work.Asymptotics.Compact.Wref z

/-- The polynomial truncation of `dD2 = (U² - V²)(z) - D2ref(z)`. -/
def dD2pol (z : ℍ) : ℂ := D2refHi z - Work.Asymptotics.Compact.D2ref z

/-- The polynomial truncation of `dE8 = E₈(z) - E8ref(z)`. -/
def dE8pol (z : ℍ) : ℂ := E8refHi z - Work.Asymptotics.Compact.E8ref z

/-- The polynomial truncation of `dE6 = E₆(z) - E6ref(z)`. -/
def dE6pol (z : ℍ) : ℂ := E6refHi z - Work.Asymptotics.Compact.E6ref z

/-- The polynomial truncation of `dE10 = E₁₀(z) - E10ref(z)`. -/
def dE10pol (z : ℍ) : ℂ := E10refHi z - Work.Asymptotics.Compact.E10ref z

/-- The polynomial truncation of `dL = 𝓛(z) - Lref(z)`. -/
def dLpol (ℓ : Work.Kernels.LogLambdaData) (z : ℍ) : ℂ :=
  LrefHi ℓ z - Work.Asymptotics.Compact.Lref ℓ z

/-- The remainder `W(z) - WrefHi(z) = O(u⁶)`. -/
def rW (z : ℍ) : ℂ := Work.Kernels.WFun z - WrefHi z

/-- The remainder `(U² - V²)(z) - D2refHi(z) = O(u⁶)`. -/
def rD2 (z : ℍ) : ℂ := Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2 - D2refHi z

/-- The remainder `E₄(z)² - E8refHi(z) = O(u⁶)`. -/
def rE8 (z : ℍ) : ℂ := E8Fun z - E8refHi z

/-- The remainder `E₆(z) - E6refHi(z) = O(u⁶)`. -/
def rE6 (z : ℍ) : ℂ := E6Fun z - E6refHi z

/-- The remainder `E₄(z)E₆(z) - E10refHi(z) = O(u⁶)`. -/
def rE10 (z : ℍ) : ℂ := E10Fun z - E10refHi z

/-- The remainder `𝓛(z) - LrefHi(z) = O(u⁵)`. -/
def rL (ℓ : Work.Kernels.LogLambdaData) (z : ℍ) : ℂ := ℓ.L z - LrefHi ℓ z

/-- **The polynomial part of `DevA1`.** -/
def DevA1pol (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  -3456 * E4Fun τ * Work.Asymptotics.Compact.E10ref z * dLpol ℓ z

/-- **The polynomial part of `DevA2`.** -/
def DevA2pol (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  -3456 * E4Fun τ * dE10pol z * Work.Asymptotics.Compact.Lref ℓ z

/-- **The polynomial part of `DevA3`.** -/
def DevA3pol (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  -3456 * E4Fun τ * dE10pol z * dLpol ℓ z

/-- **The polynomial part of `Dev8RawJF`**: `dW, dD2, dE8, dE6, dE10, dL` replaced by their
proved-order truncations.  Since `E8refHi = E8ref + 61920q²` etc., this is `Dev8RawJF` with all
six deviations truncated — and it is a genuine *polynomial in `u = Ept z`* (the `ref` functions
are polynomials in `Ept z`). -/
def Dev8Pol (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  DeltaFun τ * (DevA1pol ℓ τ z + DevA2pol ℓ τ z + DevA3pol ℓ τ z)
    + psi2 ℓ τ * E14Fun τ
        * ((Work.Asymptotics.Compact.E8ref z * dWpol z
              - Work.Asymptotics.Compact.E6ref z * dD2pol z)
            + (dE8pol z * Work.Asymptotics.Compact.Wref z
                - dE6pol z * Work.Asymptotics.Compact.D2ref z)
            + (dE8pol z * dWpol z - dE6pol z * dD2pol z))
    + psi4 ℓ τ * ((1728 * DeltaFun τ - E4Fun τ ^ 3)
            * Work.Asymptotics.Compact.E8ref z * dWpol z
          + E4Fun τ ^ 3 * Work.Asymptotics.Compact.E6ref z * dD2pol z)
    + psi4 ℓ τ * ((1728 * DeltaFun τ - E4Fun τ ^ 3)
            * dE8pol z * Work.Asymptotics.Compact.Wref z
          + E4Fun τ ^ 3 * dE6pol z * Work.Asymptotics.Compact.D2ref z)
    + psi4 ℓ τ * ((1728 * DeltaFun τ - E4Fun τ ^ 3)
            * dE8pol z * dWpol z
          + E4Fun τ ^ 3 * dE6pol z * dD2pol z)

/-- **The remainder of the `Dev8RawJF` split**: every deviation replaced by its remainder. -/
def Dev8Rem (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  DeltaFun τ * (-3456 * E4Fun τ * Work.Asymptotics.Compact.E10ref z * rL ℓ z
      + -3456 * E4Fun τ * rE10 z * Work.Asymptotics.Compact.Lref ℓ z
      + -3456 * E4Fun τ * (rE10 z * Work.Asymptotics.Compact.dL ℓ z
            + dE10pol z * rL ℓ z))
    + psi2 ℓ τ * E14Fun τ
        * ((Work.Asymptotics.Compact.E8ref z * rW z
              - Work.Asymptotics.Compact.E6ref z * rD2 z)
            + (rE8 z * Work.Asymptotics.Compact.Wref z
                - rE6 z * Work.Asymptotics.Compact.D2ref z)
            + (rE8 z * Work.Asymptotics.Compact.dW z
                + dE8pol z * rW z
                - rE6 z * Work.Asymptotics.Compact.dD2 z
                - dE6pol z * rD2 z))
    + psi4 ℓ τ * ((1728 * DeltaFun τ - E4Fun τ ^ 3)
            * Work.Asymptotics.Compact.E8ref z * rW z
          + E4Fun τ ^ 3 * Work.Asymptotics.Compact.E6ref z * rD2 z)
    + psi4 ℓ τ * ((1728 * DeltaFun τ - E4Fun τ ^ 3)
            * rE8 z * Work.Asymptotics.Compact.Wref z
          + E4Fun τ ^ 3 * rE6 z * Work.Asymptotics.Compact.D2ref z)
    + psi4 ℓ τ * ((1728 * DeltaFun τ - E4Fun τ ^ 3)
            * (rE8 z * Work.Asymptotics.Compact.dW z + dE8pol z * rW z)
          + E4Fun τ ^ 3
            * (rE6 z * Work.Asymptotics.Compact.dD2 z + dE6pol z * rD2 z))

/-- **The `Dev8RawJF` split.** -/
theorem Dev8RawJF_eq_pol_add (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    Dev8RawJF ℓ τ z = Dev8Pol ℓ τ z + Dev8Rem ℓ τ z := by
  rw [Dev8RawJF, Dev8Pol, Dev8Rem, DevA1pol, DevA2pol, DevA3pol,
    dWpol, dD2pol, dE8pol, dE6pol, dE10pol, dLpol, rW, rD2, rE8, rE6, rE10, rL,
    Work.Asymptotics.Compact.DevA1, Work.Asymptotics.Compact.DevA2,
    Work.Asymptotics.Compact.DevA3, Work.Asymptotics.Compact.dW,
    Work.Asymptotics.Compact.dD2, Work.Asymptotics.Compact.dE8,
    Work.Asymptotics.Compact.dE6, Work.Asymptotics.Compact.dE10,
    Work.Asymptotics.Compact.dL]
  ring

end

end Work.Asymptotics.KhatE1

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane
open Work.Kernels

noncomputable section

/-- The deviation of `kdevNum0` from its truncated version (the RHS of `kdevNum0_split`). -/
def kdevNum0Rem (τ z : ℍ) : ℂ :=
  (τ : ℂ) * Work.Kernels.E6Fun τ
      * (Work.Kernels.phitVec z 2 * (Work.Kernels.E4Fun z) ^ 2
          - phit2Ztr z * (E4Ztr z) ^ 2)
    - 2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ
      * (Work.Kernels.phitVec z 1 * Work.Kernels.E4Fun z * Work.Kernels.E6Fun z
          - phit1Ztr z * E4Ztr z * E6Ztr z)

/-- Repackaging of `kdevNum0_split`. -/
theorem kdevNum0_eq_Ztr_add (τ z : ℍ) :
    kdevNum0 τ z = kdevNum0Ztr τ z + kdevNum0Rem τ z :=
  kdevNum0_split τ z

/-- `kdevSig2JFZtr` with `Dev8RawJF ↦ Dev8Pol` and `kdevNum0 ↦ kdevNum0Ztr`. -/
def kdevSig2JFZtrPol (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  ((3456 : ℂ) * (Real.pi : ℂ))⁻¹ *
      (Work.Kernels.DeltaFun τ * br8refJF ℓ τ z
        + Work.Kernels.DeltaFun τ * Dev8Pol ℓ τ z)
    - Work.Asymptotics.Compact.tailC⁻¹ *
        (Work.Kernels.DeltaFun τ *
          (Work.Kernels.phi2 τ * Work.Kernels.E14Fun τ * (z : ℂ) ^ 2
              * DeltaZtr z
            + Work.Kernels.DeltaFun τ * kdevNum0Ztr τ z))

/-- **The `kdevSig2JFZtr` polynomial/deviation split.** -/
theorem kdevSig2JFZtr_eq_pol_add (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    kdevSig2JFZtr ℓ τ z
      = kdevSig2JFZtrPol ℓ τ z
        + (((3456 : ℂ) * (Real.pi : ℂ))⁻¹ * Work.Kernels.DeltaFun τ * Dev8Rem ℓ τ z
            - Work.Asymptotics.Compact.tailC⁻¹ * Work.Kernels.DeltaFun τ
                * Work.Kernels.DeltaFun τ * kdevNum0Rem τ z) := by
  rw [kdevSig2JFZtr, kdevSig2JFZtrPol, Dev8RawJF_eq_pol_add ℓ τ z,
    kdevNum0_eq_Ztr_add τ z]
  ring

/-- **The polynomial part of `WresPoly`**: `Dev8RawJF ↦ Dev8Pol` and `kdevNum0 ↦ kdevNum0Ztr`
— a genuine polynomial in `u = Ept z`. -/
def WresPolyPol (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  (kdevA2JFZtr ℓ τ z
      - 2 * (Work.Residues.Ept z) ^ 2 * (Work.Kernels.DeltaFun τ * KdevE2 ℓ τ z))
    * ShDeltaZtr τ z
  + kdevSig2JFZtrPol ℓ τ z

/-- **The `WresPoly` polynomial/deviation split.** -/
theorem WresPoly_eq_pol_add (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    WresPoly ℓ τ z
      = WresPolyPol ℓ τ z
        + (((3456 : ℂ) * (Real.pi : ℂ))⁻¹ * Work.Kernels.DeltaFun τ * Dev8Rem ℓ τ z
            - Work.Asymptotics.Compact.tailC⁻¹ * Work.Kernels.DeltaFun τ
                * Work.Kernels.DeltaFun τ * kdevNum0Rem τ z) := by
  rw [WresPoly, WresPolyPol, kdevSig2JFZtr_eq_pol_add ℓ τ z]
  ring

/-- **The cleared residual's polynomial/deviation split.**  `R = Kdev8Bracket - 2·KdevE2·u²`. -/
theorem Kdev8Cleared_eq_pol_add (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ)
    (hSh : Work.Asymptotics.Compact.Sh τ z ≠ 0) (hΔ : Work.Kernels.DeltaFun τ ≠ 0) :
    Work.Kernels.DeltaFun τ *
        (Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.Sh τ z *
          (Work.Asymptotics.KhatE1Core.Kdev8Bracket ℓ τ z
            - 2 * KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2))
      = WresPolyPol ℓ τ z
        + (((3456 : ℂ) * (Real.pi : ℂ))⁻¹ * Work.Kernels.DeltaFun τ * Dev8Rem ℓ τ z
            - Work.Asymptotics.Compact.tailC⁻¹ * Work.Kernels.DeltaFun τ
                * Work.Kernels.DeltaFun τ * kdevNum0Rem τ z
            + (kdevA2JF ℓ τ z
                - 2 * (Work.Residues.Ept z) ^ 2
                    * (Work.Kernels.DeltaFun τ * KdevE2 ℓ τ z)) * ShDev τ z
            + KdevA2Dev ℓ τ z * ShDeltaZtr τ z
            + KdevSig2Dev ℓ τ z) := by
  rw [KdevWresClearedPoly_decomp ℓ τ z hSh hΔ, WresPoly_eq_pol_add ℓ τ z]
  ring

end

end Work.Asymptotics.KhatE1


namespace Work.Asymptotics.KhatE1

open UpperHalfPlane
open Work.Kernels

noncomputable section

/-! ## The `u`-coefficients of `WresPolyPol`

`WresPolyPol` is a polynomial in `u = Ept z` of degree `16`; the defs below are its coefficients,
computed by `ring_nf` from the (fully unfolded) expression and verified by the single `ring`
identity `WresPolyPol_eq_sum`.  `p0, p1, p2` vanish by the three rungs (`WresPolyAt0_eq_zero`,
`br8refJF_u1`, `WresPolyAt2_eq_zero`); the bounds for `p3 … p16` are the remaining obligation.
-/

def p0 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  -((Work.Kernels.DeltaFun τ) ^ 2) * ((Real.pi : ℂ)⁻¹) * Work.Kernels.E4Fun τ * Work.Asymptotics.Compact.Xc ℓ z  + ((Work.Kernels.DeltaFun τ) ^ 2) * ((Real.pi : ℂ)⁻¹) * Work.Asymptotics.Compact.br0 8 ℓ τ z * ((1 : ℂ) / 3456)  + ((Work.Kernels.DeltaFun τ) ^ 2) * ((Real.pi : ℂ)⁻¹) * Work.Kernels.psi4 ℓ τ * ((1 : ℂ) / 2)

def p1 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  Work.Kernels.DeltaFun τ * Work.Kernels.E6Fun τ * ((Real.pi : ℂ)⁻¹) * ((Work.Kernels.E4Fun τ) ^ 2) * Work.Kernels.psi2 ℓ τ * ((-1 : ℂ) / 144)  + Work.Kernels.DeltaFun τ * ((Real.pi : ℂ)⁻¹) * ((Work.Kernels.E4Fun τ) ^ 3) * Work.Kernels.psi4 ℓ τ * ((1 : ℂ) / 144)  + Work.Kernels.DeltaFun τ * ((Real.pi : ℂ)⁻¹) * R8p0JF ℓ τ * ((-1 : ℂ) / 3456)  + ((Work.Kernels.DeltaFun τ) ^ 2) * ((Real.pi : ℂ)⁻¹) * Work.Kernels.E4Fun τ * 8  - ((Work.Kernels.DeltaFun τ) ^ 2) * ((Real.pi : ℂ)⁻¹) * Work.Kernels.psi4 ℓ τ * 4

def p2 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.tailC⁻¹ * (τ : ℂ) * Work.Kernels.E6Fun τ * (z : ℂ) * Complex.I * ((Real.pi : ℂ)⁻¹) * ((Work.Kernels.E4Fun τ) ^ 3) * 12  - Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.tailC⁻¹ * (τ : ℂ) * Work.Kernels.E6Fun τ * ((z : ℂ) ^ 2) * ((Work.Kernels.E4Fun τ) ^ 3)  - Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.tailC⁻¹ * (τ : ℂ) * Work.Kernels.E6Fun τ * (Complex.I ^ 2) * (((Real.pi : ℂ)⁻¹) ^ 2) * ((Work.Kernels.E4Fun τ) ^ 3) * 36  - Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.tailC⁻¹ * Work.Kernels.E6Fun τ * ((z : ℂ) ^ 2) * ((Work.Kernels.E4Fun τ) ^ 2) * Work.Kernels.phi2 τ  - Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.tailC⁻¹ * (z : ℂ) * Complex.I * ((Real.pi : ℂ)⁻¹) * Work.Kernels.phi0 τ * ((Work.Kernels.E4Fun τ) ^ 4) * 12  + Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.tailC⁻¹ * ((z : ℂ) ^ 2) * Work.Kernels.phi0 τ * ((Work.Kernels.E4Fun τ) ^ 4) * 2  + Work.Kernels.DeltaFun τ * Work.Kernels.E6Fun τ * ((Real.pi : ℂ)⁻¹) * ((Work.Kernels.E4Fun τ) ^ 2) * Work.Kernels.psi2 ℓ τ * ((1 : ℂ) / 3)  + Work.Kernels.DeltaFun τ * ((Real.pi : ℂ)⁻¹) * ((Work.Kernels.E4Fun τ) ^ 3) * Work.Asymptotics.Compact.br0 8 ℓ τ z * ((-1 : ℂ) / 3456)  + Work.Kernels.DeltaFun τ * ((Real.pi : ℂ)⁻¹) * ((Work.Kernels.E4Fun τ) ^ 3) * Work.Kernels.psi4 ℓ τ * ((-1 : ℂ) / 3)  - ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * (τ : ℂ) * Work.Kernels.E6Fun τ * (z : ℂ) * Complex.I * ((Real.pi : ℂ)⁻¹) * 3168  + ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * (τ : ℂ) * Work.Kernels.E6Fun τ * ((z : ℂ) ^ 2) * 288  + ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * (τ : ℂ) * Work.Kernels.E6Fun τ * (Complex.I ^ 2) * (((Real.pi : ℂ)⁻¹) ^ 2) * 8640  + ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * (z : ℂ) * Complex.I * ((Real.pi : ℂ)⁻¹) * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ * 11808  - ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * ((z : ℂ) ^ 2) * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ * 2016  - ((Work.Kernels.DeltaFun τ) ^ 2) * ((Real.pi : ℂ)⁻¹) * Work.Kernels.E4Fun τ * 12  + ((Work.Kernels.DeltaFun τ) ^ 2) * ((Real.pi : ℂ)⁻¹) * Work.Kernels.E4Fun τ * Work.Asymptotics.Compact.Xc ℓ z * 264  + ((Work.Kernels.DeltaFun τ) ^ 2) * ((Real.pi : ℂ)⁻¹) * Work.Asymptotics.Compact.br0 8 ℓ τ z * ((5 : ℂ) / 24)  + ((Work.Kernels.DeltaFun τ) ^ 2) * ((Real.pi : ℂ)⁻¹) * Work.Kernels.psi4 ℓ τ * 252  - ((Work.Kernels.DeltaFun τ) ^ 2) * KdevE2 ℓ τ z * 2

def p3 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  Work.Kernels.DeltaFun τ * Work.Kernels.E6Fun τ * ((Real.pi : ℂ)⁻¹) * ((Work.Kernels.E4Fun τ) ^ 2) * Work.Kernels.psi2 ℓ τ * ((13 : ℂ) / 12)  + Work.Kernels.DeltaFun τ * ((Real.pi : ℂ)⁻¹) * ((Work.Kernels.E4Fun τ) ^ 3) * Work.Kernels.psi4 ℓ τ * ((-13 : ℂ) / 12)  + Work.Kernels.DeltaFun τ * ((Real.pi : ℂ)⁻¹) * R8p0JF ℓ τ * ((-5 : ℂ) / 24)  + ((Work.Kernels.DeltaFun τ) ^ 2) * ((Real.pi : ℂ)⁻¹) * Work.Kernels.E4Fun τ * ((-6304 : ℂ) / 3)  - ((Work.Kernels.DeltaFun τ) ^ 2) * ((Real.pi : ℂ)⁻¹) * Work.Kernels.psi4 ℓ τ * 1936  + ((Real.pi : ℂ)⁻¹) * ((Work.Kernels.E4Fun τ) ^ 3) * R8p0JF ℓ τ * ((1 : ℂ) / 3456)

def p4 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  -Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.tailC⁻¹ * (τ : ℂ) * Work.Kernels.E6Fun τ * (z : ℂ) * Complex.I * ((Real.pi : ℂ)⁻¹) * ((Work.Kernels.E4Fun τ) ^ 3) * 288  + Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.tailC⁻¹ * (τ : ℂ) * Work.Kernels.E6Fun τ * ((z : ℂ) ^ 2) * ((Work.Kernels.E4Fun τ) ^ 3) * 24  + Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.tailC⁻¹ * (τ : ℂ) * Work.Kernels.E6Fun τ * (Complex.I ^ 2) * (((Real.pi : ℂ)⁻¹) ^ 2) * ((Work.Kernels.E4Fun τ) ^ 3) * 864  + Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.tailC⁻¹ * Work.Kernels.E6Fun τ * ((z : ℂ) ^ 2) * ((Work.Kernels.E4Fun τ) ^ 2) * Work.Kernels.phi2 τ * 24  + Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.tailC⁻¹ * (z : ℂ) * Complex.I * ((Real.pi : ℂ)⁻¹) * Work.Kernels.phi0 τ * ((Work.Kernels.E4Fun τ) ^ 4) * 288  - Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.tailC⁻¹ * ((z : ℂ) ^ 2) * Work.Kernels.phi0 τ * ((Work.Kernels.E4Fun τ) ^ 4) * 48  + Work.Kernels.DeltaFun τ * Work.Kernels.E6Fun τ * ((Real.pi : ℂ)⁻¹) * ((Work.Kernels.E4Fun τ) ^ 2) * Work.Kernels.psi2 ℓ τ * ((16 : ℂ) / 3)  + Work.Kernels.DeltaFun τ * ((Real.pi : ℂ)⁻¹) * ((Work.Kernels.E4Fun τ) ^ 3) * Work.Asymptotics.Compact.br0 8 ℓ τ z * ((1 : ℂ) / 144)  + Work.Kernels.DeltaFun τ * ((Real.pi : ℂ)⁻¹) * ((Work.Kernels.E4Fun τ) ^ 3) * Work.Kernels.psi4 ℓ τ * ((-16 : ℂ) / 3)  + Work.Kernels.DeltaFun τ * ((Work.Kernels.E4Fun τ) ^ 3) * KdevE2 ℓ τ z * 2  - ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * (τ : ℂ) * Work.Kernels.E6Fun τ * (z : ℂ) * Complex.I * ((Real.pi : ℂ)⁻¹) * 1547424  + ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * (τ : ℂ) * Work.Kernels.E6Fun τ * ((z : ℂ) ^ 2) * 139968  + ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * (τ : ℂ) * Work.Kernels.E6Fun τ * (Complex.I ^ 2) * (((Real.pi : ℂ)⁻¹) ^ 2) * 4224960  + ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * (z : ℂ) * Complex.I * ((Real.pi : ℂ)⁻¹) * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ * 3776544  - ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * ((z : ℂ) ^ 2) * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ * 616896  + ((Work.Kernels.DeltaFun τ) ^ 2) * ((Real.pi : ℂ)⁻¹) * Work.Kernels.E4Fun τ * 3162  + ((Work.Kernels.DeltaFun τ) ^ 2) * ((Real.pi : ℂ)⁻¹) * Work.Kernels.E4Fun τ * Work.Asymptotics.Compact.Xc ℓ z * 135432  + ((Work.Kernels.DeltaFun τ) ^ 2) * ((Real.pi : ℂ)⁻¹) * Work.Asymptotics.Compact.br0 8 ℓ τ z * ((415 : ℂ) / 8)  + ((Work.Kernels.DeltaFun τ) ^ 2) * ((Real.pi : ℂ)⁻¹) * Work.Kernels.psi4 ℓ τ * 36732  - ((Work.Kernels.DeltaFun τ) ^ 2) * KdevE2 ℓ τ z * 1440

def p5 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  Work.Kernels.DeltaFun τ * Work.Kernels.E6Fun τ * ((Real.pi : ℂ)⁻¹) * ((Work.Kernels.E4Fun τ) ^ 2) * Work.Kernels.psi2 ℓ τ * ((-145 : ℂ) / 24)  + Work.Kernels.DeltaFun τ * ((Real.pi : ℂ)⁻¹) * ((Work.Kernels.E4Fun τ) ^ 3) * Work.Kernels.psi4 ℓ τ * ((145 : ℂ) / 24)  + Work.Kernels.DeltaFun τ * ((Real.pi : ℂ)⁻¹) * R8p0JF ℓ τ * ((-415 : ℂ) / 8)  - ((Work.Kernels.DeltaFun τ) ^ 2) * ((Real.pi : ℂ)⁻¹) * Work.Kernels.E4Fun τ * 1086272  - ((Work.Kernels.DeltaFun τ) ^ 2) * ((Real.pi : ℂ)⁻¹) * Work.Kernels.psi4 ℓ τ * 255384  + ((Real.pi : ℂ)⁻¹) * ((Work.Kernels.E4Fun τ) ^ 3) * R8p0JF ℓ τ * ((-1 : ℂ) / 144)

def p6 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.tailC⁻¹ * (τ : ℂ) * Work.Kernels.E6Fun τ * (z : ℂ) * Complex.I * ((Real.pi : ℂ)⁻¹) * ((Work.Kernels.E4Fun τ) ^ 3) * 3024  - Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.tailC⁻¹ * (τ : ℂ) * Work.Kernels.E6Fun τ * ((z : ℂ) ^ 2) * ((Work.Kernels.E4Fun τ) ^ 3) * 252  - Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.tailC⁻¹ * (τ : ℂ) * Work.Kernels.E6Fun τ * (Complex.I ^ 2) * (((Real.pi : ℂ)⁻¹) ^ 2) * ((Work.Kernels.E4Fun τ) ^ 3) * 9072  - Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.tailC⁻¹ * Work.Kernels.E6Fun τ * ((z : ℂ) ^ 2) * ((Work.Kernels.E4Fun τ) ^ 2) * Work.Kernels.phi2 τ * 252  - Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.tailC⁻¹ * (z : ℂ) * Complex.I * ((Real.pi : ℂ)⁻¹) * Work.Kernels.phi0 τ * ((Work.Kernels.E4Fun τ) ^ 4) * 3024  + Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.tailC⁻¹ * ((z : ℂ) ^ 2) * Work.Kernels.phi0 τ * ((Work.Kernels.E4Fun τ) ^ 4) * 504  + Work.Kernels.DeltaFun τ * Work.Kernels.E6Fun τ * ((Real.pi : ℂ)⁻¹) * ((Work.Kernels.E4Fun τ) ^ 2) * Work.Kernels.psi2 ℓ τ * ((-1178 : ℂ) / 3)  + Work.Kernels.DeltaFun τ * ((Real.pi : ℂ)⁻¹) * ((Work.Kernels.E4Fun τ) ^ 3) * Work.Asymptotics.Compact.br0 8 ℓ τ z * ((-7 : ℂ) / 96)  + Work.Kernels.DeltaFun τ * ((Real.pi : ℂ)⁻¹) * ((Work.Kernels.E4Fun τ) ^ 3) * Work.Kernels.psi4 ℓ τ * ((1178 : ℂ) / 3)  - Work.Kernels.DeltaFun τ * ((Work.Kernels.E4Fun τ) ^ 3) * KdevE2 ℓ τ z * 48  - ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * (τ : ℂ) * Work.Kernels.E6Fun τ * (z : ℂ) * Complex.I * ((Real.pi : ℂ)⁻¹) * 209018880  + ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * (τ : ℂ) * Work.Kernels.E6Fun τ * ((z : ℂ) ^ 2) * 18658944  + ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * (τ : ℂ) * Work.Kernels.E6Fun τ * (Complex.I ^ 2) * (((Real.pi : ℂ)⁻¹) ^ 2) * 572313600  + ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * (z : ℂ) * Complex.I * ((Real.pi : ℂ)⁻¹) * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ * 264176640  - ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * ((z : ℂ) ^ 2) * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ * 37490688  + ((Work.Kernels.DeltaFun τ) ^ 2) * ((Real.pi : ℂ)⁻¹) * Work.Kernels.E4Fun τ * 1626768  + ((Work.Kernels.DeltaFun τ) ^ 2) * ((Real.pi : ℂ)⁻¹) * Work.Asymptotics.Compact.br0 8 ℓ τ z * 4900  + ((Work.Kernels.DeltaFun τ) ^ 2) * ((Real.pi : ℂ)⁻¹) * Work.Kernels.psi4 ℓ τ * 748800  - ((Work.Kernels.DeltaFun τ) ^ 2) * KdevE2 ℓ τ z * 358560

def p7 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  Work.Kernels.DeltaFun τ * Work.Kernels.E6Fun τ * ((Real.pi : ℂ)⁻¹) * ((Work.Kernels.E4Fun τ) ^ 2) * Work.Kernels.psi2 ℓ τ * 1870  - Work.Kernels.DeltaFun τ * ((Real.pi : ℂ)⁻¹) * ((Work.Kernels.E4Fun τ) ^ 3) * Work.Kernels.psi4 ℓ τ * 1870  - Work.Kernels.DeltaFun τ * ((Real.pi : ℂ)⁻¹) * R8p0JF ℓ τ * 4900  - ((Work.Kernels.DeltaFun τ) ^ 2) * ((Real.pi : ℂ)⁻¹) * Work.Kernels.E4Fun τ * 1444608  - ((Work.Kernels.DeltaFun τ) ^ 2) * ((Real.pi : ℂ)⁻¹) * Work.Kernels.psi4 ℓ τ * 1002240  + ((Real.pi : ℂ)⁻¹) * ((Work.Kernels.E4Fun τ) ^ 3) * R8p0JF ℓ τ * ((7 : ℂ) / 96)

def p8 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  -Work.Kernels.DeltaFun τ * Work.Kernels.E6Fun τ * ((Real.pi : ℂ)⁻¹) * ((Work.Kernels.E4Fun τ) ^ 2) * Work.Kernels.psi2 ℓ τ * 3959  + Work.Kernels.DeltaFun τ * ((Real.pi : ℂ)⁻¹) * ((Work.Kernels.E4Fun τ) ^ 3) * Work.Kernels.psi4 ℓ τ * 3959  + Work.Kernels.DeltaFun τ * ((Work.Kernels.E4Fun τ) ^ 3) * KdevE2 ℓ τ z * 504  - ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * (τ : ℂ) * Work.Kernels.E6Fun τ * (z : ℂ) * Complex.I * ((Real.pi : ℂ)⁻¹) * 4943047680  + ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * (τ : ℂ) * Work.Kernels.E6Fun τ * ((z : ℂ) ^ 2) * 403932096  + ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * (τ : ℂ) * Work.Kernels.E6Fun τ * (Complex.I ^ 2) * (((Real.pi : ℂ)⁻¹) ^ 2) * 13772851200  + ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * (z : ℂ) * Complex.I * ((Real.pi : ℂ)⁻¹) * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ * 5078039040  - ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * ((z : ℂ) ^ 2) * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ * 582982272  + ((Work.Kernels.DeltaFun τ) ^ 2) * ((Real.pi : ℂ)⁻¹) * Work.Kernels.E4Fun τ * 812592  + ((Work.Kernels.DeltaFun τ) ^ 2) * ((Real.pi : ℂ)⁻¹) * Work.Asymptotics.Compact.br0 8 ℓ τ z * 112050  + ((Work.Kernels.DeltaFun τ) ^ 2) * ((Real.pi : ℂ)⁻¹) * Work.Kernels.psi4 ℓ τ * 743040  - ((Work.Kernels.DeltaFun τ) ^ 2) * KdevE2 ℓ τ z * 33868800

def p9 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  Work.Kernels.DeltaFun τ * Work.Kernels.E6Fun τ * ((Real.pi : ℂ)⁻¹) * ((Work.Kernels.E4Fun τ) ^ 2) * Work.Kernels.psi2 ℓ τ * 8842  - Work.Kernels.DeltaFun τ * ((Real.pi : ℂ)⁻¹) * ((Work.Kernels.E4Fun τ) ^ 3) * Work.Kernels.psi4 ℓ τ * 8842  - Work.Kernels.DeltaFun τ * ((Real.pi : ℂ)⁻¹) * R8p0JF ℓ τ * 112050  - ((Work.Kernels.DeltaFun τ) ^ 2) * ((Real.pi : ℂ)⁻¹) * Work.Kernels.psi4 ℓ τ * 1486080

def p10 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  -((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * (τ : ℂ) * Work.Kernels.E6Fun τ * (z : ℂ) * Complex.I * ((Real.pi : ℂ)⁻¹) * 42550272000  + ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * (τ : ℂ) * Work.Kernels.E6Fun τ * ((z : ℂ) ^ 2) * 2918799360  + ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * (τ : ℂ) * Work.Kernels.E6Fun τ * (Complex.I ^ 2) * (((Real.pi : ℂ)⁻¹) ^ 2) * 120932352000  + ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * (z : ℂ) * Complex.I * ((Real.pi : ℂ)⁻¹) * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ * 40310784000  - ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * ((z : ℂ) ^ 2) * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ * 4262492160  + ((Work.Kernels.DeltaFun τ) ^ 2) * ((Real.pi : ℂ)⁻¹) * Work.Asymptotics.Compact.br0 8 ℓ τ z * 972000  - ((Work.Kernels.DeltaFun τ) ^ 2) * KdevE2 ℓ τ z * 774489600

def p11 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  -Work.Kernels.DeltaFun τ * ((Real.pi : ℂ)⁻¹) * R8p0JF ℓ τ * 972000

def p12 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  -((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * (τ : ℂ) * Work.Kernels.E6Fun τ * (z : ℂ) * Complex.I * ((Real.pi : ℂ)⁻¹) * 124963430400  + ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * (τ : ℂ) * Work.Kernels.E6Fun τ * ((z : ℂ) ^ 2) * 4157982720  + ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * (τ : ℂ) * Work.Kernels.E6Fun τ * (Complex.I ^ 2) * (((Real.pi : ℂ)⁻¹) ^ 2) * 362797056000  + ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * (z : ℂ) * Complex.I * ((Real.pi : ℂ)⁻¹) * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ * 120932352000  - ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * ((z : ℂ) ^ 2) * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ * 14982174720  + ((Work.Kernels.DeltaFun τ) ^ 2) * ((Real.pi : ℂ)⁻¹) * Work.Asymptotics.Compact.br0 8 ℓ τ z * 2916000  - ((Work.Kernels.DeltaFun τ) ^ 2) * KdevE2 ℓ τ z * 6718464000

def p13 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  -Work.Kernels.DeltaFun τ * ((Real.pi : ℂ)⁻¹) * R8p0JF ℓ τ * 2916000

def p14 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  -((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * (τ : ℂ) * Work.Kernels.E6Fun τ * ((z : ℂ) ^ 2) * 21499084800  - ((Work.Kernels.DeltaFun τ) ^ 2) * KdevE2 ℓ τ z * 20155392000

def p15 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  (0 : ℂ)

def p16 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  -((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * (τ : ℂ) * Work.Kernels.E6Fun τ * ((z : ℂ) ^ 2) * 24186470400


/-- **The `u`-expansion of the polynomial part of the cleared residual.** -/
def Puept (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  p0 ℓ τ z + p1 ℓ τ z * (Work.Residues.Ept z) + p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + p4 ℓ τ z * (Work.Residues.Ept z) ^ 4 + p5 ℓ τ z * (Work.Residues.Ept z) ^ 5 + p6 ℓ τ z * (Work.Residues.Ept z) ^ 6 + p7 ℓ τ z * (Work.Residues.Ept z) ^ 7 + p8 ℓ τ z * (Work.Residues.Ept z) ^ 8 + p9 ℓ τ z * (Work.Residues.Ept z) ^ 9 + p10 ℓ τ z * (Work.Residues.Ept z) ^ 10 + p11 ℓ τ z * (Work.Residues.Ept z) ^ 11 + p12 ℓ τ z * (Work.Residues.Ept z) ^ 12 + p13 ℓ τ z * (Work.Residues.Ept z) ^ 13 + p14 ℓ τ z * (Work.Residues.Ept z) ^ 14 + p15 ℓ τ z * (Work.Residues.Ept z) ^ 15 + p16 ℓ τ z * (Work.Residues.Ept z) ^ 16

/-- **The coefficient extraction.**  `WresPolyPol` is the explicit polynomial
`Σ_{k=0}^{16} p_k · u^k` in `u = Ept z`. -/
theorem WresPolyPol_eq_sum (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    WresPolyPol ℓ τ z = Puept ℓ τ z := by
  rw [WresPolyPol, Puept,
    kdevA2JFZtr, kdevSig2JFZtrPol, Dev8Pol, DevA1pol, DevA2pol, DevA3pol,
    dWpol, dD2pol, dE8pol, dE6pol, dE10pol, dLpol, br8refJF,
    ShDeltaZtr, PhiMainTrunc, kdevDirTrunc, kdevNum0Ztr, phit1Ztr, phit2Ztr, GtTr,
    WrefHi, D2refHi, E8refHi, E10refHi, E6refHi, LrefHi,
    E4Ztr, E6Ztr, E2Ztr, DeltaZtr,
    Work.Asymptotics.Compact.E8ref, Work.Asymptotics.Compact.E10ref,
    Work.Asymptotics.Compact.E6ref, Work.Asymptotics.Compact.Wref,
    Work.Asymptotics.Compact.D2ref, Work.Asymptotics.Compact.Lref,
    Work.Asymptotics.Small.qParamFun_eq_Ept_sq z,
    p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16]
  ring

end

end Work.Asymptotics.KhatE1

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane
open Work.Kernels

noncomputable section

/-- **The `d = 8` value of `br0`**: `br0 8 ℓ τ z = 3456·E₄(τ)·Xc ℓ z - 1728·ψ₄ ℓ τ`. -/
theorem br0_eight_eq (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    Work.Asymptotics.Compact.br0 8 ℓ τ z
      = 3456 * Work.Kernels.E4Fun τ * Work.Asymptotics.Compact.Xc ℓ z
        - 1728 * Work.Kernels.psi4 ℓ τ := by
  rw [Work.Asymptotics.Compact.br0, Work.Asymptotics.Compact.Gminus, if_pos rfl,
    Work.Asymptotics.Compact.Gminus8, Work.Asymptotics.Compact.Xc]
  field_simp
  ring

/-- **The `u⁰`-coefficient vanishes.** -/
theorem p0_eq_zero (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : p0 ℓ τ z = 0 := by
  rw [p0, br0_eight_eq ℓ τ z]
  ring

/-- **The `u¹`-coefficient vanishes.** -/
theorem p1_eq_zero (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : p1 ℓ τ z = 0 := by
  rw [p1, R8p0JF]
  ring

/-- **The `u²`-coefficient vanishes.**  Uses the `j`-free form `Delta_mul_KdevE2` of
`Δ(τ)·KdevE2`. -/
theorem p2_eq_zero (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : p2 ℓ τ z = 0 := by
  have hK : (Work.Kernels.DeltaFun τ) ^ 2 * KdevE2 ℓ τ z
      = Work.Kernels.DeltaFun τ * (Work.Kernels.DeltaFun τ * KdevE2 ℓ τ z) := by ring
  rw [p2, br0_eight_eq ℓ τ z, hK, Delta_mul_KdevE2 ℓ τ z]
  ring

end

end Work.Asymptotics.KhatE1
