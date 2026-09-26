import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.Bracket24TailCore
import Submission.Work.Asymptotics.KhatE1Core.Bracket24BCoeffs
import Submission.Work.Asymptotics.K24FDefs
import Submission.Work.Asymptotics.KMFDDefs

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane
open Work.Residues (Ept)

noncomputable section

/-!
# The truncated `E(z)`-expansion of the `d = 24` bracket: `Xtrunc`

This module *materialises* the expression `Xtrunc`, the `Sh`-cleared `d = 24` bracket
`X = KPlus24Group + KMinus24Group = Sh τ z · Bracket24 ℓ τ z` with every `z`-atom (and every
inverse of a `z`-atom) replaced by its explicit truncation, while the `τ`-atoms and the
reference polynomials (`Compact.Dref`, `Wref`, `Lref`, `D2ref`, `E14ref`, `E10ref`, `Sinvref`,
`KMFDDefs.kmfd_*ref`) are kept.

Structure of the module:

* the truncated atoms `E4T, E6T, E8T, E10T, E14T, DeltaT, invDeltaT, invE4T, invE4cubeT, E2ST,
  WT, D2T, LT, jzT, d1T` (all explicit polynomials in `q = qParamFun z`, `Ept z`, the
  reference `S0`, and `Xc ℓ z`);
* the truncated `K₊`-side pieces `PfunT, UfunT, VfunT, PhiT, Sm1T … Sm5T`, `KPlus24GroupT`;
* the truncated `K₋`-side pieces `A24T`, `brMinusT`, `ShT`;
* `Xtrunc`.

The two facts used downstream are

  `Bracket24XtruncRing` : `Xtrunc - B₂E² - B₃E³ - B₄E⁴ - B₅E⁵` is `O(‖q‖⁻¹(scale τ)^N(1+t)^M ‖E‖⁶)`
  (the finite `ring` identity together with the crude `j`-degree-≤1 estimate), and

  `Bracket24XtruncTail` : `X - Xtrunc` is bounded by the `z`-atom truncation tails.

The truncation depths are those of the *proved* atom expansions of the workspace
(`KhatE1Core.stripAtom_trunc`, `KhatE1.ZAtomsSecondOrder`, `KhatE1.cusp_L_fourth`,
`KhatE1Core.invDeltaSecondOrder`, `KhatE1Core.ZDevRefined`), which is exactly what makes the
second statement provable.
-/

/-- `q(z) = qParamFun z`. -/
def Tq (z : ℍ) : ℂ := Work.Kernels.qParamFun z
/-- `E(z) = Ept z`. -/
def Te (z : ℍ) : ℂ := Ept z

/-- Truncation of `E₄(z)`. -/
def E4T (z : ℍ) : ℂ := 1 + 240 * Tq z + 2160 * (Tq z) ^ 2
/-- Truncation of `E₆(z)`. -/
def E6T (z : ℍ) : ℂ := 1 - 504 * Tq z - 16632 * (Tq z) ^ 2
/-- Truncation of `E₈(z) = E₄(z)²`. -/
def E8T (z : ℍ) : ℂ := 1 + 480 * Tq z + 61920 * (Tq z) ^ 2
/-- Truncation of `E₁₀(z) = E₄(z)E₆(z)`. -/
def E10T (z : ℍ) : ℂ := 1 - 264 * Tq z - 135432 * (Tq z) ^ 2
/-- Truncation of `E₁₄(z) = E₄(z)²E₆(z)`. -/
def E14T (z : ℍ) : ℂ := 1 - 24 * Tq z - 196632 * (Tq z) ^ 2
/-- Truncation of `Δ(z)`. -/
def DeltaT (z : ℍ) : ℂ := Tq z - 24 * (Tq z) ^ 2 + 252 * (Tq z) ^ 3
/-- Truncation of `Δ(z)⁻¹`. -/
def invDeltaT (z : ℍ) : ℂ := (Tq z)⁻¹ + 24 + 324 * Tq z
/-- Truncation of `E₄(z)⁻¹`. -/
def invE4T (z : ℍ) : ℂ := 1 - 240 * Tq z + 55440 * (Tq z) ^ 2
/-- Truncation of `E₄(z)⁻³`. -/
def invE4cubeT (z : ℍ) : ℂ := 1 - 720 * Tq z + 339120 * (Tq z) ^ 2
/-- Truncation of `E₂ˢ(z)` (`S0` is the reference of `E₂ˢ`). -/
def E2ST (z : ℍ) : ℂ := Work.Asymptotics.K24F.S0 z - 24 * Tq z - 72 * (Tq z) ^ 2
/-- Truncation of `W(z)`. -/
def WT (z : ℍ) : ℂ := 1 - 8 * Te z + 24 * (Te z) ^ 2 - 32 * (Te z) ^ 3
  + 24 * (Te z) ^ 4 - 48 * (Te z) ^ 5
/-- Truncation of `U(z)² - V(z)²`. -/
def D2T (z : ℍ) : ℂ := 1 + 16 * Te z - 144 * (Te z) ^ 2 + 448 * (Te z) ^ 3
  - 912 * (Te z) ^ 4 + 2016 * (Te z) ^ 5
/-- Truncation of `𝓛(z)`. -/
def LT (ℓ : Work.Kernels.LogLambdaData) (z : ℍ) : ℂ :=
  Work.Asymptotics.Compact.Xc ℓ z - 8 * Te z + 12 * Tq z - (32 / 3) * (Te z) ^ 3
    + 6 * (Tq z) ^ 2
/-- Truncation of `j(z)`. -/
def jzT (z : ℍ) : ℂ := (Tq z)⁻¹ + 744 + 196884 * Tq z
/-- Truncation of `d1 z = Δ(z)⁻¹ - q⁻¹ - 24`. -/
def d1T (z : ℍ) : ℂ := 324 * Tq z

/-! ## The truncated `K₊`-side pieces -/

/-- Truncated `Pfun`. -/
def PfunT (τ z : ℍ) : ℂ :=
  Work.Asymptotics.K24F.r0 τ * (6 * E4T z - 6 * (E2ST z) ^ 2)
    + Work.Asymptotics.K24F.r1 τ * ((-12 * Work.Kernels.jInvariantFun τ + 8640) * E4T z
        + (12 * Work.Kernels.jInvariantFun τ - 12096) * (E2ST z) ^ 2)
    + Work.Asymptotics.K24F.r2 τ * (6 * E4T z - 6 * (E2ST z) ^ 2)

/-- Truncated `Ufun`. -/
def UfunT (τ z : ℍ) : ℂ :=
  1728 * Work.Asymptotics.K24F.r0 τ * (E2ST z) ^ 2 + 1728 * Work.Asymptotics.K24F.r2 τ * E4T z

/-- Truncated `Vfun`. -/
def VfunT (τ z : ℍ) : ℂ := -3456 * Work.Asymptotics.K24F.r1 τ * E14T z * E2ST z

/-- Truncated `Φ`. -/
def PhiT (τ z : ℍ) : ℂ := PfunT τ z - VfunT τ z * invE4cubeT z

/-- Truncated `S1`. -/
def Sm1T (τ z : ℍ) : ℂ :=
  Work.Kernels.jInvariantFun τ * (PhiT τ z - Work.Asymptotics.K24F.Phiref τ z)
    - (E4T z) ^ 3 * Work.Asymptotics.K24F.Q1 τ z * (Tq z * invDeltaT z - 1)
    - (E4T z) ^ 3 * (PhiT τ z - Work.Asymptotics.K24F.Phiref τ z - Tq z * Work.Asymptotics.K24F.Q1 τ z)
        * invDeltaT z

/-- Truncated `S2`. -/
def Sm2T (τ z : ℍ) : ℂ :=
  Work.Kernels.jInvariantFun τ * Work.Asymptotics.K24F.Phiref τ z * (1 - DeltaT z * (Tq z)⁻¹)
    - (E4T z) ^ 3 * Work.Asymptotics.K24F.Phiref τ z * d1T z

/-- Truncated `S3`. -/
def Sm3T (τ z : ℍ) : ℂ :=
  3456 * Work.Asymptotics.K24F.R0 τ
    * ((E4T z) ^ 3 * Work.Asymptotics.K24F.S0 z - E6T z * E2ST z * invE4T z)

/-- Truncated `S4`. -/
def Sm4T (τ z : ℍ) : ℂ :=
  (UfunT τ z - Work.Asymptotics.K24F.Uref τ z)
    + Work.Asymptotics.K24F.Uref τ z * (1 - (E4T z) ^ 3)

/-- Truncated `S5`. -/
def Sm5T (τ z : ℍ) : ℂ :=
  -(DeltaT z * Work.Kernels.jInvariantFun τ) * Work.Asymptotics.K24F.Th0 τ z

/-- The truncated `K₊`-group. -/
def KPlus24GroupT (τ z : ℍ) : ℂ :=
  -(Work.Asymptotics.K24F.c * (z : ℂ) ^ 2
      * (Sm1T τ z + Sm2T τ z + Sm3T τ z + Sm4T τ z + Sm5T τ z))

/-! ## The truncated `K₋`-side pieces -/

/-- Truncated `A₂₄`. -/
def A24T (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  -3456 * Work.Kernels.DeltaFun τ * E14T z * LT ℓ z
    - (Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ
        - Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ) * E10T z * D2T z

/-- Truncated `Sh τ z = E₄(z)³ - Δ(z)j(τ)`. -/
def ShT (τ z : ℍ) : ℂ := (E4T z) ^ 3 - DeltaT z * Work.Kernels.jInvariantFun τ

/-- Truncated `brMinus 24 = Δ(z)⁻¹A₂₄ + C₂₄W(z) + (j(τ)-j(z))W(z)B₂₄`. -/
def brMinusT (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  invDeltaT z * A24T ℓ τ z + Work.Asymptotics.Compact.C24 ℓ τ * WT z
    + (Work.Kernels.jInvariantFun τ - jzT z) * WT z * Work.Asymptotics.Compact.B24 ℓ τ

/-- **The truncated bracket** `Xtrunc`, the expression `KPlus24Group + KMinus24Group` with every
`z`-atom replaced by its truncation. -/
def Xtrunc (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  KPlus24GroupT τ z
    + ((3456 : ℂ) * (Real.pi : ℂ))⁻¹
        * (brMinusT ℓ τ z + ShT τ z * Work.Asymptotics.Compact.br0 24 ℓ τ z
            - ShT τ z * Ept z
                * (Work.Asymptotics.E1combo24 ℓ τ + Work.Asymptotics.KhatE1.Am24 ℓ τ))

/-- The `E(z)^4`-coefficient of the `Sh`-cleared bracket (the model's generated polynomial, as in
`KhatE1Core.Bracket24B4`). -/
def B4T (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ := Bracket24B4 ℓ τ z

end

end Work.Asymptotics.KhatE1Core
