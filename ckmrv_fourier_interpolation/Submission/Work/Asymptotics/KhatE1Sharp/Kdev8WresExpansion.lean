import Mathlib
import Submission.Work.Asymptotics.KhatE1.KdevE2Defs
import Submission.Work.Asymptotics.KhatE1Sharp.Kdev8ABDefs
import Submission.Work.Asymptotics.KhatE1Core.ClearedCombos

/-!
# Clearing `Δ(τ)` from the `E(z)²`-coefficient: the start of the `u`-expansion

The `u`-expansion of the cleared residual
`Δ(τ)·Sh(τ,z)·(Kdev8Bracket - 2·KdevE2·Ept z²)` (with `u = Ept z`) can only be a statement
about *polynomials in the atoms* once every `Δ(τ)`-denominator has been cleared.  The bracket
part is already polynomial (`KhatE1.kdevBridge2`: `Δ(τ)·Kdev8Bracket·Sh = kdevA2·Sh + kdevSig2`),
so the only remaining inverse power of `Δ(τ)` sits in `KdevE2` (`KdevE2plus` contains
`-φ₂(τ)E₁₄(τ)z²/Δ(τ)` and `KdevE2minus` contains `1152·ψ₂E₁₄/Δ(τ)`).

Here we clear it: `Δ(τ)·KdevE2` is an explicit polynomial in
`E₄(τ),E₆(τ),E₁₄(τ),Δ(τ),ψ₂,ψ₄,φ₀(τ),φ₂(τ),z,Xc ℓ z`, using only the defining identity
`Δ(τ)j(τ) = E₄(τ)³` (`ClassicalFacts.DeltaFun_mul_jInvariantFun`).  This is the first
mechanical step of the finite `q(τ)^0`/`q(τ)^1` cancellation of
`KhatE1.Kdev8BracketTailBound`.
-/

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane

noncomputable section

/-- `j(τ) = E₄(τ)³/Δ(τ)` (division form of `ClassicalFacts.DeltaFun_mul_jInvariantFun`). -/
theorem jInvariantFun_eq_E4cube_div (τ : ℍ) :
    Work.Kernels.jInvariantFun τ
      = Work.Kernels.E4Fun τ ^ 3 / Work.Kernels.DeltaFun τ := by
  have hD : Work.Kernels.DeltaFun τ ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ
  rw [eq_div_iff hD, mul_comm]
  exact Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun τ

/-- **`Δ(τ)·KdevE2` is a polynomial in the atoms** (no `1/Δ(τ)` left).

Obtained from the definition `KdevE2 = KdevE2plus + KdevE2minus` by distributing `Δ(τ)` and
using `Δ(τ)·j(τ) = E₄(τ)³`; it is the form in which the `Ept z`-expansion of the residual
`Kdev8Bracket - 2·KdevE2·Ept z²` becomes a computation in the atoms. -/
theorem Delta_mul_KdevE2 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    Work.Kernels.DeltaFun τ * KdevE2 ℓ τ z
      = (1 / (2 * Work.Asymptotics.Compact.tailC)) *
          ( -24 * ( Work.Kernels.DeltaFun τ * ((τ : ℂ) * Work.Kernels.E6Fun τ *
                      (-2 * (z : ℂ) ^ 2 + 12 * Complex.I * (z : ℂ) / (Real.pi : ℂ)))
                    + 2 * Work.Kernels.DeltaFun τ * (Work.Kernels.phi0 τ)
                        * Work.Kernels.E4Fun τ * (z : ℂ) ^ 2 )
            - Work.Kernels.phi2 τ * Work.Kernels.E14Fun τ * (z : ℂ) ^ 2
            - ( (τ : ℂ) * Work.Kernels.E6Fun τ
                  * ((z : ℂ) - 6 * Complex.I / (Real.pi : ℂ)) ^ 2
                  * (Work.Kernels.E4Fun τ ^ 3 - 240 * Work.Kernels.DeltaFun τ)
                - 2 * (Work.Kernels.phi0 τ) * Work.Kernels.E4Fun τ
                    * ((z : ℂ) ^ 2 - 6 * Complex.I * (z : ℂ) / (Real.pi : ℂ))
                    * (Work.Kernels.E4Fun τ ^ 3 - 984 * Work.Kernels.DeltaFun τ) ) )
        + (1 / (6912 * (Real.pi : ℂ))) *
            ( Work.Asymptotics.Compact.Xc ℓ z *
                (3400704 * Work.Kernels.DeltaFun τ * Work.Kernels.E4Fun τ
                  - 3456 * (Work.Kernels.E4Fun τ) ^ 4)
              + (-41472 * Work.Kernels.DeltaFun τ * Work.Kernels.E4Fun τ
                  - 373248 * Work.Kernels.DeltaFun τ * Work.Kernels.psi4 ℓ τ
                  + 1152 * (Work.Kernels.psi2 ℓ τ * Work.Kernels.E14Fun τ)
                  + 576 * (Work.Kernels.E4Fun τ) ^ 3 * Work.Kernels.psi4 ℓ τ) ) := by
  have hD : Work.Kernels.DeltaFun τ ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ
  rw [KdevE2, KdevE2plus, KdevE2minus, jInvariantFun_eq_E4cube_div τ,
    Work.Asymptotics.Compact.Xc]
  field_simp

end

end Work.Asymptotics.KhatE1

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane

noncomputable section

/-- **The fully cleared residual.**  With `u = Ept z`, the cleared residual of the sharp tail
bound is

  `Δ(τ)·Sh(τ,z)·(Kdev8Bracket - 2·KdevE2·u²)
     = (kdevA2 - 2·u²·(Δ(τ)·KdevE2))·Sh + kdevSig2`,

a polynomial in the atoms (no `Sh⁻¹`, no `Δ(τ)⁻¹`, no `Δ(z)⁻¹`, no `(j(τ)-j(z))⁻¹`) once
`Δ(τ)·KdevE2` is replaced by its cleared form `Delta_mul_KdevE2`.
This is the object whose `Ept z`-expansion has to have its `q(τ)^0`- and `q(τ)^1`-parts
cancelled. -/
theorem KdevWresCleared_eq (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ)
    (hSh : Work.Asymptotics.Compact.Sh τ z ≠ 0)
    (hΔ : Work.Kernels.DeltaFun τ ≠ 0) :
    Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.Sh τ z *
        (Work.Asymptotics.KhatE1Core.Kdev8Bracket ℓ τ z
          - 2 * KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2)
      = (kdevA2 ℓ τ z
            - 2 * (Work.Residues.Ept z) ^ 2
                * (Work.Kernels.DeltaFun τ * KdevE2 ℓ τ z))
          * Work.Asymptotics.Compact.Sh τ z
        + kdevSig2 ℓ τ z := by
  have hb := kdevBridge2 ℓ τ z hSh
  have hΔK : Work.Kernels.DeltaFun τ * KdevE2 ℓ τ z
      = (Work.Kernels.DeltaFun τ * KdevE2 ℓ τ z) := rfl
  calc Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.Sh τ z *
        (Work.Asymptotics.KhatE1Core.Kdev8Bracket ℓ τ z
          - 2 * KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2)
      = Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.Sh τ z
          * Work.Asymptotics.KhatE1Core.Kdev8Bracket ℓ τ z
        - 2 * (Work.Residues.Ept z) ^ 2 * Work.Asymptotics.Compact.Sh τ z
            * (Work.Kernels.DeltaFun τ * KdevE2 ℓ τ z) := by ring
    _ = (kdevA2 ℓ τ z * Work.Asymptotics.Compact.Sh τ z + kdevSig2 ℓ τ z)
        - 2 * (Work.Residues.Ept z) ^ 2 * Work.Asymptotics.Compact.Sh τ z
            * (Work.Kernels.DeltaFun τ * KdevE2 ℓ τ z) := by rw [hb]; ring
    _ = (kdevA2 ℓ τ z
            - 2 * (Work.Residues.Ept z) ^ 2
                * (Work.Kernels.DeltaFun τ * KdevE2 ℓ τ z))
          * Work.Asymptotics.Compact.Sh τ z
        + kdevSig2 ℓ τ z := by rw [hΔK]; ring

end

end Work.Asymptotics.KhatE1

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane

noncomputable section

/-- **`Sh` eliminated: the residual is a polynomial in the atoms with no `j(τ)`-denominator.**

Multiplying the cleared residual by `Δ(τ)` and using the proved
`KhatE1Core.DeltaFun_mul_Sh` (`Δ(τ)Sh(τ,z) = Δ(τ)E₄(z)³ - Δ(z)E₄(τ)³`) removes the last
non-atomic factor `Sh(τ,z) = E₄(z)³ - Δ(z)j(τ)`.  The result,
`Δ(τ)²·Sh·(Kdev8Bracket - 2·KdevE2·u²)`, is an explicit polynomial in
`E₄(τ),E₆(τ),E₁₄(τ),Δ(τ),ψ₂,ψ₄`, the `z`-atoms `E₂(z),E₄(z),E₆(z),Δ(z),E₈ref,E₁₀ref,
Wref,D2ref,𝓛ref` (and their deviations `dW,dD2,dL,dE₈,dE₆,dE₁₀`), `Xc ℓ z`, `z` and `u`;
the only remaining `j(τ)`-occurrences sit inside `kdevSig2` as `Δ(τ)·j(τ)` (in the `brMinus`
part) and are removed by `ClearedCombos.Delta_mul_br8ref` / `Delta_mul_Dev8Raw`, i.e. the next
rung is `rw`-only.

Since `‖Δ(τ)‖ ≤ 27‖q(τ)‖` on the funnel, the sharp tail bound for the bracket is *equivalent*
to a bound `‖Δ(τ)²·Sh·(Kdev8Bracket - 2·KdevE2·u²)‖ ≤ C‖q(τ)‖³‖Ept z‖²(scale τ)^N(1+t)^M`. -/
theorem KdevWresClearedPoly_eq (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ)
    (hSh : Work.Asymptotics.Compact.Sh τ z ≠ 0)
    (hΔ : Work.Kernels.DeltaFun τ ≠ 0) :
    Work.Kernels.DeltaFun τ *
        (Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.Sh τ z *
          (Work.Asymptotics.KhatE1Core.Kdev8Bracket ℓ τ z
            - 2 * KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2))
      = (kdevA2 ℓ τ z
            - 2 * (Work.Residues.Ept z) ^ 2
                * (Work.Kernels.DeltaFun τ * KdevE2 ℓ τ z))
          * (Work.Kernels.DeltaFun τ * Work.Kernels.E4Fun z ^ 3
              - Work.Kernels.DeltaFun z * Work.Kernels.E4Fun τ ^ 3)
        + Work.Kernels.DeltaFun τ * kdevSig2 ℓ τ z := by
  have h := KdevWresCleared_eq ℓ τ z hSh hΔ
  have hSh' : Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.Sh τ z
      = Work.Kernels.DeltaFun τ * Work.Kernels.E4Fun z ^ 3
        - Work.Kernels.DeltaFun z * Work.Kernels.E4Fun τ ^ 3 := by
    rw [Work.Asymptotics.Compact.Sh,
      ← Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun τ]
    ring
  calc Work.Kernels.DeltaFun τ *
        (Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.Sh τ z *
          (Work.Asymptotics.KhatE1Core.Kdev8Bracket ℓ τ z
            - 2 * KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2))
      = (kdevA2 ℓ τ z
            - 2 * (Work.Residues.Ept z) ^ 2
                * (Work.Kernels.DeltaFun τ * KdevE2 ℓ τ z))
          * (Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.Sh τ z)
        + Work.Kernels.DeltaFun τ * kdevSig2 ℓ τ z := by
        rw [h]; ring
    _ = (kdevA2 ℓ τ z
            - 2 * (Work.Residues.Ept z) ^ 2
                * (Work.Kernels.DeltaFun τ * KdevE2 ℓ τ z))
          * (Work.Kernels.DeltaFun τ * Work.Kernels.E4Fun z ^ 3
              - Work.Kernels.DeltaFun z * Work.Kernels.E4Fun τ ^ 3)
        + Work.Kernels.DeltaFun τ * kdevSig2 ℓ τ z := by
        rw [hSh']

end

end Work.Asymptotics.KhatE1


namespace Work.Asymptotics.KhatE1

open UpperHalfPlane
open Work.Kernels

noncomputable section

/-- The `j(τ)`-free form of `Δ(τ)·br8ref ℓ τ z` (verbatim RHS of the proved
`KhatE1Core.Delta_mul_br8ref`; no `j(τ)` occurs). -/
def br8refJF (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  DeltaFun τ * (-3456 * E4Fun τ * Work.Asymptotics.Compact.E10ref z
            * Work.Asymptotics.Compact.Lref ℓ z)
        + psi2 ℓ τ * E14Fun τ
            * (Work.Asymptotics.Compact.E8ref z * Work.Asymptotics.Compact.Wref z
              - Work.Asymptotics.Compact.E6ref z * Work.Asymptotics.Compact.D2ref z)
        + psi4 ℓ τ * ((1728 * DeltaFun τ - E4Fun τ ^ 3)
              * Work.Asymptotics.Compact.E8ref z * Work.Asymptotics.Compact.Wref z
            + E4Fun τ ^ 3 * Work.Asymptotics.Compact.E6ref z
              * Work.Asymptotics.Compact.D2ref z)

/-- The `j(τ)`-free form of `Δ(τ)·Dev8Raw ℓ τ z` (verbatim RHS of the proved
`KhatE1Core.Delta_mul_Dev8Raw`; no `j(τ)` occurs). -/
def Dev8RawJF (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  DeltaFun τ * (Work.Asymptotics.Compact.DevA1 ℓ τ z
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
              * Work.Asymptotics.Compact.dD2 z)

/-- Repackaging of `KhatE1Core.Delta_mul_br8ref`. -/
theorem Delta_mul_br8ref_eq (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.br8ref ℓ τ z
      = br8refJF ℓ τ z :=
  Work.Asymptotics.KhatE1Core.Delta_mul_br8ref ℓ τ z

/-- Repackaging of `KhatE1Core.Delta_mul_Dev8Raw`. -/
theorem Delta_mul_Dev8Raw_eq (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.Dev8Raw ℓ τ z
      = Dev8RawJF ℓ τ z :=
  Work.Asymptotics.KhatE1Core.Delta_mul_Dev8Raw ℓ τ z

/-- **`Δ(τ)·kdevSig2` in `j(τ)`-free form.**  `kdevSig2` contains `j(τ)` only through
`brMinus = br8ref + Dev8Raw`; both summands are multiplied by the outer `Δ(τ)³`-worth of factors,
so `Δ(τ)³·(1728 - j(τ))` and `Δ(τ)³·j(τ)` collapse to `E₄(τ)³`-expressions
(`ClearedCombos.Delta_mul_br8ref`, `ClearedCombos.Delta_mul_Dev8Raw`).  The result mentions no
`j(τ)`. -/
def kdevSig2JF (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  ((3456 : ℂ) * (Real.pi : ℂ))⁻¹ *
      (Work.Kernels.DeltaFun τ * br8refJF ℓ τ z
        + Work.Kernels.DeltaFun τ * Dev8RawJF ℓ τ z)
    - Work.Asymptotics.Compact.tailC⁻¹ *
        (Work.Kernels.DeltaFun τ *
          (Work.Kernels.phi2 τ * Work.Kernels.E14Fun τ * (z : ℂ) ^ 2
              * Work.Kernels.DeltaFun z
            + Work.Kernels.DeltaFun τ * kdevNum0 τ z))

/-- **The `j`-clearing rung.**  `Δ(τ)·kdevSig2 ℓ τ z = kdevSig2JF ℓ τ z`, with `kdevSig2JF`
`j(τ)`-free. -/
theorem Delta_mul_kdevSig2_jfree (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    Work.Kernels.DeltaFun τ * kdevSig2 ℓ τ z = kdevSig2JF ℓ τ z := by
  have hcomm : Work.Kernels.DeltaFun τ *
        (Work.Kernels.DeltaFun τ *
            (((3456 : ℂ) * (Real.pi : ℂ))⁻¹ *
              (Work.Asymptotics.Compact.br8ref ℓ τ z
                + Work.Asymptotics.Compact.Dev8Raw ℓ τ z))
          - Work.Asymptotics.Compact.tailC⁻¹ *
              (Work.Kernels.phi2 τ * Work.Kernels.E14Fun τ * (z : ℂ) ^ 2
                  * Work.Kernels.DeltaFun z
                + Work.Kernels.DeltaFun τ * kdevNum0 τ z))
      = ((3456 : ℂ) * (Real.pi : ℂ))⁻¹ *
          (Work.Kernels.DeltaFun τ *
              (Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.br8ref ℓ τ z)
            + Work.Kernels.DeltaFun τ *
              (Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.Dev8Raw ℓ τ z))
        - Work.Kernels.DeltaFun τ *
            (Work.Asymptotics.Compact.tailC⁻¹ *
              (Work.Kernels.phi2 τ * Work.Kernels.E14Fun τ * (z : ℂ) ^ 2
                  * Work.Kernels.DeltaFun z
                + Work.Kernels.DeltaFun τ * kdevNum0 τ z)) := by ring
  rw [kdevSig2, Work.Asymptotics.Compact.brMinus8_decomp, kdevSig2JF, hcomm,
    Delta_mul_br8ref_eq ℓ τ z, Delta_mul_Dev8Raw_eq ℓ τ z]
  ring

/-- **The residual identity, end to end `j(τ)`-free.**  Combining `KdevWresClearedPoly_eq` with
the `j`-clearing rung: the cleared residual of the sharp tail bound equals an explicit polynomial
in the atoms with *no* `Sh`, *no* `j(τ)` and no denominator except none at all. -/
theorem KdevWresClearedPolyJF_eq (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ)
    (hSh : Work.Asymptotics.Compact.Sh τ z ≠ 0)
    (hΔ : Work.Kernels.DeltaFun τ ≠ 0) :
    Work.Kernels.DeltaFun τ *
        (Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.Sh τ z *
          (Work.Asymptotics.KhatE1Core.Kdev8Bracket ℓ τ z
            - 2 * KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2))
      = (kdevA2 ℓ τ z
            - 2 * (Work.Residues.Ept z) ^ 2
                * (Work.Kernels.DeltaFun τ * KdevE2 ℓ τ z))
          * (Work.Kernels.DeltaFun τ * Work.Kernels.E4Fun z ^ 3
              - Work.Kernels.DeltaFun z * Work.Kernels.E4Fun τ ^ 3)
        + kdevSig2JF ℓ τ z := by
  rw [KdevWresClearedPoly_eq ℓ τ z hSh hΔ, Delta_mul_kdevSig2_jfree ℓ τ z]

end

end Work.Asymptotics.KhatE1

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane
open Work.Kernels

noncomputable section

/-- The `j(τ)`-free form of `Δ(τ)·R8_p0 ℓ τ` (`Δ(τ)j(τ) = E₄(τ)³`). -/
def R8p0JF (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  (27648 : ℂ) * Work.Kernels.DeltaFun τ * Work.Kernels.E4Fun τ
    + (-13824 : ℂ) * (Work.Kernels.DeltaFun τ * Work.Kernels.psi4 ℓ τ)
    + (-24 : ℂ) * (Work.Kernels.psi2 ℓ τ * Work.Kernels.E14Fun τ)
    + (24 : ℂ) * ((Work.Kernels.E4Fun τ) ^ 3 * Work.Kernels.psi4 ℓ τ)

/-- `Δ(τ)·R8_p0 ℓ τ = R8p0JF ℓ τ`. -/
theorem Delta_mul_R8p0 (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.R8_p0 ℓ τ = R8p0JF ℓ τ := by
  have hΔ : Work.Kernels.DeltaFun τ ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ
  rw [Work.Asymptotics.Compact.R8_p0, jInvariantFun_eq_E4cube_div τ]
  simp only [R8p0JF]
  field_simp

/-- **The `j(τ)`-free form of `kdevA2`** (the `j(τ)`-occurrences of `kdevA2` come only from
`R8_p0`, always under the outer `Δ(τ)`). -/
def kdevA2JF (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  Work.Kernels.DeltaFun τ * (Work.Asymptotics.Compact.tailC⁻¹
      * Work.Asymptotics.Compact.PhiMain τ z)
    + ((3456 : ℂ) * (Real.pi : ℂ))⁻¹
        * (Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.br0 8 ℓ τ z
            - Work.Residues.Ept z * R8p0JF ℓ τ)
    + Work.Kernels.DeltaFun τ * (Work.Asymptotics.Compact.tailC⁻¹ * kdevDir τ z)

/-- `kdevA2 ℓ τ z = kdevA2JF ℓ τ z`. -/
theorem kdevA2_eq_JF (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    kdevA2 ℓ τ z = kdevA2JF ℓ τ z := by
  have h := Delta_mul_R8p0 ℓ τ
  rw [kdevA2, kdevA2JF, ← h]
  ring

/-- **The residual identity, fully `j(τ)`-free.**  No `Sh`, no `j(τ)`, no denominator: the
cleared residual of the sharp tail bound is an explicit polynomial in
`E₄(τ),E₆(τ),E₁₄(τ),Δ(τ),ψ₂,ψ₄`, `Xc ℓ z`, `z`, `u = Ept z` and the `z`-atoms
`E₂(z),E₄(z),E₆(z),Δ(z),E₈ref,E₁₀ref,Wref,D2ref,𝓛ref` together with their deviations. -/
theorem KdevWresClearedPolyFullJF_eq (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ)
    (hSh : Work.Asymptotics.Compact.Sh τ z ≠ 0)
    (hΔ : Work.Kernels.DeltaFun τ ≠ 0) :
    Work.Kernels.DeltaFun τ *
        (Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.Sh τ z *
          (Work.Asymptotics.KhatE1Core.Kdev8Bracket ℓ τ z
            - 2 * KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2))
      = (kdevA2JF ℓ τ z
            - 2 * (Work.Residues.Ept z) ^ 2
                * (Work.Kernels.DeltaFun τ * KdevE2 ℓ τ z))
          * (Work.Kernels.DeltaFun τ * Work.Kernels.E4Fun z ^ 3
              - Work.Kernels.DeltaFun z * Work.Kernels.E4Fun τ ^ 3)
        + kdevSig2JF ℓ τ z := by
  rw [KdevWresClearedPolyJF_eq ℓ τ z hSh hΔ, kdevA2_eq_JF ℓ τ z]

end

end Work.Asymptotics.KhatE1
