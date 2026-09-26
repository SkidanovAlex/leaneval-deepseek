import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.Kdev8_matching_bridge
import Submission.Work.Asymptotics.KhatE1.KdevE2Defs
import Submission.Work.Asymptotics.KhatE1.Kdev8CoeffAux
import Submission.Work.Asymptotics.KhatE1Core.PhiCleared
import Submission.Work.Kernels.Classical

/-!
# An explicit polynomial form of the `d = 8` bracket `Kdev8Bracket`

`Kdev8Bracket ℓ τ z = tailC⁻¹(Φ₁+Φ₂+Φ₃) + (3456π)⁻¹(Ept z·(R8 − R8_p0) + Dev8Sum)` is the
explicit bracket of `KhatE1Core.Kdev8_matching_bridge`.  This file records the explicit polynomial data used to write it in the form

  `Δ(τ)·Kdev8Bracket ℓ τ z · Sh τ z = kdevA2 ℓ τ z · Sh τ z + kdevSig2 ℓ τ z`

(the bridge identity itself is the remaining pure-algebra step), where `kdevA2`, `kdevSig2` and
`kdevDir`, `kdevNum`, `kdevNum0` are explicit polynomials in the
atoms of `τ` (`E₄, E₆, E₁₄, Δ, j, ψ₂, ψ₄`) and of `z` (`E₄(z), E₆(z), E₈(z), E₁₀(z), Δ(z), W(z),
U²−V², 𝓛(z)`), in `Ept z` and `z` alone — no `Sh⁻¹`, no `Δ(τ)⁻¹`:

* `kdevA2 ℓ τ z = Δ(τ)·(tailC⁻¹·Φ₁ + (3456π)⁻¹(br0 8 − Ept z·R8_p0) + tailC⁻¹·kdevDir τ z)`;
* `kdevSig2 ℓ τ z = Δ(τ)·(3456π)⁻¹·brMinus ℓ 8 τ z
      − tailC⁻¹·(φ₂(τ)E₁₄(τ)z²Δ(z) + Δ(τ)·kdevNum0 τ z)`;
* `kdevDir τ z = τ E₆(τ)φ̃₂(z) − 2φ₀(τ)E₄(τ)φ̃₁(z)`;
* `kdevNum0 τ z = τ E₆(τ)φ̃₂(z)E₄(z)² − 2φ₀(τ)E₄(τ)φ̃₁(z)E₄(z)E₆(z)`,
  `kdevNum τ z = τ E₆(τ)φ̃₂(z)(E₈(z)−E₄(z)³+Δ(z)j(τ)) − 2φ₀(τ)E₄(τ)φ̃₁(z)(E₁₀(z)−E₄(z)³+Δ(z)j(τ))`.

Because `‖Sh τ z‖ ≥ 1/16` and `‖Δ(τ)‖ ≥ q(τ)/2` on the funnel, a bound
`‖kdevA2·Sh + kdevSig2‖ ≤ C q(τ)² q_z (scale τ)^N (1+t)^M` is exactly the "sharp bracket bound"
`‖Kdev8Bracket‖ ≤ C' q(τ) (scale τ)^N (1+t)^M e^{-2πt}` and therefore yields the target of
`KhatE1.Kdev8TailSharpFleet`.
-/

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane

noncomputable section

/-- `dir τ z = τ·E₆(τ)·φ̃₂(z) − 2·φ₀(τ)·E₄(τ)·φ̃₁(z)`. -/
def kdevDir (τ z : ℍ) : ℂ :=
  (τ : ℂ) * Work.Kernels.E6Fun τ * Work.Kernels.phitVec z 2
    - 2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ * Work.Kernels.phitVec z 1

/-- The numerator of the `K₊`-residual with the `E₈(z)`, `E₁₀(z)` (and `Δ(z)j(τ)`) terms kept. -/
def kdevNum (τ z : ℍ) : ℂ :=
  (τ : ℂ) * Work.Kernels.E6Fun τ * Work.Kernels.phitVec z 2
      * (Work.Kernels.E8Fun z - Work.Kernels.E4Fun z ^ 3
          + Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ)
    - 2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ * Work.Kernels.phitVec z 1
      * (Work.Kernels.E10Fun z - Work.Kernels.E4Fun z ^ 3
          + Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ)

/-- The same numerator with `E₈(z)`, `E₁₀(z)`, `Δ(z)j(τ)` eliminated. -/
def kdevNum0 (τ z : ℍ) : ℂ :=
  (τ : ℂ) * Work.Kernels.E6Fun τ * Work.Kernels.phitVec z 2 * Work.Kernels.E4Fun z ^ 2
    - 2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ * Work.Kernels.phitVec z 1
      * Work.Kernels.E4Fun z * Work.Kernels.E6Fun z

/-- The polynomial part of `Δ(τ)·Kdev8Bracket·Sh`. -/
def kdevA2 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  Work.Kernels.DeltaFun τ * (Work.Asymptotics.Compact.tailC⁻¹
      * Work.Asymptotics.Compact.PhiMain τ z)
    + Work.Kernels.DeltaFun τ * (((3456 : ℂ) * (Real.pi : ℂ))⁻¹
        * (Work.Asymptotics.Compact.br0 8 ℓ τ z
            - Work.Residues.Ept z * Work.Asymptotics.Compact.R8_p0 ℓ τ))
    + Work.Kernels.DeltaFun τ * (Work.Asymptotics.Compact.tailC⁻¹ * kdevDir τ z)

/-- The `Sh`-coefficient of `Δ(τ)·Kdev8Bracket·Sh`. -/
def kdevSig2 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  Work.Kernels.DeltaFun τ
      * (((3456 : ℂ) * (Real.pi : ℂ))⁻¹ * Work.Asymptotics.Compact.brMinus ℓ 8 τ z)
    - Work.Asymptotics.Compact.tailC⁻¹
        * (Work.Kernels.phi2 τ * Work.Kernels.E14Fun τ * (z : ℂ) ^ 2 * Work.Kernels.DeltaFun z
            + Work.Kernels.DeltaFun τ * kdevNum0 τ z)

theorem Kdev8Bracket_eq_cleared (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ)
    (hSh : Work.Asymptotics.Compact.Sh τ z ≠ 0) :
    Work.Asymptotics.KhatE1Core.Kdev8Bracket ℓ τ z
      = Work.Asymptotics.Compact.tailC⁻¹ *
          (Work.Asymptotics.Compact.PhiMain τ z + Work.Asymptotics.Compact.PhiDiv τ z
            + Work.Asymptotics.Compact.PhiCorr τ z)
        - 2 * KdevLead ℓ τ * Work.Residues.Ept z
        + ((3456 : ℂ) * (Real.pi : ℂ))⁻¹ *
            ((Work.Asymptotics.Compact.Sh τ z)⁻¹ *
              (Work.Asymptotics.Compact.brMinus ℓ 8 τ z
                + Work.Asymptotics.Compact.Sh τ z * Work.Asymptotics.Compact.br0 8 ℓ τ z)) := by
  have hdec := Work.Asymptotics.Compact.decomp8 ℓ τ z hSh
  have href := Work.Asymptotics.Compact.Tref8_eq ℓ τ z
  have hp0 := Work.Asymptotics.KhatE1.R8_p0_eq_e1combo8 ℓ τ
  have hlead : ((3456 : ℂ) * (Real.pi : ℂ))⁻¹ *
        (Work.Residues.Ept z * Work.Asymptotics.Compact.R8_p0 ℓ τ)
      = 2 * KdevLead ℓ τ * Work.Residues.Ept z := by
    rw [hp0, KdevLead]; field_simp; ring
  have hDev : Work.Asymptotics.Compact.Dev8Sum ℓ τ z
      = (Work.Asymptotics.Compact.Sh τ z)⁻¹ *
          (Work.Asymptotics.Compact.brMinus ℓ 8 τ z
            + Work.Asymptotics.Compact.Sh τ z * Work.Asymptotics.Compact.br0 8 ℓ τ z)
        - Work.Asymptotics.Compact.Tref8 ℓ τ z := by
    rw [hdec]; ring
  simp only [Work.Asymptotics.KhatE1Core.Kdev8Bracket]
  rw [hDev, href]
  have e2 : ((3456 : ℂ) * (Real.pi : ℂ))⁻¹ *
        (Work.Residues.Ept z * (Work.Asymptotics.Compact.R8 ℓ τ z - Work.Asymptotics.Compact.R8_p0 ℓ τ)
          + ((Work.Asymptotics.Compact.Sh τ z)⁻¹ *
              (Work.Asymptotics.Compact.brMinus ℓ 8 τ z
                + Work.Asymptotics.Compact.Sh τ z * Work.Asymptotics.Compact.br0 8 ℓ τ z)
            - Work.Residues.Ept z * Work.Asymptotics.Compact.R8 ℓ τ z))
      = ((3456 : ℂ) * (Real.pi : ℂ))⁻¹ *
          ((Work.Asymptotics.Compact.Sh τ z)⁻¹ *
              (Work.Asymptotics.Compact.brMinus ℓ 8 τ z
                + Work.Asymptotics.Compact.Sh τ z * Work.Asymptotics.Compact.br0 8 ℓ τ z))
        - ((3456 : ℂ) * (Real.pi : ℂ))⁻¹ *
            (Work.Residues.Ept z * Work.Asymptotics.Compact.R8_p0 ℓ τ) := by
    ring
  rw [e2, hlead]
  ring

/-- `kdevNum0 = kdevNum + kdevDir·Sh` (`ring`, using `E₈ = E₄²`, `E₁₀ = E₄E₆`). -/
theorem kdevNum0_eq (τ z : ℍ) :
    kdevNum0 τ z = kdevNum τ z + kdevDir τ z * Work.Asymptotics.Compact.Sh τ z := by
  simp only [kdevNum0, kdevNum, kdevDir, Work.Asymptotics.Compact.Sh,
    Work.Kernels.E8Fun, Work.Kernels.E10Fun, Work.Kernels.E14Fun]
  ring


/-- **The polynomial bridge.**  `Δ(τ)·Kdev8Bracket·Sh = kdevA2·Sh + kdevSig2`.  (Pure algebra
from `Kdev8Bracket_eq_cleared`, `Delta_mul_Sh_mul_PhiSum`, `kdevNum0_eq`,
`DeltaFun_mul_jInvariantFun` and `R8_p0_eq_e1combo8`.) -/
theorem kdevBridge2 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ)
    (hSh : Work.Asymptotics.Compact.Sh τ z ≠ 0) :
    kdevA2 ℓ τ z * Work.Asymptotics.Compact.Sh τ z + kdevSig2 ℓ τ z
      = Work.Asymptotics.KhatE1Core.Kdev8Bracket ℓ τ z
          * (Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.Sh τ z) := by
  have hcl := Work.Asymptotics.KhatE1.Kdev8Bracket_eq_cleared ℓ τ z hSh
  have hsum := Work.Asymptotics.KhatE1Core.Delta_mul_Sh_mul_PhiSum τ z hSh
  have hclSh : Work.Asymptotics.KhatE1Core.Kdev8Bracket ℓ τ z
        * (Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.Sh τ z)
      = Work.Asymptotics.Compact.tailC⁻¹
          * (Work.Kernels.DeltaFun τ
              * (Work.Asymptotics.Compact.Sh τ z
                * (Work.Asymptotics.Compact.PhiMain τ z
                  + Work.Asymptotics.Compact.PhiDiv τ z
                  + Work.Asymptotics.Compact.PhiCorr τ z)))
        - 2 * Work.Asymptotics.KhatE1.KdevLead ℓ τ * Work.Residues.Ept z
            * (Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.Sh τ z)
        + ((3456 : ℂ) * (Real.pi : ℂ))⁻¹
            * (Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.brMinus ℓ 8 τ z
              + Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.Sh τ z
                  * Work.Asymptotics.Compact.br0 8 ℓ τ z) := by
    rw [hcl]
    field_simp
  rw [mul_assoc] at hsum
  simp only [kdevA2, kdevSig2, kdevDir]
  rw [hclSh, hsum, kdevNum0_eq,
    Work.Asymptotics.KhatE1.KdevLead, Work.Asymptotics.KhatE1.R8_p0_eq_e1combo8]
  simp only [kdevNum, kdevDir, Work.Asymptotics.Compact.Sh, Work.Kernels.E8Fun,
    Work.Kernels.E10Fun, Work.Kernels.E14Fun]
  rw [← Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun τ]
  ring

end

end Work.Asymptotics.KhatE1
