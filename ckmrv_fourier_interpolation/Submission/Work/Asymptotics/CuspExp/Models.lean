/-
# The explicit truncated models of the CKMRV kernel's cusp expansion

With `q = e^{2πiz}` and `E = e^{πiz}` (so `q = E²`, `‖E‖ = e^{-π Im z}`), the cusp-`i∞`
expansion of the CKMRV kernel is obtained by replacing each atom of the (explicit) kernel by
its truncated expansion:

`E₄(z) ↦ 1 + 240q`,  `E₆(z) ↦ 1 - 504q`,  `E₈ ↦ (1+240q)²`, `E₁₀ ↦ (1+240q)(1-504q)`,
`E₁₄ ↦ (1+240q)²(1-504q)`,  `1/Δ(z) ↦ E⁻² + 24`,  `(j(τ)-j(z))⁻¹ ↦ -q + (744-j(τ))q²`,
`(Δ(z)(j(τ)-j(z)))⁻¹ ↦ -1 + (720-j(τ))q`,  `G(z) = zE₂(z)-6i/π ↦ (z-6i/π) - 24zq`,
`U(z) ↦ 1+8E+24q`,  `W(z) ↦ 1-8E+24q`,  `U(z)²-V(z)² ↦ 1+16E-144q`,
`𝓛(z) ↦ πiz + c - 8E + 12q`,  `𝓛_S(z) ↦ -16E`.

This file defines these models and the resulting models `MP8`, `MM8`, `MP24`, `MM24` of the
four kernels `K₊^{(8)}`, `K₋^{(8)}`, `K₊^{(24)}`, `K₋^{(24)}; the expansion statements
(the differences are `O(‖E‖)` uniformly on `K ⊆ 𝒟`) live in the sibling files.
-/
import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.TildeFacts.KPlus_z_tildeA
import Submission.Work.Residues.ThetaEpt
import Submission.Work.Asymptotics.GcuspDefs

namespace Work.Asymptotics

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

noncomputable section

/-! ## The models of the `z`-atoms -/

/-- `q(z) = e^{2πiz} = E(z)²`. -/
def mq (z : ℍ) : ℂ := Work.Kernels.qParamFun z

/-- The model of `G(z) = zE₂(z) - 6i/π`. -/
def mG (z : ℍ) : ℂ := ((z : ℂ) - 6 * Complex.I / (Real.pi : ℂ)) - 24 * (z : ℂ) * mq z

/-- The model of `1/Δ(z)`. -/
def minvD (z : ℍ) : ℂ := (Work.Residues.Ept z)⁻¹ ^ 2 + 24

/-- The model of `E₄(z)`. -/
def mE4 (z : ℍ) : ℂ := 1 + 240 * mq z

/-- The model of `E₆(z)`. -/
def mE6 (z : ℍ) : ℂ := 1 - 504 * mq z

/-- The model of `E₈(z) = E₄(z)²`. -/
def mE8 (z : ℍ) : ℂ := mE4 z * mE4 z

/-- The model of `E₁₀(z) = E₄(z)E₆(z)`. -/
def mE10 (z : ℍ) : ℂ := mE4 z * mE6 z

/-- The model of `E₁₄(z) = E₄(z)²E₆(z)`. -/
def mE14 (z : ℍ) : ℂ := mE4 z * mE4 z * mE6 z

/-- The model of `E₁₄(z)/Δ(z)`. -/
def mE14D (z : ℍ) : ℂ := mE14 z * minvD z

/-- The model of `E₁₀(z)/Δ(z)`. -/
def mE10D (z : ℍ) : ℂ := mE10 z * minvD z

/-- The model of `U(z) = θ₀₀(z)⁴`. -/
def mU (z : ℍ) : ℂ := 1 + 8 * Work.Residues.Ept z + 24 * mq z

/-- The model of `W(z) = θ₀₁(z)⁴`. -/
def mW (z : ℍ) : ℂ := 1 - 8 * Work.Residues.Ept z + 24 * mq z

/-- The model of `U(z)² - V(z)²`. -/
def mD (z : ℍ) : ℂ := 1 + 16 * Work.Residues.Ept z - 144 * mq z

/-- The model of `𝓛_S(z)`. -/
def mL_S (z : ℍ) : ℂ := -16 * Work.Residues.Ept z

/-- The model of `(j(τ)-j(z))⁻¹`. -/
def minvJ (τ z : ℍ) : ℂ := -mq z + (744 - Work.Kernels.jInvariantFun τ) * mq z ^ 2

/-- The model of `(Δ(z)(j(τ)-j(z)))⁻¹`. -/
def mR (τ z : ℍ) : ℂ := -1 + (720 - Work.Kernels.jInvariantFun τ) * mq z

/-! ## The models of the τ-atoms (untouched by the expansion) -/

/-- `φ_{-2}(τ) = τ`. -/
def tphi0 (τ : ℍ) : ℂ := Work.Kernels.phiVec τ 0

/-- `φ_0(τ)`. -/
def tphi1 (τ : ℍ) : ℂ := Work.Kernels.phiVec τ 1

/-- `φ_2(τ)`. -/
def tphi2 (τ : ℍ) : ℂ := Work.Kernels.phiVec τ 2

/-! ## The models of the four kernels -/

variable (ℓ : Work.Kernels.LogLambdaData)

/-- The model of `K₊^{(8)}`. -/
def MP8 (τ z : ℍ) : ℂ :=
  ((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)⁻¹ *
    ( tphi0 τ * Work.Kernels.E6Fun τ * (z : ℂ) ^ 2
      + tphi0 τ * Work.Kernels.E6Fun τ * mE8 z * (mG z) ^ 2 * mR τ z
      - 2 * tphi1 τ * Work.Kernels.E4Fun τ * (z : ℂ) ^ 2
      - 2 * tphi1 τ * Work.Kernels.E4Fun τ * mE10 z * ((z : ℂ) * mG z) * mR τ z
      + tphi2 τ * (Work.Kernels.E14Fun τ / Work.Kernels.DeltaFun τ) * (z : ℂ) ^ 2 * minvJ τ z)

/-- The model of `K₋^{(8)}`. -/
def MM8 (τ z : ℍ) : ℂ :=
  ((2 : ℂ) * 1728 * (Real.pi : ℂ))⁻¹ * mR τ z *
    ( (-3456) * Work.Kernels.E4Fun τ * mE10 z * (Real.pi * Complex.I * (z : ℂ)
          + cuspL ℓ - 8 * Work.Residues.Ept z + 12 * mq z)
      + Work.Kernels.psi2 ℓ τ * (Work.Kernels.E14Fun τ / Work.Kernels.DeltaFun τ) *
          (mE8 z * mW z - mE6 z * mD z)
      + Work.Kernels.psi4 ℓ τ *
          ((1728 - Work.Kernels.jInvariantFun τ) * mE8 z * mW z
            + Work.Kernels.jInvariantFun τ * mE6 z * mD z) )

/-- The model of `K₊^{(24)}`. -/
def MP24 (τ z : ℍ) : ℂ :=
  ((36 : ℂ) * 1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)⁻¹ * minvD z *
    ( 6 * tphi0 τ * Work.Kernels.E14Fun τ * mE4 z * (z : ℂ) ^ 2
      + tphi0 τ * Work.Kernels.E14Fun τ * (1728 * minvJ τ z - 6) * (mG z) ^ 2
      + tphi1 τ * Work.Kernels.DeltaFun τ
          * (-12 * Work.Kernels.jInvariantFun τ + 5 * 1728) * mE4 z * (z : ℂ) ^ 2
      + tphi1 τ * Work.Kernels.DeltaFun τ * (-2 * 1728 * minvJ τ z)
          * mE14D z * ((z : ℂ) * mG z)
      + tphi1 τ * Work.Kernels.DeltaFun τ
          * (12 * Work.Kernels.jInvariantFun τ - 7 * 1728) * (mG z) ^ 2
      + tphi2 τ * Work.Kernels.E10Fun τ * (1728 * minvJ τ z + 6) * mE4 z * (z : ℂ) ^ 2
      + tphi2 τ * Work.Kernels.E10Fun τ * (-6) * (mG z) ^ 2 )

/-- The model of `K₋^{(24)}`. -/
def MM24 (τ z : ℍ) : ℂ :=
  ((2 : ℂ) * 1728 * (Real.pi : ℂ))⁻¹ *
    ( Work.Kernels.DeltaFun τ *
        ((-2 * 1728) * mE14D z * (Real.pi * Complex.I * (z : ℂ)
            + cuspL ℓ - 8 * Work.Residues.Ept z + 12 * mq z) * mR τ z
          - 2 * 1728 * mW z * minvD z)
      + Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ
          * (Work.Kernels.jInvariantFun τ * mR τ z + 2 * minvD z) * mW z
      - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ * mE10D z * mD z * mR τ z
      + Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
          * (1728 * mR τ z - 2 * minvD z - Work.Kernels.jInvariantFun τ * mR τ z) * mW z
      + Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ * mE10D z * mD z * mR τ z )

/-- The non-decaying part `𝒢(τ,z) = G_{0,0} + zG_{0,1} + q⁻¹(G_{1,0} + zG_{1,1})` of the cusp
expansion, as a function of `z ∈ ℍ` (at `z = it` it is `Aexp G τ t`). -/
def AexpZ (G : Fin 2 → Fin 2 → ℍ → ℂ) (τ z : ℍ) : ℂ :=
  G 0 0 τ + (z : ℂ) * G 0 1 τ + (mq z)⁻¹ * (G 1 0 τ + (z : ℂ) * G 1 1 τ)

/-- On the imaginary axis `AexpZ` is `Aexp`. -/
lemma AexpZ_imagAxis (G : Fin 2 → Fin 2 → ℍ → ℂ) (τ : ℍ) (t : ℝ) (ht : 0 < t) :
    AexpZ G τ (Work.Kernels.imagAxis t ht) = Aexp G τ t := by
  have hcoe : ((Work.Kernels.imagAxis t ht : ℍ) : ℂ) = (t : ℂ) * Complex.I := rfl
  have hq : (mq (Work.Kernels.imagAxis t ht))⁻¹ = Complex.exp (2 * Real.pi * t) := by
    unfold mq Work.Kernels.qParamFun
    rw [hcoe]
    have h1 : (2 : ℂ) * (Real.pi : ℂ) * Complex.I * ((t : ℂ) * Complex.I)
        = -((2 * Real.pi * t : ℝ) : ℂ) := by
      calc (2 : ℂ) * (Real.pi : ℂ) * Complex.I * ((t : ℂ) * Complex.I)
          = 2 * (Real.pi : ℂ) * (t : ℂ) * (Complex.I * Complex.I) := by ring
        _ = 2 * (Real.pi : ℂ) * (t : ℂ) * (-1) := by rw [Complex.I_mul_I]
        _ = -((2 * Real.pi * t : ℝ) : ℂ) := by push_cast; ring
    rw [h1, Complex.exp_neg, inv_inv]
    congr 1
    push_cast
    ring
  unfold AexpZ Aexp
  rw [hq, hcoe]

/-- The model of `K^{(d)} = (K₊^{(d)} + K₋^{(d)})/2`. -/
def MK (d : ℕ) (τ z : ℍ) : ℂ :=
  if d = 8 then (MP8 τ z + MM8 ℓ τ z) / 2 else (MP24 τ z + MM24 ℓ τ z) / 2

end

end Work.Asymptotics
