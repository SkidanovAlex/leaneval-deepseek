/-
# Definitions for the cusp expansion of the CKMRV kernel `z ↦ K^{(d)}(τ,z)` at `i∞`
-/
import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.ModerateGrowth
import Submission.Work.Asymptotics.cusp_L_second

noncomputable section

open UpperHalfPlane

namespace Work.Asymptotics.Compact

open Work.Kernels

/-- The cusp constant `c` of `𝓛`: the limit of `𝓛(z) - πiz` at `i∞`. -/
def cuspC (ℓ : Work.Kernels.LogLambdaData) : ℂ :=
  Classical.choose (Work.Asymptotics.cusp_L_second ℓ)

lemma cuspC_spec (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : UpperHalfPlane, 1 ≤ z.im →
      ‖ℓ.L z - ((Real.pi : ℂ) * Complex.I * (z : ℂ) + cuspC ℓ - 8 * Work.Residues.Ept z +
          12 * (Work.Residues.Ept z) ^ 2)‖ ≤ C * ‖Work.Residues.Ept z‖ ^ 3 :=
  Classical.choose_spec (Work.Asymptotics.cusp_L_second ℓ)

/-- `φ_0(τ) = τE₂(τ) - 3i/π`. -/
def phi1 (τ : UpperHalfPlane) : ℂ := (τ : ℂ) * E2Fun τ - 3 * Complex.I / (Real.pi : ℂ)

/-- `φ_2(τ) = τE₂(τ)² - (6i/π)E₂(τ)`. -/
def phi2t (τ : UpperHalfPlane) : ℂ :=
  (τ : ℂ) * E2Fun τ ^ 2 - (6 * Complex.I / (Real.pi : ℂ)) * E2Fun τ

/-- `𝒢_+^{(8)}`. -/
def Gplus8 (τ : UpperHalfPlane) (z : UpperHalfPlane) : ℂ :=
  (Real.pi : ℂ) ^ 2 / (36 * Complex.I) *
    (((τ : ℂ) * E6Fun τ - 2 * phi1 τ * E4Fun τ) * (z : ℂ) ^ 2 +
      (2 * phi1 τ * E4Fun τ) * ((z : ℂ) ^ 2 + 6 * (z : ℂ) / ((Real.pi : ℂ) * Complex.I)) -
      ((τ : ℂ) * E6Fun τ) *
        ((z : ℂ) ^ 2 + 12 * (z : ℂ) / ((Real.pi : ℂ) * Complex.I) - 36 / (Real.pi : ℂ) ^ 2))

/-- `𝒢_+^{(24)}`. -/
def Gplus24 (τ : UpperHalfPlane) (z : UpperHalfPlane) : ℂ :=
  (1 / (36 * 1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)) *
    (( (1 / ((Real.pi : ℂ) * Complex.I)) *
            (-72 * (τ : ℂ) * E14Fun τ + phi1 τ * DeltaFun τ *
                (144 * jInvariantFun τ - 124416) -
              72 * phi2t τ * E10Fun τ) * (z : ℂ) +
          (216 * (τ : ℂ) * E14Fun τ / (Real.pi : ℂ) ^ 2 -
            36 * phi1 τ * DeltaFun τ * (12 * jInvariantFun τ - 12096) /
              (Real.pi : ℂ) ^ 2 +
            216 * phi2t τ * E10Fun τ / (Real.pi : ℂ) ^ 2)) *
        (Work.Residues.Ept z) ^ (-2 : ℤ) +
      ( (20736 / ((Real.pi : ℂ) * Complex.I)) *
            (phi1 τ * E4Fun τ ^ 3 - 720 * phi1 τ * DeltaFun τ -
              (τ : ℂ) * E14Fun τ) * (z : ℂ) +
          (864 / (Real.pi : ℂ) ^ 2) *
            (78 * (τ : ℂ) * E14Fun τ -
              phi1 τ * DeltaFun τ * (12 * jInvariantFun τ - 12096) +
              6 * phi2t τ * E10Fun τ)))

/-- `𝒢_+^{(d)}`. -/
def Gplus (d : ℕ) (τ : UpperHalfPlane) (z : UpperHalfPlane) : ℂ :=
  if d = 8 then Gplus8 τ z else Gplus24 τ z

/-- `𝒢_-^{(8)}`. -/
def Gminus8 (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) (z : UpperHalfPlane) : ℂ :=
  (E4Fun τ * ((Real.pi : ℂ) * Complex.I * (z : ℂ) + cuspC ℓ) - psi4 ℓ τ / 2) / (Real.pi : ℂ)

/-- `𝒢_-^{(24)}`. -/
def Gminus24 (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) (z : UpperHalfPlane) : ℂ :=
  (1 / (2 * 1728 * (Real.pi : ℂ))) *
    (- ( -3456 * DeltaFun τ * ((Real.pi : ℂ) * Complex.I * (z : ℂ) + cuspC ℓ) +
            3456 * DeltaFun τ -
            3 * psi2 ℓ τ * E10Fun τ + 3 * psi4 ℓ τ * E8Fun τ) *
          (Work.Residues.Ept z) ^ (-2 : ℤ) +
        ( - ( -41472 * DeltaFun τ -
                3456 * DeltaFun τ * (jInvariantFun τ - 768) +
                psi2 ℓ τ * E10Fun τ * (3 * jInvariantFun τ - 1152) +
                psi4 ℓ τ * E8Fun τ * (2880 - 3 * jInvariantFun τ)) +
            (720 - jInvariantFun τ) *
              ( -3456 * DeltaFun τ * ((Real.pi : ℂ) * Complex.I * (z : ℂ) + cuspC ℓ) +
                3456 * DeltaFun τ -
                3 * psi2 ℓ τ * E10Fun τ + 3 * psi4 ℓ τ * E8Fun τ)))

/-- `𝒢_-^{(d)}`. -/
def Gminus (d : ℕ) (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) (z : UpperHalfPlane) : ℂ :=
  if d = 8 then Gminus8 ℓ τ z else Gminus24 ℓ τ z

/-- The coefficient functions `G_{i,j}` of the non-decaying part of `K^{(d)}`. -/
def Gcoef (d : ℕ) (ℓ : Work.Kernels.LogLambdaData) : Fin 2 → Fin 2 → UpperHalfPlane → ℂ :=
  if d = 8 then
    fun i j τ =>
      if i = 1 then 0
      else if j = 0 then
        (-Complex.I * (τ : ℂ) * E6Fun τ +
          (E4Fun τ * cuspC ℓ - psi4 ℓ τ / 2) / (Real.pi : ℂ)) / 2
      else
        ((Real.pi : ℂ) / 3 * ((τ : ℂ) * E6Fun τ - phi1 τ * E4Fun τ) +
          Complex.I * E4Fun τ) / 2
  else
    fun i j τ =>
      let E4 := E4Fun τ
      let E6 := E6Fun τ
      let D := DeltaFun τ
      let p0 := (τ : ℂ)
      let p1 := phi1 τ
      let p2 := phi2t τ
      let E14 := E4 ^ 2 * E6
      let E10 := E4 * E6
      let E8 := E4 ^ 2
      let ψ2 := psi2 ℓ τ
      let ψ4 := psi4 ℓ τ
      if i = 0 ∧ j = 0 then
        (-(13 * Complex.I / 12) * (p0 * E14) + (Complex.I / 6) * (p1 * E4 ^ 3)
            - 168 * Complex.I * (p1 * D) - (Complex.I / 12) * (p2 * E10)
            - 720 * D * cuspC ℓ / (Real.pi : ℂ) - 36 * D / (Real.pi : ℂ)
            + E4 ^ 3 * cuspC ℓ / (Real.pi : ℂ) - 7 * (ψ2 * E10) / (24 * (Real.pi : ℂ))
            - 5 * (ψ4 * E8) / (24 * (Real.pi : ℂ))) / 2
      else if i = 0 ∧ j = 1 then
        ((Real.pi : ℂ) / 3 * (p0 * E14 + 720 * (p1 * D) - p1 * E4 ^ 3)
            - Complex.I * (720 * D - E4 ^ 3)) / 2
      else if i = 1 ∧ j = 0 then
        (-(Complex.I / 288) * (p0 * E14 + p2 * E10) + (Complex.I / 144) * (p1 * E4 ^ 3)
            - 7 * Complex.I * (p1 * D) + D * (cuspC ℓ - 1) / (Real.pi : ℂ)
            + (ψ2 * E10 - ψ4 * E8) / (1152 * (Real.pi : ℂ))) / 2
      else
        ((Real.pi : ℂ) / 864 * (p0 * E14 + p2 * E10 + 1728 * (p1 * D) - 2 * (p1 * E4 ^ 3))
            + Complex.I * D) / 2

/-- The `Aexp`-shaped expression built from `Gcoef`. -/
def Gfun (d : ℕ) (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
  Gcoef d ℓ 0 0 τ + (z : ℂ) * Gcoef d ℓ 0 1 τ +
    (Work.Residues.Ept z) ^ (-2 : ℤ) *
      (Gcoef d ℓ 1 0 τ + (z : ℂ) * Gcoef d ℓ 1 1 τ)

end Work.Asymptotics.Compact
