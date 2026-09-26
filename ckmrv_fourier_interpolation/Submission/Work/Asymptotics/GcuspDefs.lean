/-
# The coefficient functions of the CKMRV cusp expansion

Definitions shared by `Submission/Work/Asymptotics/Kaxis_local_tail.lean` and the lemmas about
it (`GcuspInP`, `cuspExpansionKernel`).  See the docstring of
`Submission/Work/Asymptotics/Kaxis_local_tail.lean` for the derivation of the formulas.
-/
import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.ModerateGrowth
import Submission.Work.Asymptotics.cusp_invDelta
import Submission.Work.Asymptotics.cusp_U_second
import Submission.Work.Asymptotics.cusp_W_second
import Submission.Work.Asymptotics.cusp_D_second
import Submission.Work.Asymptotics.cusp_L_second
import Submission.Work.Kernels.TildeFacts.theta_quartic

namespace Work.Asymptotics

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped Topology MatrixGroups ModularForm Modular Manifold Bundle

noncomputable section

/-! ## The coefficient functions of the expansion -/

/-- `c₈ = 1/(36 π⁻² i)`, the prefactor of `Υ_+^{(8)}`. -/
def cuspC8 : ℂ := ((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)⁻¹

/-- `c₂₄ = 1/(36·1728·π⁻²·i)`, the prefactor of `Υ_+^{(24)}`. -/
def cuspC24 : ℂ := ((36 : ℂ) * 1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)⁻¹

/-- The constant `c_L` of the cusp expansion `ℓ.L z = πiz + c_L - 8E + 12E² + O(E³)`
(of `cusp_L_second`). -/
def cuspL (ℓ : Work.Kernels.LogLambdaData) : ℂ :=
  Classical.choose (cusp_L_second ℓ)

variable (ℓ : Work.Kernels.LogLambdaData)

/-- The `d = 8` coefficient functions.  (`G 1 j = 0` since the kernel has no `e^{2πt}` term in
eight dimensions.) -/
def Gcusp8 (i j : Fin 2) (τ : ℍ) : ℂ :=
  if i = 1 then 0
  else if j = 0 then
    (Work.Kernels.phiVec τ 0 * Work.Kernels.E6Fun τ * (-Complex.I)
        + Work.Kernels.E4Fun τ * cuspL ℓ / (Real.pi : ℂ)
        - Work.Kernels.psi4 ℓ τ / (2 * (Real.pi : ℂ))) / 2
  else
    ((Real.pi : ℂ) / 3 * (Work.Kernels.phiVec τ 0 * Work.Kernels.E6Fun τ
        - Work.Kernels.phiVec τ 1 * Work.Kernels.E4Fun τ)
        + Complex.I * Work.Kernels.E4Fun τ) / 2

/-- The `d = 24` coefficient functions. -/
def Gcusp24 (i j : Fin 2) (τ : ℍ) : ℂ :=
  let E4 := Work.Kernels.E4Fun τ
  let E6 := Work.Kernels.E6Fun τ
  let Δ := Work.Kernels.DeltaFun τ
  let p0 := Work.Kernels.phiVec τ 0
  let p1 := Work.Kernels.phiVec τ 1
  let p2 := Work.Kernels.phiVec τ 2
  let E14 := E4 ^ 2 * E6
  let E10 := E4 * E6
  let E8 := E4 ^ 2
  let ψ2 := Work.Kernels.psi2 ℓ τ
  let ψ4 := Work.Kernels.psi4 ℓ τ
  if i = 0 ∧ j = 0 then
    (-(13 * Complex.I / 12) * (p0 * E14) + (Complex.I / 6) * (p1 * E4 ^ 3)
        - 168 * Complex.I * (p1 * Δ) - (Complex.I / 12) * (p2 * E10)
        - 720 * Δ * cuspL ℓ / (Real.pi : ℂ) - 36 * Δ / (Real.pi : ℂ)
        + E4 ^ 3 * cuspL ℓ / (Real.pi : ℂ) - 7 * (ψ2 * E10) / (24 * (Real.pi : ℂ))
        - 5 * (ψ4 * E8) / (24 * (Real.pi : ℂ))) / 2
  else if i = 0 ∧ j = 1 then
    ((Real.pi : ℂ) / 3 * (p0 * E14 + 720 * (p1 * Δ) - p1 * E4 ^ 3)
        - Complex.I * (720 * Δ - E4 ^ 3)) / 2
  else if i = 1 ∧ j = 0 then
    (-(Complex.I / 288) * (p0 * E14 + p2 * E10) + (Complex.I / 144) * (p1 * E4 ^ 3)
        - 7 * Complex.I * (p1 * Δ) + Δ * (cuspL ℓ - 1) / (Real.pi : ℂ)
        + (ψ2 * E10 - ψ4 * E8) / (1152 * (Real.pi : ℂ))) / 2
  else
    ((Real.pi : ℂ) / 864 * (p0 * E14 + p2 * E10 + 1728 * (p1 * Δ) - 2 * (p1 * E4 ^ 3))
        + Complex.I * Δ) / 2

/-- The coefficient functions of the cusp expansion of `K^{(d)}`: `Gcusp8` in dimension `8` and
`Gcusp24` in dimension `24`. -/
def Gcusp (d : ℕ) : Fin 2 → Fin 2 → ℍ → ℂ :=
  if d = 8 then Gcusp8 ℓ else Gcusp24 ℓ


/-! ## Moderate growth of the atoms (private helpers) -/

private lemma InP_coe : Work.Kernels.InP (fun τ : ℍ => (τ : ℂ)) := by
  refine ⟨by simpa using UpperHalfPlane.mdifferentiable_coe, ?_⟩
  refine ⟨1, 0, 1, by norm_num, by norm_num, by norm_num, fun τ _ => ?_⟩
  simp only [Real.rpow_zero, Real.rpow_one, mul_one]
  exact le_trans (le_abs_self _) (by simp)

private lemma InP_xi2 : Work.Kernels.InP Work.Kernels.xi2Fun := by
  have h : Work.Kernels.xi2Fun
      = fun τ : ℍ => Work.Kernels.UFun τ + Work.Kernels.WFun τ := rfl
  rw [h]
  exact (Work.Kernels.InP.pow Work.Kernels.ClassicalFacts.theta00Fun_mem_InP 4).add
    (Work.Kernels.InP.pow Work.Kernels.ClassicalFacts.theta01Fun_mem_InP 4)

private lemma InP_xi4 : Work.Kernels.InP Work.Kernels.xi4Fun := by
  have h : Work.Kernels.xi4Fun
      = fun τ : ℍ => Work.Kernels.UFun τ ^ 2 + Work.Kernels.WFun τ ^ 2 -
          2 * Work.Kernels.VFun τ ^ 2 := rfl
  rw [h]
  exact ((Work.Kernels.InP.pow (Work.Kernels.InP.pow
        Work.Kernels.ClassicalFacts.theta00Fun_mem_InP 4) 2).add
      (Work.Kernels.InP.pow (Work.Kernels.InP.pow
        Work.Kernels.ClassicalFacts.theta01Fun_mem_InP 4) 2)).sub
    (Work.Kernels.InP.const_mul 2 (Work.Kernels.InP.pow (Work.Kernels.InP.pow
      Work.Kernels.ClassicalFacts.theta10Fun_mem_InP 4) 2))

private lemma InP_psi2 (ℓ : Work.Kernels.LogLambdaData) : Work.Kernels.InP (Work.Kernels.psi2 ℓ) := by
  have hL : Work.Kernels.InP ℓ.L := ⟨ℓ.holo, ℓ.memP⟩
  have hLS : Work.Kernels.InP ℓ.L_S := ⟨ℓ.holo_S, ℓ.memP_S⟩
  have h : Work.Kernels.psi2 ℓ = fun τ : ℍ => Work.Kernels.xi2Fun τ * ℓ.L τ +
      (Work.Kernels.xi2Fun ∣[(2 : ℤ)] ModularGroup.S) τ * ℓ.L_S τ := rfl
  rw [h]
  exact (InP_xi2.mul hL).add ((InP_xi2.slash (2 : ℤ) ModularGroup.S).mul hLS)

private lemma InP_psi4 (ℓ : Work.Kernels.LogLambdaData) : Work.Kernels.InP (Work.Kernels.psi4 ℓ) := by
  have hL : Work.Kernels.InP ℓ.L := ⟨ℓ.holo, ℓ.memP⟩
  have hLS : Work.Kernels.InP ℓ.L_S := ⟨ℓ.holo_S, ℓ.memP_S⟩
  have h : Work.Kernels.psi4 ℓ = fun τ : ℍ => Work.Kernels.xi4Fun τ * ℓ.L τ +
      (Work.Kernels.xi4Fun ∣[(4 : ℤ)] ModularGroup.S) τ * ℓ.L_S τ := rfl
  rw [h]
  exact (InP_xi4.mul hL).add ((InP_xi4.slash (4 : ℤ) ModularGroup.S).mul hLS)


end

end Work.Asymptotics
