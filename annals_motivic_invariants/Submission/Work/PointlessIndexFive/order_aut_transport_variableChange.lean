import Mathlib
import Submission.Work.Arithmetic.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.PointlessIndexFive

/-- Conjugating a variable change by `C₀` transports the automorphism group of `W` to that
of `W' = C₀ • W`.  Hence the exponent bound `orderOf τ ∣ 2 ∨ orderOf τ ∣ 6` transfers from
`Aut 𝕜 W'` back to `Aut 𝕜 W`. -/
theorem order_aut_transport_variableChange {𝕜 : Type} [Field 𝕜]
    {W W' : WeierstrassCurve 𝕜} (C₀ : WeierstrassCurve.VariableChange 𝕜) (hC₀ : C₀ • W = W')
    (hW' : ∀ τ : Work.Arithmetic.Aut 𝕜 W', orderOf τ ∣ 2 ∨ orderOf τ ∣ 6) :
    ∀ σ : Work.Arithmetic.Aut 𝕜 W, orderOf σ ∣ 2 ∨ orderOf σ ∣ 6 := by
  intro σ
  have hσ : (σ : WeierstrassCurve.VariableChange 𝕜) • W = W := σ.2
  have hconj : (C₀ * (σ : WeierstrassCurve.VariableChange 𝕜) * C₀⁻¹) • W' = W' := by
    rw [mul_smul, mul_smul]
    have : C₀⁻¹ • W' = W := by
      rw [← hC₀, ← mul_smul, inv_mul_cancel, one_smul]
    rw [this, hσ, hC₀]
  let τ : Work.Arithmetic.Aut 𝕜 W' :=
    ⟨C₀ * (σ : WeierstrassCurve.VariableChange 𝕜) * C₀⁻¹, hconj⟩
  have hord : orderOf τ = orderOf σ := by
    have h1 : orderOf (τ : WeierstrassCurve.VariableChange 𝕜) = orderOf τ :=
      Subgroup.orderOf_coe τ
    have h2 : orderOf ((σ : WeierstrassCurve.VariableChange 𝕜)) = orderOf σ :=
      Subgroup.orderOf_coe σ
    rw [← h1, ← h2]
    show orderOf (C₀ * (σ : WeierstrassCurve.VariableChange 𝕜) * C₀⁻¹) =
      orderOf (σ : WeierstrassCurve.VariableChange 𝕜)
    exact (SemiconjBy.orderOf_eq C₀
      (x := (σ : WeierstrassCurve.VariableChange 𝕜))
      (y := C₀ * (σ : WeierstrassCurve.VariableChange 𝕜) * C₀⁻¹)
      (by unfold SemiconjBy; group)).symm
  rcases hW' τ with h | h
  · left; rwa [hord] at h
  · right; rwa [hord] at h

end Work.PointlessIndexFive
