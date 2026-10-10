import Mathlib
import Submission.Work.MotC5N3.LamAS.asF_transfer
import Submission.Work.MotC5N3.LamAS.asIota_range
import Submission.Work.MotV5.LamAS.linearDisjoint_of_isGalois_of_inf_bot

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC5N3.LamAS

/-- The range of the algebra map out of an intermediate field is its underlying subalgebra. -/
theorem range_toAlgHom_eq_toSubalgebra {R E : Type*} [Field R] [Field E] [Algebra R E]
    (S : IntermediateField R E) :
    (IsScalarTower.toAlgHom R ↥S E).range = S.toSubalgebra := by
  rw [show IsScalarTower.toAlgHom R ↥S E = S.val from rfl, IntermediateField.range_val]

/-- The twist field of a class `g ∈ {f₁, f₂}`, pulled back to `M = L(E)` along the base-change map
`asIota`, is linearly disjoint from the constants `L` over `K`. -/
theorem asF_linearDisjoint (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] {K : Type} [Field K] [Algebra 𝕜 K]
    [CharP K 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (f₁ f₂ g : K)
    (τ : OmA K D ≃ₐ[K] OmA K D)
    (σS : OmA K D ≃ₐ[KbA K] OmA K D)
    (σ : KbA K ≃ₐ[K] KbA K)
    [hGal : IsGalois K ↥(asL2 f₁ f₂)] [hFin : FiniteDimensional K ↥(asL2 f₁ f₂)]
    (h : ASTwistData 𝕜 D g τ σS σ) (hg : g = f₁ ∨ g = f₂) :
    (asF D f₁ f₂ g τ σS).LinearDisjoint
      ↥(asL2 f₁ f₂) := by
  have hRange : (asIota D f₁ f₂).fieldRange =
      Work.MotC5N3.kleinField K D ⊔ LImage D (asL2 f₁ f₂) :=
    asIota_range 𝕜 D hD f₁ f₂
  obtain ⟨-, -, hinf⟩ := asF_transfer 𝕜 D hD f₁ f₂ g τ σS σ h hg hRange
  haveI hGalL : IsGalois K ↥(asLImageM D f₁ f₂) :=
    IsGalois.of_algEquiv (AlgHom.equivFieldRange (IsScalarTower.toAlgHom K
      ↥(asL2 f₁ f₂) (asML D f₁ f₂)))
  haveI hFinL : FiniteDimensional K ↥(asLImageM D f₁ f₂) :=
    (AlgHom.equivFieldRange (IsScalarTower.toAlgHom K
      ↥(asL2 f₁ f₂) (asML D f₁ f₂))).toLinearEquiv.finiteDimensional
  have hLI : (asLImageM D f₁ f₂).LinearDisjoint ↥(asF D f₁ f₂ g τ σS) :=
    Work.MotV5.LamAS.linearDisjoint_of_isGalois_of_inf_bot (A := asLImageM D f₁ f₂)
      (B := asF D f₁ f₂ g τ σS) (by rw [inf_comm]; exact hinf)
  rw [IntermediateField.linearDisjoint_iff]
  rw [show (IsScalarTower.toAlgHom K ↥(asL2 f₁ f₂)
      (asML D f₁ f₂)).range = (asLImageM D f₁ f₂).toSubalgebra from rfl]
  rw [IntermediateField.linearDisjoint_iff] at hLI
  rw [range_toAlgHom_eq_toSubalgebra] at hLI
  exact Subalgebra.LinearDisjoint.symm hLI

end Work.MotC5N3.LamAS
