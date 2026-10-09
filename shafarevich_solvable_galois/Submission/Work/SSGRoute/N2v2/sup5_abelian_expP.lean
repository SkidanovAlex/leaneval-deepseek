import Mathlib
import Submission.Work.SSGRoute.myv2.LevelE
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.N2v2

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- **The compositum of five abelian exponent-`p` levels over `↥K`, with all instances.** -/
theorem sup5_abelian_expP {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    (p : ℕ) [Fact p.Prime]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    (E₁ E₂ E₃ E₄ E₅ : IntermediateField ↥K Ω)
    [FiniteDimensional ↥K E₁] [IsGalois ↥K E₁] [IsMulCommutative (↥E₁ ≃ₐ[↥K] ↥E₁)]
    [NumberField ↥E₁]
    [FiniteDimensional ↥K E₂] [IsGalois ↥K E₂] [IsMulCommutative (↥E₂ ≃ₐ[↥K] ↥E₂)]
    [NumberField ↥E₂]
    [FiniteDimensional ↥K E₃] [IsGalois ↥K E₃] [IsMulCommutative (↥E₃ ≃ₐ[↥K] ↥E₃)]
    [NumberField ↥E₃]
    [FiniteDimensional ↥K E₄] [IsGalois ↥K E₄] [IsMulCommutative (↥E₄ ≃ₐ[↥K] ↥E₄)]
    [NumberField ↥E₄]
    [FiniteDimensional ↥K E₅] [IsGalois ↥K E₅] [IsMulCommutative (↥E₅ ≃ₐ[↥K] ↥E₅)]
    [NumberField ↥E₅]
    (h₁ : ∀ σ : (↥E₁ ≃ₐ[↥K] ↥E₁), σ ^ p = 1)
    (h₂ : ∀ σ : (↥E₂ ≃ₐ[↥K] ↥E₂), σ ^ p = 1)
    (h₃ : ∀ σ : (↥E₃ ≃ₐ[↥K] ↥E₃), σ ^ p = 1)
    (h₄ : ∀ σ : (↥E₄ ≃ₐ[↥K] ↥E₄), σ ^ p = 1)
    (h₅ : ∀ σ : (↥E₅ ≃ₐ[↥K] ↥E₅), σ ^ p = 1) :
    ∃ (E : IntermediateField ↥K Ω) (_ : FiniteDimensional ↥K E) (_ : IsGalois ↥K E)
      (_ : IsMulCommutative (↥E ≃ₐ[↥K] ↥E)) (_ : NumberField ↥E),
      E₁ ≤ E ∧ E₂ ≤ E ∧ E₃ ≤ E ∧ E₄ ≤ E ∧ E₅ ≤ E ∧
        ∀ σ : (↥E ≃ₐ[↥K] ↥E), σ ^ p = 1 := by
  -- Iterate the binary step `sup_abelian_expP` four times, adjoining `E₃, E₄, E₅` in turn.
  obtain ⟨E₁₂, hfd₁₂, hgal₁₂, hcomm₁₂, hnf₁₂, hle₁₂₁, hle₁₂₂, hexp₁₂⟩ :=
    sup_abelian_expP (k := k) (Ω := Ω) p K E₁ E₂ h₁ h₂
  haveI := hfd₁₂
  haveI := hgal₁₂
  haveI := hcomm₁₂
  haveI := hnf₁₂
  obtain ⟨E₁₂₃, hfd₁₂₃, hgal₁₂₃, hcomm₁₂₃, hnf₁₂₃, hle₁₂₃a, hle₁₂₃b, hexp₁₂₃⟩ :=
    sup_abelian_expP (k := k) (Ω := Ω) p K E₁₂ E₃ hexp₁₂ h₃
  haveI := hfd₁₂₃
  haveI := hgal₁₂₃
  haveI := hcomm₁₂₃
  haveI := hnf₁₂₃
  obtain ⟨E₁₂₃₄, hfd₁₂₃₄, hgal₁₂₃₄, hcomm₁₂₃₄, hnf₁₂₃₄, hle₁₂₃₄a, hle₁₂₃₄b, hexp₁₂₃₄⟩ :=
    sup_abelian_expP (k := k) (Ω := Ω) p K E₁₂₃ E₄ hexp₁₂₃ h₄
  haveI := hfd₁₂₃₄
  haveI := hgal₁₂₃₄
  haveI := hcomm₁₂₃₄
  haveI := hnf₁₂₃₄
  obtain ⟨E₁₂₃₄₅, hfd₁₂₃₄₅, hgal₁₂₃₄₅, hcomm₁₂₃₄₅, hnf₁₂₃₄₅, hle₁₂₃₄₅a, hle₁₂₃₄₅b,
    hexp₁₂₃₄₅⟩ :=
    sup_abelian_expP (k := k) (Ω := Ω) p K E₁₂₃₄ E₅ hexp₁₂₃₄ h₅
  refine ⟨E₁₂₃₄₅, hfd₁₂₃₄₅, hgal₁₂₃₄₅, hcomm₁₂₃₄₅, hnf₁₂₃₄₅, ?_, ?_, ?_, ?_, ?_,
    hexp₁₂₃₄₅⟩
  · exact le_trans (le_trans (le_trans hle₁₂₁ hle₁₂₃a) hle₁₂₃₄a) hle₁₂₃₄₅a
  · exact le_trans (le_trans (le_trans hle₁₂₂ hle₁₂₃a) hle₁₂₃₄a) hle₁₂₃₄₅a
  · exact le_trans (le_trans hle₁₂₃b hle₁₂₃₄a) hle₁₂₃₄₅a
  · exact le_trans hle₁₂₃₄b hle₁₂₃₄₅a
  · exact hle₁₂₃₄₅b

end Work.SSGRoute.N2v2
