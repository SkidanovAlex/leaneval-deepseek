import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.NumberTheory.NumberField.Basic
import Submission.Work.SSGRoute.myv2.sup_isMulCommutative
import Submission.Work.SSGRoute.myv2.sup_pow_eq_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The compositum of two abelian exponent-`p` levels, with all instances

The level `E = M ⊔ F_a ⊔ F_{c₁} ⊔ F_{c₂} ⊔ F_{b_g}` of the `hsplit` orthogonality must carry the
instances `FiniteDimensional`/`IsGalois`/`IsMulCommutative`/`NumberField` and have exponent `p` (for
the existence of the idèlic Artin map and for "`p`-th powers die").  This file provides the binary
step, to be iterated; the two inputs are the delegated `sup_isMulCommutative` and `sup_pow_eq_one`.
-/

open scoped NumberField

namespace Work.SSGRoute.N2v2

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]

/-- **The compositum of two abelian exponent-`p` levels over `↥K`, with all instances.** -/
theorem sup_abelian_expP (p : ℕ) [Fact p.Prime]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    (E₁ E₂ : IntermediateField ↥K Ω) [FiniteDimensional ↥K E₁] [IsGalois ↥K E₁]
    [IsMulCommutative (↥E₁ ≃ₐ[↥K] ↥E₁)] [FiniteDimensional ↥K E₂] [IsGalois ↥K E₂]
    [IsMulCommutative (↥E₂ ≃ₐ[↥K] ↥E₂)] [NumberField ↥E₁] [NumberField ↥E₂]
    (h₁ : ∀ σ : (↥E₁ ≃ₐ[↥K] ↥E₁), σ ^ p = 1)
    (h₂ : ∀ σ : (↥E₂ ≃ₐ[↥K] ↥E₂), σ ^ p = 1) :
    ∃ (E : IntermediateField ↥K Ω) (_ : FiniteDimensional ↥K E) (_ : IsGalois ↥K E)
      (_ : IsMulCommutative (↥E ≃ₐ[↥K] ↥E)) (_ : NumberField ↥E),
      E₁ ≤ E ∧ E₂ ≤ E ∧ ∀ σ : (↥E ≃ₐ[↥K] ↥E), σ ^ p = 1 := by
  haveI hfd : FiniteDimensional ↥K ↥(E₁ ⊔ E₂) := IntermediateField.finiteDimensional_sup E₁ E₂
  haveI hgal : IsGalois ↥K ↥(E₁ ⊔ E₂) := inferInstance
  haveI hcomm : IsMulCommutative (↥(E₁ ⊔ E₂) ≃ₐ[↥K] ↥(E₁ ⊔ E₂)) :=
    Work.SSGRoute.myv2.sup_isMulCommutative K E₁ E₂
  haveI hnf : NumberField ↥(E₁ ⊔ E₂) := NumberField.of_module_finite ↥K ↥(E₁ ⊔ E₂)
  exact ⟨E₁ ⊔ E₂, hfd, hgal, hcomm, hnf, le_sup_left, le_sup_right,
    Work.SSGRoute.myv2.sup_pow_eq_one K E₁ E₂ p h₁ h₂⟩

end Work.SSGRoute.N2v2
