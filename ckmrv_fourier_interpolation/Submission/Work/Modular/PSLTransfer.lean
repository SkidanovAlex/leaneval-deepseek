import Submission.Work.Modular.GroupAlgebra

/-!
# The group algebra of `PSL(2, ℤ)` and the ideal `I` of the paper

The paper works with the group algebra `R = ℂ[PSL(2, ℤ)]` (the element `-I ∈ SL(2, ℤ)` acts
trivially on `ℍ`) and the right ideal `I = (T - I)^2 · R + S (T - I)^2 · R`.  This file sets up
those objects; `quotient_basis_PSL` transfers the six-dimensionality result
`quotient_basis` (proved for the abstract group `Γ = ⟨S, T | S² = (ST)³ = 1⟩`) to `ℂ[PSL(2, ℤ)]`
along the classical presentation isomorphism `presentedGroup_equiv_PSL`.
-/

noncomputable section

open scoped MonoidAlgebra MatrixGroups

namespace Work.Modular

/-- The group algebra `ℂ[PSL(2, ℤ)]`. -/
abbrev PSLGroupRing : Type := MonoidAlgebra ℂ (Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℤ)

/-- The image of the generator `S` in `PSL(2, ℤ)`. -/
def pslS : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℤ := QuotientGroup.mk ModularGroup.S

/-- The image of the generator `T` in `PSL(2, ℤ)`. -/
def pslT : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℤ := QuotientGroup.mk ModularGroup.T

/-- `S` as an element of `ℂ[PSL(2, ℤ)]`. -/
def pslSR : PSLGroupRing := MonoidAlgebra.of ℂ _ pslS

/-- `T` as an element of `ℂ[PSL(2, ℤ)]`. -/
def pslTR : PSLGroupRing := MonoidAlgebra.of ℂ _ pslT

/-- The right ideal `I = (T - 1) ^ 2 · ℂ[PSL(2, ℤ)] + S (T - 1) ^ 2 · ℂ[PSL(2, ℤ)]`. -/
def idealPSL : Submodule ℂ PSLGroupRing :=
  Submodule.span ℂ {x : PSLGroupRing |
    (∃ r : PSLGroupRing, x = (pslTR - 1) ^ 2 * r) ∨
      (∃ r : PSLGroupRing, x = pslSR * (pslTR - 1) ^ 2 * r)}

/-- The six elements `1, T, TS, S, ST, STS` of `ℂ[PSL(2, ℤ)]`. -/
def pslBasisElem : Fin 6 → PSLGroupRing :=
  ![1, pslTR, pslTR * pslSR, pslSR, pslSR * pslTR, pslSR * pslTR * pslSR]

end Work.Modular
