import Mathlib
import Submission.Work.Asymptotics.Graze.Vanishing

open scoped MatrixGroups

namespace Work.CKFinal.ArcCont

/-- **The pair condition `φ₊ + φ₋ = 0` on the eight arc-branch elements.**

The eight elements appearing in `Work.CKFinal.ArcCont.arc_branch_classify` are exactly the four
"grazing" elements of `Work.Asymptotics.Graze.GrazeElem` (`T S T`, `(T S)⁻¹`, `S T`,
`(T S T)⁻¹`) together with their negatives: indeed `S T⁻¹ = -(T S)⁻¹` since `S⁻¹ = -S`.  On each
of those `φ` vanishes (CKMRV Theorem 4.9(3)), and `φ₊ + φ₋ = 2 φ`, so `φ₊ + φ₋ = 0`. -/
theorem phiPair_arc_branches (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hγ : γ = ModularGroup.T * ModularGroup.S * ModularGroup.T ∨
      γ = -(ModularGroup.T * ModularGroup.S * ModularGroup.T) ∨
      γ = ModularGroup.S * ModularGroup.T⁻¹ ∨
      γ = -(ModularGroup.S * ModularGroup.T⁻¹) ∨
      γ = (ModularGroup.T * ModularGroup.S * ModularGroup.T)⁻¹ ∨
      γ = -((ModularGroup.T * ModularGroup.S * ModularGroup.T)⁻¹) ∨
      γ = ModularGroup.S * ModularGroup.T ∨
      γ = -(ModularGroup.S * ModularGroup.T)) :
    Work.Residues.phiPlus (MonoidAlgebra.single γ (1 : ℂ))
      + Work.Residues.phiMinus (MonoidAlgebra.single γ (1 : ℂ)) = 0 := by
  rcases hγ with h | h | h | h | h | h | h | h
  · subst h; exact Work.Asymptotics.Graze.phiPair_graze _ (Or.inl rfl)
  · subst h; exact Work.Asymptotics.Graze.phiPair_graze_neg _ (Or.inl rfl)
  · -- `γ = S T⁻¹ = -(T S)⁻¹`
    subst h
    have hS : (ModularGroup.S * ModularGroup.T⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
        = -((ModularGroup.T * ModularGroup.S)⁻¹) := by decide
    rw [hS]
    exact Work.Asymptotics.Graze.phiPair_graze_neg _ (Or.inr (Or.inl rfl))
  · -- `γ = -(S T⁻¹) = (T S)⁻¹`
    subst h
    have hS : (-(ModularGroup.S * ModularGroup.T⁻¹) : Matrix.SpecialLinearGroup (Fin 2) ℤ)
        = ((ModularGroup.T * ModularGroup.S)⁻¹) := by decide
    rw [hS]
    exact Work.Asymptotics.Graze.phiPair_graze _ (Or.inr (Or.inl rfl))
  · subst h; exact Work.Asymptotics.Graze.phiPair_graze _ (Or.inr (Or.inr (Or.inr rfl)))
  · subst h; exact Work.Asymptotics.Graze.phiPair_graze_neg _ (Or.inr (Or.inr (Or.inr rfl)))
  · subst h; exact Work.Asymptotics.Graze.phiPair_graze _ (Or.inr (Or.inr (Or.inl rfl)))
  · subst h; exact Work.Asymptotics.Graze.phiPair_graze_neg _ (Or.inr (Or.inr (Or.inl rfl)))

end Work.CKFinal.ArcCont
