import Mathlib
import Submission.Work.FeitSibley.GroupTheory.S_Q1

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.FeitSibley.CharQ

/-- Conjugation by an element `d ∈ D` is compatible with the direct product decomposition
`Q = S × Q₁`: it acts componentwise. -/
theorem prodIso_conjMem {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    (d : G) (hd : d ∈ h.D) (a : ↥h.S) (b : ↥h.Q1) :
    Work.Induction.conjMem h.Q ⟨d, h.Q_normal_in_H (h.D_le_H hd)⟩ (h.prodIso (a, b)) =
      h.prodIso (Work.Induction.conjMem h.S ⟨d, h.S_normal_in_H (h.D_le_H hd)⟩ a,
        Work.Induction.conjMem h.Q1 ⟨d, h.Q1_normal_in_H (h.D_le_H hd)⟩ b) := by
  apply Subtype.ext
  simp only [Work.Induction.conjMem_val, Work.FeitSibley.FSData.prodIso_apply,
    Work.FeitSibley.FSData.prodHom_apply, Subgroup.coe_inv]
  group

theorem prodChar_conjFun {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    (d : G) (hd : d ∈ h.D) (lam : ↥h.S → ℂ) (theta : ↥h.Q1 → ℂ) :
    Work.Induction.conjFun h.Q ⟨d, h.Q_normal_in_H (h.D_le_H hd)⟩ (h.prodChar lam theta) =
      h.prodChar (Work.Induction.conjFun h.S ⟨d, h.S_normal_in_H (h.D_le_H hd)⟩ lam)
        (Work.Induction.conjFun h.Q1 ⟨d, h.Q1_normal_in_H (h.D_le_H hd)⟩ theta) := by
  funext q
  obtain ⟨a, b, hab⟩ : ∃ a : ↥h.S, ∃ b : ↥h.Q1, h.prodIso (a, b) = q :=
    ⟨(h.prodIso.symm q).1, (h.prodIso.symm q).2, h.prodIso.apply_symm_apply q⟩
  rw [← hab]
  clear hab
  simp only [Work.Induction.conjFun_apply, Work.FeitSibley.FSData.prodChar,
    MulEquiv.symm_apply_apply]
  rw [prodIso_conjMem h d hd a b]
  simp only [MulEquiv.symm_apply_apply]

end Work.FeitSibley.CharQ
