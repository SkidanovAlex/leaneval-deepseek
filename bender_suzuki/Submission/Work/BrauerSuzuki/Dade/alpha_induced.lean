import Mathlib
import Submission.Work.BrauerSuzuki.Dade.alpha_facts
import Submission.Work.BrauerSuzuki.Dade.involution_structure
import Submission.Work.BrauerSuzuki.TI.cfInner_indFun_eq_of_TISet
import Submission.Work.Induction.frobenius_reciprocity
import Submission.Work.Induction.isVChar_indFun
import Submission.Work.Induction.indFun_TI_apply

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

namespace Work.BrauerSuzuki.Dade

open Classical
open scoped Pointwise

variable {G : Type*} [Group G] [Fintype G]

/-!
# The induced virtual character `α^G`

`α^G = indFun H α` is a virtual character of `G` with `(α^G, α^G)_G = 3` and principal
coefficient `1`; it vanishes off `(√σ)^G`, in particular at `1` and at `ι`.
-/

/-- `α^G = indFun H α`. -/
noncomputable def alphaInd (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S)
    (hn : 3 ≤ d.n) : G → ℂ := Work.Induction.indFun (Hsub S d) (alpha S d hn)

/-- `α^G` is a virtual character of `G`. -/
theorem alphaInd_isVChar (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S)
    (hn : 3 ≤ d.n) : Work.CharCore.IsVChar (alphaInd S d hn) :=
  Work.Induction.isVChar_indFun (alpha_isVChar S d hn)

/-- `(α^G, α^G)_G = (α, α)_H = 3`, by the TI-set isometry (Dade 5.19). -/
theorem alphaInd_cfInner_self (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S)
    (hn : 3 ≤ d.n) : Work.CharCore.cfInner (alphaInd S d hn) (alphaInd S d hn) = 3 := by
  have h := Work.BrauerSuzuki.TI.cfInner_indFun_eq_of_TISet
    (S := Work.BrauerSuzuki.sqrtSet (sigma S d))
    (H := Subgroup.normalizer (Subgroup.zpowers (sigma S d)))
    (sqrtSet_isTISet (sigma_ne_one S d hn)) (alpha_isClassFun S d hn) (alpha_isClassFun S d hn)
    (alpha_support S d hn) (alpha_support S d hn)
  have hgoal : Work.CharCore.cfInner (alphaInd S d hn) (alphaInd S d hn)
      = Work.CharCore.cfInner (alpha S d hn) (alpha S d hn) := h
  show Work.CharCore.cfInner (alphaInd S d hn) (alphaInd S d hn) = 3
  rw [hgoal, alpha_cfInner_self S d hn]

/-- `(α, 1)_H = 1`: the principal character of `H` is `1 ∘ φ`. -/
theorem alpha_cfInner_principal (S : Sylow 2 G)
    (d : Work.BrauerSuzuki.GenQuaternionData ↥S) (hn : 3 ≤ d.n) :
    Work.CharCore.cfInner (alpha S d hn) (fun _ => (1 : ℂ)) = 1 := by
  rw [alpha_eq]
  have hiso := (Work.BrauerSuzuki.Characters.resFunHom_pullback (phi S d hn)
    (phi_spec S d hn).2.2.1).2.2
  have hone : (fun _ => (1 : ℂ) : ↥(Hsub S d) → ℂ)
      = Work.Induction.resFunHom (phi S d hn) (fun _ => (1 : ℂ)) := by
    funext x
    rfl
  rw [hone]
  simp only [hiso]
  have ha : (fun _ => (1 : ℂ)) ∈ Work.CharCore.Irr ↥S :=
    Work.CharCore.principalChar_mem_Irr (G := ↥S)
  have hb : lam S d ∈ Work.CharCore.Irr ↥S := lam_mem_Irr S d
  have hc : th S d ∈ Work.CharCore.Irr ↥S := th_mem_Irr S d
  have hab : (fun _ => (1 : ℂ)) ≠ lam S d := fun h => lam_ne_one S d h.symm
  have hac : (fun _ => (1 : ℂ)) ≠ th S d := fun h => th_ne_one S d h.symm
  simp only [Work.CharCore.cfInner_sub_left, Work.CharCore.cfInner_add_left]
  rw [Work.CharCore.irr_orthonormal (fun _ => (1 : ℂ)) (fun _ => (1 : ℂ)) ha ha,
    Work.CharCore.irr_orthonormal (lam S d) (fun _ => (1 : ℂ)) hb ha,
    Work.CharCore.irr_orthonormal (th S d) (fun _ => (1 : ℂ)) hc ha]
  simp [hab, hac, Ne.symm hab, Ne.symm hac] <;> norm_num

/-- The principal coefficient of `α^G` is `1` (Frobenius reciprocity). -/
theorem alphaInd_cfInner_principal (S : Sylow 2 G)
    (d : Work.BrauerSuzuki.GenQuaternionData ↥S) (hn : 3 ≤ d.n) :
    Work.CharCore.cfInner (alphaInd S d hn) (fun _ => (1 : ℂ)) = 1 := by
  rw [alphaInd, Work.Induction.frobenius_reciprocity (Hsub S d) (alpha S d hn) (fun _ => (1 : ℂ))
    (by intro g h; rfl)]
  exact alpha_cfInner_principal S d hn

/-- `indFun H α` vanishes at any `g` no conjugate of which lies in `√σ`. -/
theorem indFun_alpha_eq_zero_of_not_conj (S : Sylow 2 G)
    (d : Work.BrauerSuzuki.GenQuaternionData ↥S) (hn : 3 ≤ d.n) {g : G}
    (hg : ∀ x : G, x * g * x⁻¹ ∉ Work.BrauerSuzuki.sqrtSet (sigma S d)) :
    Work.Induction.indFun (Hsub S d) (alpha S d hn) g = 0 := by
  rw [Work.Induction.indFun_apply_def]
  have hzero : ∀ x : G, (if hx : x * g * x⁻¹ ∈ Hsub S d then
      alpha S d hn ⟨x * g * x⁻¹, hx⟩ else 0) = 0 := by
    intro x
    by_cases hx : x * g * x⁻¹ ∈ Hsub S d
    · rw [dite_eq_left hx]
      exact alpha_support S d hn ⟨x * g * x⁻¹, hx⟩ (hg x)
    · rw [dite_eq_right hx]
  rw [Finset.sum_congr rfl (fun x _ => hzero x)]
  simp

/-- `α^G (1) = 0`. -/
theorem alphaInd_one (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S)
    (hn : 3 ≤ d.n) : alphaInd S d hn 1 = 0 := by
  rw [alphaInd]
  refine indFun_alpha_eq_zero_of_not_conj S d hn (fun x => ?_)
  simpa using one_notMem_sqrtSet S d hn

/-- `α^G (ι) = 0`, since `√σ` contains no involution. -/
theorem alphaInd_iota (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S)
    (hn : 3 ≤ d.n) : alphaInd S d hn (iota S d) = 0 := by
  rw [alphaInd]
  refine indFun_alpha_eq_zero_of_not_conj S d hn (fun x => ?_)
  have hord : orderOf (x * iota S d * x⁻¹) = 2 := by
    rw [Work.BrauerSuzuki.Group.orderOf_conj_eq, orderOf_iota]
  exact fun hmem => (involution_structure S d hn).2.2.2.1 _ hmem hord

end Work.BrauerSuzuki.Dade
