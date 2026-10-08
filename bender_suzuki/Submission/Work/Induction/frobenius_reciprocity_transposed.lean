import Mathlib
import Submission.Work.Induction.Defs
import Submission.Work.Induction.frobenius_reciprocity

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Induction

open Classical
open scoped Pointwise

-- Transposed Frobenius reciprocity `⟨φ, Ind_H^G ψ⟩_G = ⟨Res_H^G φ, ψ⟩_H` for `φ` a class
-- function on `G` and `ψ : H → ℂ` arbitrary.  This is the classical `⟨χ, θ^G⟩ = ⟨χ|_H, θ⟩`
-- form.  Proof: `Work.Induction.frobenius_reciprocity` (which needs no hypothesis on its
-- first argument) together with conjugate symmetry of `cfInner`
-- (`Work.CharCore.cfInner_conj_symm`); alternatively expand both sides as double sums.
theorem frobenius_reciprocity_transposed {G : Type*} [Group G] [Fintype G] (H : Subgroup G)
    (φ : G → ℂ) (ψ : H → ℂ) (hφ : Work.CharCore.IsClassFun φ) :
    Work.CharCore.cfInner φ (Work.Induction.indFun H ψ)
      = Work.CharCore.cfInner (Work.Induction.resFun H φ) ψ := by
  -- Conjugate symmetry turns the desired identity into the ordinary Frobenius reciprocity
  -- `⟨Ind_H^G ψ, φ⟩_G = ⟨ψ, Res_H^G φ⟩_H`, whose class-function hypothesis is on `φ`.
  have hfr := frobenius_reciprocity H ψ φ hφ
  calc Work.CharCore.cfInner φ (Work.Induction.indFun H ψ)
      = starRingEnd ℂ (Work.CharCore.cfInner (Work.Induction.indFun H ψ) φ) :=
        CharCore.cfInner_conj_symm φ _
    _ = starRingEnd ℂ (Work.CharCore.cfInner ψ (Work.Induction.resFun H φ)) := by rw [hfr]
    _ = Work.CharCore.cfInner (Work.Induction.resFun H φ) ψ := by
        rw [CharCore.cfInner_conj_symm (Work.Induction.resFun H φ) ψ]

end Work.Induction
