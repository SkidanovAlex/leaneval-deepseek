import Mathlib
import Submission.Work.BrauerSuzuki.Defs
import Submission.Work.Induction.Defs
import Submission.Work.CharCore.Defs
import Submission.Work.CharCore.CFun
import Submission.Work.Induction.frobenius_reciprocity
import Submission.Work.Induction.isClassFun_indFun
import Submission.Work.BrauerSuzuki.TI.resFun_indFun_eq_of_TISet

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BrauerSuzuki.TI

open Classical

/-- If `φ` vanishes wherever `f` and `g` differ, then `φ` has the same inner product with
`f` and with `g`.  Indeed `cfInner φ f = |G|⁻¹ ∑_x φ x * conj (f x)` and each summand with
`φ x ≠ 0` is unchanged, the others being `0`. -/
theorem cfInner_congr_of_eq_of_ne_zero {G : Type*} [Group G] [Fintype G] {φ f g : G → ℂ}
    (h : ∀ x, φ x ≠ 0 → f x = g x) :
    Work.CharCore.cfInner φ f = Work.CharCore.cfInner φ g := by
  rw [Work.CharCore.cfInner_apply, Work.CharCore.cfInner_apply]
  refine congrArg (fun z => (Fintype.card G : ℂ)⁻¹ * z) ?_
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases hx : φ x = 0
  · rw [hx, zero_mul, zero_mul]
  · rw [h x hx]

/-- **Brauer–Suzuki isometry (Dade, set form).**  For a TI set `S` with normalizer `H` and
class functions `φ, ψ` on `H` with support contained in `S`, the induction map
`f ↦ Ind_H^G f` preserves the inner product: `⟨Ind φ, Ind ψ⟩_G = ⟨φ, ψ⟩_H`.

By Frobenius reciprocity `⟨Ind φ, Ind ψ⟩_G = ⟨φ, Res_H^G (Ind ψ)⟩_H`, so it suffices to know
that `Res_H^G (Ind ψ)` agrees with `ψ` where `φ` is non-zero, that is on `S`.  There
`Res_H^G (Ind ψ) = ψ` is exactly `resFun_indFun_eq_of_TISet`: an element `x ∉ H` conjugates
no element of `S` back into `S` (TI), so it contributes `0` to the defining sum of
`Ind_H^G ψ`. -/
theorem cfInner_indFun_eq_of_TISet {G : Type*} [Group G] [Fintype G] {S : Set G} {H : Subgroup G}
    (hTI : Work.BrauerSuzuki.IsTISet S H) {φ ψ : H → ℂ}
    (hφ : Work.CharCore.IsClassFun φ) (hψ : Work.CharCore.IsClassFun ψ)
    (hφs : Work.BrauerSuzuki.SupportLeSub φ S) (hψs : Work.BrauerSuzuki.SupportLeSub ψ S) :
    Work.CharCore.cfInner (Work.Induction.indFun H φ) (Work.Induction.indFun H ψ)
      = Work.CharCore.cfInner φ ψ := by
  classical
  -- Frobenius reciprocity reduces the claim to `⟨φ, Res_H^G (Ind ψ)⟩_H = ⟨φ, ψ⟩_H`.
  rw [Work.Induction.frobenius_reciprocity H φ (Work.Induction.indFun H ψ)
    (Work.Induction.isClassFun_indFun H ψ)]
  -- `Res_H^G (Ind ψ)` and `ψ` agree wherever `φ` does not vanish, i.e. on `S`.
  refine cfInner_congr_of_eq_of_ne_zero (fun h hh => ?_)
  have hS : (h : G) ∈ S := by
    by_contra hnot
    exact hh (hφs h hnot)
  simpa only [Work.Induction.resFun_apply] using
    resFun_indFun_eq_of_TISet hTI hψ hψs hS

end Work.BrauerSuzuki.TI
