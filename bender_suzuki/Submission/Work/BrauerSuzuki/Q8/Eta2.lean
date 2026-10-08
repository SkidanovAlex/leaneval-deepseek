import Mathlib
import Submission.Work.BrauerSuzuki.Q8.Eta
import Submission.Work.BrauerSuzuki.TI.cfInner_indFun_eq_of_TISet
import Submission.Work.BrauerSuzuki.TI.resFun_indFun_eq_of_TISet
import Submission.Work.Induction.frobenius_reciprocity
import Submission.Work.Induction.indFun_apply_of_isConj

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Glauberman's generalized character `η = Ind_{N*}^{G} ζ` (steps (2) and (3))

`η` is a generalized character of `G` with `(η,η) = 4`, `(η,1_G) = 1`, which takes the value
`4` exactly on the `G`-conjugates of the elements of `A*` (`=: B`) and vanishes elsewhere.
-/

set_option autoImplicit false

open Classical
open scoped Pointwise

namespace Work.BrauerSuzuki.Q8

variable {G : Type*} [Group G] [Finite G]

namespace Ctx

variable {x : G} {S : Sylow 2 G}
variable [Fintype G]

/-- Glauberman's generalized character `η = Ind_{N*}^{G} ζ`. -/
noncomputable def eta (h : Ctx G x S) : G → ℂ :=
  Work.Induction.indFun (Nstar x) h.zeta

theorem isVChar_eta (h : Ctx G x S) : Work.CharCore.IsVChar h.eta := by
  rw [eta]
  exact Work.Induction.isVChar_indFun h.isVChar_zeta

theorem isClassFun_eta (h : Ctx G x S) : Work.CharCore.IsClassFun h.eta := by
  rw [eta]
  exact Work.Induction.isClassFun_indFun _ _

theorem cfInner_eta_self (h : Ctx G x S) : Work.CharCore.cfInner h.eta h.eta = 4 := by
  rw [eta]
  rw [Work.BrauerSuzuki.TI.cfInner_indFun_eq_of_TISet h.isTI h.isClassFun_zeta h.isClassFun_zeta
    h.supportLeSub_zeta h.supportLeSub_zeta]
  exact h.cfInner_zeta_self

theorem cfInner_eta_one (h : Ctx G x S) :
    Work.CharCore.cfInner h.eta (fun _ => (1 : ℂ)) = 1 := by
  rw [eta]
  rw [Work.Induction.frobenius_reciprocity (Nstar x) h.zeta (fun _ : G => (1 : ℂ))
    (Work.CharCore.isClassFun_const _)]
  show Work.CharCore.cfInner h.zeta (fun _ : ↥(Nstar x) => (1 : ℂ)) = 1
  exact h.cfInner_zeta_one

theorem eta_apply_of_conj (h : Ctx G x S) {g : G} {a : ↥(Nstar x)}
    (ha : (a : G) ∈ Astar x) (hg : IsConj g (a : G)) : h.eta g = 4 := by
  rw [eta, Work.Induction.indFun_eq_of_isConj (Nstar x) h.zeta hg]
  rw [Work.BrauerSuzuki.TI.resFun_indFun_eq_of_TISet h.isTI h.isClassFun_zeta h.supportLeSub_zeta
    ha]
  exact h.zeta_apply_Astar ha

theorem eta_apply_eq_zero_of_no_conj (h : Ctx G x S) {g : G}
    (hg : ∀ u : G, ∀ b : ↥(Nstar x), (b : G) ∈ Astar x → u * g * u⁻¹ ≠ (b : G)) :
    h.eta g = 0 := by
  rw [eta, Work.Induction.indFun_apply_def]
  have hsum : (∑ u : G, (if hu : u * g * u⁻¹ ∈ Nstar x then
      h.zeta ⟨u * g * u⁻¹, hu⟩ else 0)) = 0 := by
    rw [Finset.sum_eq_zero]
    intro u _
    by_cases hu : u * g * u⁻¹ ∈ Nstar x
    · rw [dite_eq_left hu]
      by_cases hA : ((⟨u * g * u⁻¹, hu⟩ : ↥(Nstar x)) : G) ∈ Astar x
      · exact absurd rfl (hg u ⟨u * g * u⁻¹, hu⟩ hA)
      · exact h.zeta_apply_eq_zero_of_notMem_Astar hA
    · rw [dite_eq_right hu]
  rw [hsum, mul_zero]

theorem eta_apply_Bset (h : Ctx G x S) {g : G} (hg : g ∈ Bset x) : h.eta g = 4 := by
  obtain ⟨a, ha, hconj⟩ := hg
  exact h.eta_apply_of_conj (a := ⟨a, h.Cstar_le_Nstar ha.1⟩) ha hconj

theorem eta_apply_notMem_Bset (h : Ctx G x S) {g : G} (hg : g ∉ Bset x) : h.eta g = 0 := by
  refine h.eta_apply_eq_zero_of_no_conj fun u b hb hu => ?_
  exact hg ⟨b, hb, isConj_iff.mpr ⟨u, hu⟩⟩

end Ctx

end Work.BrauerSuzuki.Q8
