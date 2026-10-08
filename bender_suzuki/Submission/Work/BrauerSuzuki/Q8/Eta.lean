import Mathlib
import Submission.Work.BrauerSuzuki.Q8.Zeta
import Submission.Work.CharCore.irr_orthonormal
import Submission.Work.CharCore.CFun
import Submission.Work.Induction.frobenius_reciprocity
import Submission.Work.BrauerSuzuki.TI.cfInner_indFun_eq_of_TISet
import Submission.Work.BrauerSuzuki.TI.resFun_indFun_eq_of_TISet
import Submission.Work.BrauerSuzuki.Characters.vchar_of_norm_three

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Glauberman's generalized character `η = Ind_{N*}^{G} ζ` (steps (2) and (3))

With `ζ = Ind_{C*}^{N*}(1 - λ)` (`Work.BrauerSuzuki.Q8.Ctx.zeta`), this file studies

`η := Ind_{N*}^{G} ζ`,

a generalized character of `G`, and proves the facts used by Glauberman (1974) in steps (2)
and (3):

* `(ζ,ζ)_{N*} = 4` and `(ζ,1_{N*}) = 1`;
* `ζ` is supported on `A*`, where it takes the value `4`;
* `(η,η)_G = 4` and `(η,1_G) = 1` (TI-set isometry / Frobenius reciprocity);
* `η(y) = 4` for `y` conjugate to an element of `A*` and `η(y) = 0` otherwise.
-/

set_option autoImplicit false

open Classical
open scoped Pointwise

namespace Work.BrauerSuzuki.Q8

variable {G : Type*} [Group G] [Finite G]

namespace Ctx

variable {x : G} {S : Sylow 2 G}
variable [Fintype G]

/-- `1̃ := Ind_{C*}^{N*} 1`. -/
noncomputable def oneTilde (h : Ctx G x S) : ↥(Nstar x) → ℂ :=
  Work.Induction.indFun ((Cstar x).subgroupOf (Nstar x)) (fun _ => (1 : ℂ))

/-- `λ̃ := Ind_{C*}^{N*} λ`. -/
noncomputable def lamTilde (h : Ctx G x S) : ↥(Nstar x) → ℂ :=
  Work.Induction.indFun ((Cstar x).subgroupOf (Nstar x)) h.lamKc

theorem oneTilde_apply_mem (h : Ctx G x S) {y : ↥(Nstar x)}
    (hy : y ∈ (Cstar x).subgroupOf (Nstar x)) : h.oneTilde y = 2 := by
  rw [oneTilde]
  rw [indFun_eq_of_index_two h.Cstar_normal_Nstar h.subgroupOf_index_two
    (Work.CharCore.isClassFun_const (1 : ℂ)) (fun l k => rfl) hy]
  norm_num

theorem oneTilde_apply_notMem (h : Ctx G x S) {y : ↥(Nstar x)}
    (hy : y ∉ (Cstar x).subgroupOf (Nstar x)) : h.oneTilde y = 0 := by
  rw [oneTilde]
  exact indFun_eq_zero_of_index_two h.Cstar_normal_Nstar hy

theorem lamKc_conj (h : Ctx G x S) (l : ↥(Nstar x))
    (k : ↥((Cstar x).subgroupOf (Nstar x))) :
    h.lamKc ⟨l * k * l⁻¹, (h.Cstar_normal_Nstar).conj_mem k k.2 l⟩ = h.lamKc k := by
  rw [lamKc, lamKc]
  refine h.lamFun_conj_Nstar l.2 ⟨((k : ↥(Nstar x)) : G), Subgroup.mem_subgroupOf.mp k.2⟩

theorem lamTilde_apply_mem (h : Ctx G x S) {y : ↥(Nstar x)}
    (hy : y ∈ (Cstar x).subgroupOf (Nstar x)) : h.lamTilde y = 2 * h.lamKc ⟨y, hy⟩ := by
  rw [lamTilde]
  rw [indFun_eq_of_index_two h.Cstar_normal_Nstar h.subgroupOf_index_two h.isClassFun_lamKc
    (fun l k => h.lamKc_conj l k) hy]

theorem lamTilde_apply_notMem (h : Ctx G x S) {y : ↥(Nstar x)}
    (hy : y ∉ (Cstar x).subgroupOf (Nstar x)) : h.lamTilde y = 0 := by
  rw [lamTilde]
  exact indFun_eq_zero_of_index_two h.Cstar_normal_Nstar hy

theorem zeta_eq_sub (h : Ctx G x S) : h.zeta = h.oneTilde - h.lamTilde := by
  funext y
  by_cases hy : y ∈ (Cstar x).subgroupOf (Nstar x)
  · rw [h.zeta_apply_of_mem hy]
    change 2 * h.phiKc ⟨y, hy⟩ = h.oneTilde y - h.lamTilde y
    rw [h.oneTilde_apply_mem hy, h.lamTilde_apply_mem hy]
    rw [phiKc]
    ring
  · rw [h.zeta_apply_of_notMem hy]
    change 0 = h.oneTilde y - h.lamTilde y
    rw [h.oneTilde_apply_notMem hy, h.lamTilde_apply_notMem hy]
    ring

theorem zeta_apply_mem_Cstar_eq (h : Ctx G x S) {y : ↥(Nstar x)} (hy : (y : G) ∈ Cstar x) :
    h.zeta y = 2 * (1 - lamFun x ⟨(y : G), hy⟩) := h.zeta_apply_of_mem_Cstar hy

theorem zeta_apply_Astar (h : Ctx G x S) {y : ↥(Nstar x)} (hy : (y : G) ∈ Astar x) :
    h.zeta y = 4 := by
  have hyC : (y : G) ∈ Cstar x := hy.1
  rw [h.zeta_apply_mem_Cstar_eq hyC]
  have hnot : (y : G) ∉ (T x : Set G) * (Hstar x : Set G) := hy.2
  rw [(h.lamFun_eq_neg_one_iff ⟨(y : G), hyC⟩).mpr hnot]
  norm_num

theorem zeta_apply_eq_zero_of_notMem_Astar (h : Ctx G x S) {y : ↥(Nstar x)}
    (hy : (y : G) ∉ Astar x) : h.zeta y = 0 := by
  by_cases hyC : (y : G) ∈ Cstar x
  · rw [h.zeta_apply_mem_Cstar_eq hyC]
    have hin : (y : G) ∈ (T x : Set G) * (Hstar x : Set G) := by
      by_contra hcon
      exact hy ⟨hyC, hcon⟩
    rw [(h.lamFun_eq_one_iff ⟨(y : G), hyC⟩).mpr hin]
    norm_num
  · exact h.zeta_apply_of_notMem_Cstar hyC

theorem supportLeSub_zeta (h : Ctx G x S) :
    Work.BrauerSuzuki.SupportLeSub h.zeta (Astar x) :=
  fun y hy => h.zeta_apply_eq_zero_of_notMem_Astar hy

theorem resFun_oneTilde (h : Ctx G x S) :
    Work.Induction.resFun ((Cstar x).subgroupOf (Nstar x))
        (Work.Induction.indFun ((Cstar x).subgroupOf (Nstar x)) (fun _ => (1 : ℂ))) =
      fun _ => (2 : ℂ) := by
  funext y
  exact h.oneTilde_apply_mem y.2

theorem resFun_lamTilde (h : Ctx G x S) :
    Work.Induction.resFun ((Cstar x).subgroupOf (Nstar x))
        (Work.Induction.indFun ((Cstar x).subgroupOf (Nstar x)) h.lamKc) =
      fun y => 2 * h.lamKc y := by
  funext y
  exact h.lamTilde_apply_mem y.2

/-- An element of `A*` (nonempty because `|A*| = 2 |H*| ≥ 2`). -/
theorem exists_mem_Astar (h : Ctx G x S) : ∃ a : G, a ∈ Astar x := by
  have hApos : 0 < Nat.card ↥(Astar x) := by
    rw [h.card_Astar]
    have : 0 < Nat.card ↥(Hstar x) :=
      Nat.card_pos_iff.mpr ⟨⟨1, (Hstar x).one_mem⟩, inferInstance⟩
    positivity
  obtain ⟨⟨a, ha⟩, _⟩ := Nat.card_pos_iff.mp hApos
  exact ⟨a, ha⟩

theorem lamKc_ne_one (h : Ctx G x S) :
    h.lamKc ≠ (fun _ : ↥((Cstar x).subgroupOf (Nstar x)) => (1 : ℂ)) := by
  obtain ⟨a, ha⟩ := h.exists_mem_Astar
  let kA : ↥((Cstar x).subgroupOf (Nstar x)) :=
    ⟨⟨a, h.Cstar_le_Nstar ha.1⟩, Subgroup.mem_subgroupOf.mpr ha.1⟩
  have hkA : h.lamKc kA = -1 := by
    rw [lamKc]
    exact (h.lamFun_eq_neg_one_iff ⟨a, ha.1⟩).mpr ha.2
  intro hc
  have h1 := congrFun hc kA
  rw [hkA] at h1
  norm_num at h1

theorem cfInner_principal_self (h : Ctx G x S) :
    Work.CharCore.cfInner (fun _ : ↥((Cstar x).subgroupOf (Nstar x)) => (1 : ℂ))
      (fun _ => (1 : ℂ)) = 1 := by
  rw [Work.CharCore.irr_orthonormal (fun _ => (1 : ℂ)) (fun _ => (1 : ℂ))
    Work.CharCore.principalChar_mem_Irr Work.CharCore.principalChar_mem_Irr]
  simp

theorem cfInner_principal_const (h : Ctx G x S) (c : ℂ) :
    Work.CharCore.cfInner (fun _ : ↥((Cstar x).subgroupOf (Nstar x)) => (1 : ℂ))
      (fun _ => c) = starRingEnd ℂ c := by
  rw [Work.CharCore.cfInner_apply]
  have h1 : ∀ y : ↥((Cstar x).subgroupOf (Nstar x)),
      (fun _ => (1 : ℂ)) y * starRingEnd ℂ ((fun _ => c) y) = starRingEnd ℂ c := by
    intro y
    simp
  rw [Finset.sum_congr rfl (fun y _ => h1 y)]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  haveI : Nonempty ↥((Cstar x).subgroupOf (Nstar x)) := ⟨⟨1, (Cstar x).one_mem⟩⟩
  have hc : (Fintype.card ↥((Cstar x).subgroupOf (Nstar x)) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

theorem cfInner_zeta_self (h : Ctx G x S) :
    Work.CharCore.cfInner h.zeta h.zeta = 4 := by
  rw [h.zeta_eq_sub, Work.CharCore.cfInner_sub_left, Work.CharCore.cfInner_sub_right,
    Work.CharCore.cfInner_sub_right]
  have h11 : Work.CharCore.cfInner h.oneTilde h.oneTilde = 2 := by
    rw [oneTilde]
    rw [Work.Induction.frobenius_reciprocity ((Cstar x).subgroupOf (Nstar x)) (fun _ => (1 : ℂ))
      (Work.Induction.indFun ((Cstar x).subgroupOf (Nstar x)) (fun _ => (1 : ℂ)))
      (Work.Induction.isClassFun_indFun _ _)]
    have hres : Work.Induction.resFun ((Cstar x).subgroupOf (Nstar x))
        (Work.Induction.indFun ((Cstar x).subgroupOf (Nstar x)) (fun _ => (1 : ℂ)))
        = fun _ => (2 : ℂ) := by
      funext y
      rw [Work.Induction.resFun_apply]
      exact h.oneTilde_apply_mem y.2
    rw [hres, h.cfInner_principal_const]
    exact Complex.conj_ofNat 2
  have h22 : Work.CharCore.cfInner h.lamTilde h.lamTilde = 2 := by
    rw [lamTilde]
    rw [Work.Induction.frobenius_reciprocity ((Cstar x).subgroupOf (Nstar x)) h.lamKc
      (Work.Induction.indFun ((Cstar x).subgroupOf (Nstar x)) h.lamKc)
      (Work.Induction.isClassFun_indFun _ _)]
    have hres : Work.Induction.resFun ((Cstar x).subgroupOf (Nstar x))
        (Work.Induction.indFun ((Cstar x).subgroupOf (Nstar x)) h.lamKc)
        = (2 : ℂ) • h.lamKc := by
      funext y
      rw [Work.Induction.resFun_apply, ← lamTilde, Pi.smul_apply, smul_eq_mul,
        h.lamTilde_apply_mem y.2]
    rw [hres, Work.CharCore.cfInner_smul_right,
      Work.CharCore.irr_orthonormal h.lamKc h.lamKc h.lamKc_mem_Irr h.lamKc_mem_Irr,
      if_pos rfl]
    simp only [mul_one]
    exact Complex.conj_ofNat 2
  have h12 : Work.CharCore.cfInner h.oneTilde h.lamTilde = 0 := by
    rw [oneTilde, lamTilde]
    rw [Work.Induction.frobenius_reciprocity ((Cstar x).subgroupOf (Nstar x)) (fun _ => (1 : ℂ))
      (Work.Induction.indFun ((Cstar x).subgroupOf (Nstar x)) h.lamKc)
      (Work.Induction.isClassFun_indFun _ _)]
    have hres : Work.Induction.resFun ((Cstar x).subgroupOf (Nstar x))
        (Work.Induction.indFun ((Cstar x).subgroupOf (Nstar x)) h.lamKc)
        = (2 : ℂ) • h.lamKc := by
      funext y
      rw [Work.Induction.resFun_apply, ← lamTilde, Pi.smul_apply, smul_eq_mul,
        h.lamTilde_apply_mem y.2]
    rw [hres, Work.CharCore.cfInner_smul_right,
      Work.CharCore.irr_orthonormal (fun _ => (1 : ℂ)) h.lamKc
        Work.CharCore.principalChar_mem_Irr h.lamKc_mem_Irr,
      if_neg (fun hc => h.lamKc_ne_one hc.symm)]
    simp only [mul_zero]
  have h21 : Work.CharCore.cfInner h.lamTilde h.oneTilde = 0 := by
    rw [Work.CharCore.cfInner_conj_symm, h12]
    simp
  rw [h11, h12, h21, h22]
  norm_num

theorem cfInner_zeta_one (h : Ctx G x S) :
    Work.CharCore.cfInner h.zeta (fun _ => (1 : ℂ)) = 1 := by
  rw [h.zeta_eq_sub, Work.CharCore.cfInner_sub_left]
  have h1 : Work.CharCore.cfInner h.oneTilde (fun _ : ↥(Nstar x) => (1 : ℂ)) = 1 := by
    rw [oneTilde]
    rw [Work.Induction.frobenius_reciprocity ((Cstar x).subgroupOf (Nstar x)) (fun _ => (1 : ℂ))
      (fun _ : ↥(Nstar x) => (1 : ℂ)) (Work.CharCore.isClassFun_const _)]
    show Work.CharCore.cfInner (fun _ : ↥((Cstar x).subgroupOf (Nstar x)) => (1 : ℂ))
      (fun _ => (1 : ℂ)) = 1
    exact h.cfInner_principal_self
  have h2 : Work.CharCore.cfInner h.lamTilde (fun _ : ↥(Nstar x) => (1 : ℂ)) = 0 := by
    rw [lamTilde]
    rw [Work.Induction.frobenius_reciprocity ((Cstar x).subgroupOf (Nstar x)) h.lamKc
      (fun _ : ↥(Nstar x) => (1 : ℂ)) (Work.CharCore.isClassFun_const _)]
    show Work.CharCore.cfInner h.lamKc
      (fun _ : ↥((Cstar x).subgroupOf (Nstar x)) => (1 : ℂ)) = 0
    rw [Work.CharCore.irr_orthonormal h.lamKc (fun _ : ↥((Cstar x).subgroupOf (Nstar x)) => (1 : ℂ))
      h.lamKc_mem_Irr Work.CharCore.principalChar_mem_Irr,
      if_neg h.lamKc_ne_one]
  rw [h1, h2]
  norm_num

end Ctx

end Work.BrauerSuzuki.Q8
