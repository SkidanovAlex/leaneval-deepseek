import Mathlib
import Submission.Work.PSU3.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Fixed-point-free action of `D = H ∩ H^t` on `Q / Q₀`

`Work.PSU3.StageB.StepB.exists_fpf_action_quotient`: the second point stabiliser
`D = twoPoint H t` of a split rank-one datum acts by conjugation on the normal
`2`-subgroup `Q` (`Q ⊴ H`), and `D` normalises `Q₀ = ⟨Inv H⟩` (conjugation by an element
of `H` permutes the involutions of `H`).  Hence conjugation descends to an action on the
quotient `Q / (Q₀ ∩ Q)`.  Under the hypothesis `DFpfBar H Q t` — `D` acts fixed-point-freely
on `(Q/Q₀)#` — this induced action is fixed-point-free.
-/

open Submission.Blueprint
open Work.ThmF

namespace Work.PSU3.StageB.StepB

theorem exists_fpf_action_quotient {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hfpf : Work.PSU3.DFpfBar H Q t)
    [hK : ((Work.ThmF.Q0sub H).subgroupOf Q).Normal] :
    ∃ ρ : ↥(Submission.Blueprint.twoPoint H t) →*
        MulAut (↥Q ⧸ (Work.ThmF.Q0sub H).subgroupOf Q),
      ∀ a : ↥(Submission.Blueprint.twoPoint H t), a ≠ 1 →
        ∀ e : ↥Q ⧸ (Work.ThmF.Q0sub H).subgroupOf Q, ρ a e = e → e = 1 := by
  -- Conjugation by an element of `H` preserves `Q₀ = ⟨Inv H⟩`.
  have conj_mem_Q0sub : ∀ (a : G), a ∈ H → ∀ x ∈ Q0sub H, a * x * a⁻¹ ∈ Q0sub H := by
    intro a ha x hx
    rw [Q0sub] at hx ⊢
    refine Subgroup.closure_induction
      (p := fun y _ => a * y * a⁻¹ ∈ Subgroup.closure (Q0 H)) ?_ ?_ ?_ ?_ hx
    · intro y hy
      rcases mem_Q0_iff.mp hy with ⟨hyH, hy2⟩ | rfl
      · exact Subgroup.subset_closure (by
          rw [mem_Q0_iff]
          left
          refine ⟨H.mul_mem (H.mul_mem ha hyH) (H.inv_mem ha), ?_⟩
          have h1 : (MulAut.conj a) y = a * y * a⁻¹ := MulAut.conj_apply a y
          rw [← h1, MulEquiv.orderOf_eq]
          exact hy2)
      · simp
    · simp
    · intro y z hy hz ihy ihz
      have hh : a * (y * z) * a⁻¹ = (a * y * a⁻¹) * (a * z * a⁻¹) := by group
      rw [hh]
      exact Subgroup.mul_mem _ ihy ihz
    · intro y hy ihy
      have hh : a * y⁻¹ * a⁻¹ = (a * y * a⁻¹)⁻¹ := by group
      rw [hh]
      exact Subgroup.inv_mem _ ihy
  -- `D = twoPoint H t` normalises `Q`.
  have hD : twoPoint H t ≤ Subgroup.normalizer (Q : Set G) :=
    le_trans inf_le_left hsplit.normal
  let N : Subgroup Q := (Q0sub H).subgroupOf Q
  -- The conjugation action of `D` on `Q`.
  let φ : ↥(twoPoint H t) →* MulAut Q :=
    (Subgroup.normalizerMonoidHom (H := Q)).comp (Subgroup.inclusion hD)
  have phi_apply : ∀ (a : ↥(twoPoint H t)) (x : Q),
      ((φ a) x : G) = (a : G) * (x : G) * (a : G)⁻¹ := fun a x => rfl
  -- Each `φ a` preserves `N = Q₀ ∩ Q`.
  have hpres : ∀ a : ↥(twoPoint H t), Subgroup.map (↑(φ a)) N = N := by
    intro a
    apply le_antisymm
    · intro y hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      show ((φ a) x : G) ∈ Q0sub H
      rw [phi_apply a x]
      exact conj_mem_Q0sub (a : G) (Subgroup.mem_inf.mp a.2).1 (x : G) hx
    · intro y hy
      rw [Subgroup.mem_map]
      refine ⟨(φ a).symm y, ?_, ?_⟩
      · rw [Subgroup.mem_subgroupOf]
        have hsymm : (((φ a).symm y : Q) : G) = (a : G)⁻¹ * (y : G) * (a : G) := by
          have h1 : ((φ a).symm : Q ≃* Q) = φ a⁻¹ := by rw [map_inv]; rfl
          rw [h1]
          have h2 := phi_apply a⁻¹ y
          simpa using h2
        rw [hsymm]
        have h3 := conj_mem_Q0sub (a : G)⁻¹ (H.inv_mem (Subgroup.mem_inf.mp a.2).1) (y : G) hy
        simpa using h3
      · exact MulEquiv.apply_symm_apply (φ a) y
  -- The induced action on `Q/N` is fixed-point-free.
  have hfpf_rho : ∀ (a : ↥(twoPoint H t)), a ≠ 1 →
      ∀ e : Q ⧸ N, QuotientGroup.congr N N (φ a) (hpres a) e = e → e = 1 := by
    intro a ha e he
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective e
    rw [QuotientGroup.congr_mk] at he
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have hmem : ((φ a) x * x⁻¹ : Q) ∈ N := by
      apply (QuotientGroup.eq_one_iff _).mp
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, he, mul_inv_cancel]
    rw [Subgroup.mem_subgroupOf] at hmem
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hmem
    rw [phi_apply a x] at hmem
    by_contra hxnot
    have hne : ((a : G)⁻¹) ≠ 1 := by
      intro h
      exact ha (Subtype.ext (by simpa using inv_eq_one.mp h))
    have hnot := hfpf ((a : G)⁻¹) ((twoPoint H t).inv_mem a.2) hne (x : G) x.2 hxnot
    rw [inv_inv] at hnot
    exact hnot hmem
  refine ⟨{ toFun := fun a => QuotientGroup.congr N N (φ a) (hpres a),
            map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · apply MulEquiv.ext
    intro x
    refine QuotientGroup.induction_on x ?_
    intro q
    rw [QuotientGroup.congr_mk]
    simp
  · intro a b
    apply MulEquiv.ext
    intro x
    refine QuotientGroup.induction_on x ?_
    intro q
    rw [QuotientGroup.congr_mk, MulAut.mul_apply, QuotientGroup.congr_mk, QuotientGroup.congr_mk]
    rw [map_mul φ a b, MulAut.mul_apply]
  · intro a ha e he
    exact hfpf_rho a ha e he

end Work.PSU3.StageB.StepB
