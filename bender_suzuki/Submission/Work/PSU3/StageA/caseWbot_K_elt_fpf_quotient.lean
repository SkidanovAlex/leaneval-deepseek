import Mathlib
import Submission.Work.PSU3.StageA.caseWbot_setup
import Submission.Work.PSU3.StageB.cocycle_prod_is_coboundary
import Submission.Work.ThmF.ChV12.prop3

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageA

/-!
# `Work.PSU3.StageA.caseWbot_K_elt_fpf_quotient`

The action of `K = J(D,t) = Ksub H t` on the quotient `Q / Q₀` is fixed-point-free.

With `Q` non-abelian (`hnab`), Ch. V §1 Corollary of Prop. 2 makes `Q` a Suzuki 2-group, so by
Higman `Z(Q) = Ω₁(Q) = Q0sub H ∩ Q` and `Q/Z(Q)` is elementary abelian (`x² ∈ Z(Q)` for every
`x ∈ Q`).

Let `k ∈ Ksub H t = Kset H t` be non-trivial (`FeitThompsonProp` gives `Ksub = Kset`), and let
`x ∈ Q` satisfy `k⁻¹ x k x⁻¹ ∈ Q0sub H = Z(Q)`; set `d = k⁻¹ x k x⁻¹` and `y = k⁻¹ x k = d · x`.
Since `d ∈ Z(Q)` is central in `Q`, `y · y = d² x² = x²` while `y · y = k⁻¹ x² k`; hence
`k⁻¹ x² k = x²`.  Now `x² ∈ Z(Q) = Q0sub H` (squares are central) and `x²` is fixed by
conjugation by `k`.  But `Kset H t` acts *regularly* on `Q0sub H♯ = Inv H` (Ch. I §2,
`Kset_regular`), so a non-trivial `k` has no non-trivial fixed point there: `x² = 1`.  Finally
`Q0sub H ∩ Q = Ω₁(Q)`, so `x ∈ Q0sub H`.
-/

theorem caseWbot_K_elt_fpf_quotient {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hFT : Submission.Blueprint.FeitThompsonProp)
    (hnab : ¬ Submission.Blueprint.IsAbelianSubgroup Q)
    {k : G} (hk : k ∈ Work.ThmF.Ksub H t) (hk1 : k ≠ 1) :
    ∀ x ∈ Q, k⁻¹ * x * k * x⁻¹ ∈ Work.ThmF.Q0sub H → x ∈ Work.ThmF.Q0sub H := by
  -- `Ksub H t = Kset H t` (Ch. V §1 Prop. 2, via `FeitThompsonProp`)
  obtain ⟨-, hKset, -⟩ := caseWbot_K_facts hS hFT hC4
  have hkKset : k ∈ Work.ThmF.Kset H t := hKset ▸ hk
  -- `Q` is a Suzuki 2-group; Higman's consequences and `Z(Q) = Q0sub H ∩ Q`
  have hSuz : Submission.Blueprint.IsSuzukiTwoGroup ↥Q := caseWbot_isSuzukiTwoGroup hS hFT hC4 hnab
  have hcenter : Subgroup.center ↥Q = (Work.ThmF.Q0sub H).subgroupOf Q :=
    caseWbot_center_subgroupOf hS hFT hC4 hnab
  have hHig := Work.Higman.higmanProp ↥Q hSuz
  have hcommH := Work.ThmF.ChV12.involutions_of_H_commute hS.situation hC4 H Q t hS.split
  obtain ⟨hQ0sq, -, -, hQ0inv⟩ := Work.ThmF.ChV12.Q0sub_elementary H hcommH
  -- a non-trivial `k ∈ K` fixes no non-trivial point of `Q0sub H` under conjugation
  have hfpf : ∀ z ∈ Work.ThmF.Q0sub H, k⁻¹ * z * k = z → z = 1 := by
    intro z hz hzk
    by_contra hz1
    have hzinv : z ∈ Submission.Blueprint.involutions (H : Set G) := hQ0inv z hz hz1
    obtain ⟨m, -, huniq⟩ := Work.ThmF.L5.Kset_regular hS.split z hzinv z hzinv
    have hzk' : k * z * k⁻¹ = z := by
      calc k * z * k⁻¹ = k * (k⁻¹ * z * k) * k⁻¹ := by rw [hzk]
        _ = z := by group
    have h1 : k = m := huniq k ⟨hkKset, hzk'⟩
    have h2 : (1 : G) = m := huniq 1 ⟨Work.ThmF.one_mem_Kset H t, by group⟩
    exact hk1 (by rw [h1, ← h2])
  intro x hxQ hc
  -- `d = k⁻¹ x k x⁻¹ ∈ Q0sub H` and `k⁻¹ x k = d · x`
  set d : G := k⁻¹ * x * k * x⁻¹ with hd
  have hdQ0 : d ∈ Work.ThmF.Q0sub H := hc
  have hdQ : d ∈ Q := Q0sub_le_Q hS.split hdQ0
  -- `d` is central in `Q`
  have hdx : d * x = x * d := by
    have hmem : (⟨d, hdQ⟩ : ↥Q) ∈ Subgroup.center ↥Q := by
      rw [hcenter]; exact Subgroup.mem_subgroupOf.mpr hdQ0
    have hcomm := Subgroup.mem_center_iff.mp hmem ⟨x, hxQ⟩
    exact (congrArg Subtype.val hcomm).symm
  have hd2 : d * d = 1 := hQ0sq d hdQ0
  have hyeq : k⁻¹ * x * k = d * x := by rw [hd]; group
  have hy2 : (d * x) * (d * x) = x * x := by
    calc (d * x) * (d * x) = d * (x * d) * x := by group
      _ = d * (d * x) * x := by rw [hdx]
      _ = (d * d) * (x * x) := by group
      _ = x * x := by rw [hd2, one_mul]
  -- hence `x²` is fixed by conjugation by `k`
  have hker : k⁻¹ * (x * x) * k = x * x := by
    calc k⁻¹ * (x * x) * k = (k⁻¹ * x * k) * (k⁻¹ * x * k) := by group
      _ = (d * x) * (d * x) := by rw [hyeq]
      _ = x * x := hy2
  -- `x² ∈ Q0sub H` (squares of a Suzuki 2-group are central, `Z(Q) = Q0sub H ∩ Q`)
  have hx2Q0 : x * x ∈ Work.ThmF.Q0sub H := by
    have hmem : (⟨x * x, Q.mul_mem hxQ hxQ⟩ : ↥Q) ∈ Subgroup.center ↥Q := by
      have h := hHig.2.1 (⟨x, hxQ⟩ : ↥Q)
      have heq : (⟨x, hxQ⟩ : ↥Q) ^ 2 = ⟨x * x, Q.mul_mem hxQ hxQ⟩ :=
        Subtype.ext (by rw [pow_two]; rfl)
      rwa [heq] at h
    rw [hcenter] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem
  have hx2 : x * x = 1 := hfpf (x * x) hx2Q0 hker
  -- `x² = 1` means `x ∈ Ω₁(Q) = Q0sub H ∩ Q`
  exact (caseC_Q0sub_subgroupOf_iff_sq hS hC4 ⟨x, hxQ⟩).mpr (Subtype.ext hx2)

end Work.PSU3.StageA
