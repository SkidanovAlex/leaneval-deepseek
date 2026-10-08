import Mathlib
import Submission.Work.PSU3.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageB.StepB

theorem W_normal_twoPoint {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp) :
    ((Work.ThmF.W H t).subgroupOf (Submission.Blueprint.twoPoint H t)).Normal := by
  classical
  have hP4 := (hC4 G hS.situation H hS.split.stronglyEmbedded t hS.split.invol
    hS.split.not_mem).2.2.2.2.1
  have hW_eq : Work.ThmF.W H t =
      Submission.Blueprint.twoPoint H t ⊓
        Subgroup.centralizer (Submission.Blueprint.involutions (H : Set G)) := by
    simpa only [Work.ThmF.W, Work.ThmF.Kset] using hP4
  have hW_le_D : Work.ThmF.W H t ≤ Submission.Blueprint.twoPoint H t := by
    rw [hW_eq]; exact inf_le_left
  rw [Subgroup.normal_subgroupOf_iff hW_le_D]
  intro w d hw hd
  rw [hW_eq] at hw ⊢
  obtain ⟨hwD, hwC⟩ := Subgroup.mem_inf.mp hw
  have hdH : d ∈ H := (Subgroup.mem_inf.mp hd).1
  refine Subgroup.mem_inf.mpr ⟨(Submission.Blueprint.twoPoint H t).mul_mem
    ((Submission.Blueprint.twoPoint H t).mul_mem hd hwD)
    ((Submission.Blueprint.twoPoint H t).inv_mem hd), ?_⟩
  rw [Subgroup.mem_centralizer_iff] at hwC ⊢
  intro a ha
  have ha' : d⁻¹ * a * d ∈ Submission.Blueprint.involutions (H : Set G) := by
    refine ⟨H.mul_mem (H.mul_mem (H.inv_mem hdH) ha.1) hdH, ?_⟩
    have h1 : d⁻¹ * a * d = (MulAut.conj d⁻¹) a := by rw [MulAut.conj_apply, inv_inv]
    rw [h1, MulEquiv.orderOf_eq, ha.2]
  have h2 := hwC (d⁻¹ * a * d) ha'
  calc a * (d * w * d⁻¹) = d * (d⁻¹ * a * d) * w * d⁻¹ := by group
    _ = d * ((d⁻¹ * a * d) * w) * d⁻¹ := by group
    _ = d * (w * (d⁻¹ * a * d)) * d⁻¹ := by rw [← h2]
    _ = (d * w * d⁻¹) * a := by group

end Work.PSU3.StageB.StepB
