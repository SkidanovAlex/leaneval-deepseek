import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.ThmF.Setup
import Submission.Work.PSU3.StageA.chVI_prop
import Submission.Work.ThmF.ChV12.KsubSubgroupOfNormal

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageA

theorem Ksub_eq_Kset_cyclic_normal_of_W_ne_bot {G : Type} [Group G] [Finite G]
    {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hW : Work.ThmF.W H t ≠ ⊥) :
    (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t ∧
      IsCyclic ↥(Work.ThmF.Ksub H t) ∧
      ((Work.ThmF.Ksub H t).subgroupOf (Submission.Blueprint.twoPoint H t)).Normal := by
  obtain ⟨hKset, hcyc⟩ := Ksub_eq_Kset_of_W_ne_bot hS hC4 hW
  exact ⟨hKset, hcyc, Work.ThmF.ChV12.KsubSubgroupOfNormal hS.split hKset⟩

end Work.PSU3.StageA
