import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.S_le_H
import Submission.Work.BG.invJCard
import Submission.Work.BG.invJ_sum_conjClasses
import Submission.Work.GLUE.Defs

namespace Work.BG

theorem lemma22EvalWK_Jsum {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Fintype ↥C.P.H]
    (hc : Work.GW2.C16.Compat D C) (θ : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H ℂ) :
    ∑ x ∈ Work.GW2.C16.invJ C, θ x =
      ((Subgroup.centralizer ({D.t1} : Set G)).relIndex D.H : ℂ) *
          θ ⟨D.t1, hc.H_eq.symm ▸ (Work.BG.S_le_H D D.t1_mem)⟩ +
        ((Subgroup.centralizer ({D.t2} : Set G)).relIndex D.H : ℂ) *
          θ ⟨D.t2, hc.H_eq.symm ▸ (Work.BG.S_le_H D D.t2_mem)⟩ := by
  classical
  exact invJ_sum_conjClasses D C hc
    ⟨D.t1, hc.H_eq.symm ▸ (Work.BG.S_le_H D D.t1_mem)⟩
    ⟨D.t2, hc.H_eq.symm ▸ (Work.BG.S_le_H D D.t2_mem)⟩
    rfl rfl (fun x => θ x) (fun g x => θ.conj_eq x g)

end Work.BG
