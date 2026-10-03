import Mathlib
import Submission.Work.OROneRel.wgtMMDefs
import Submission.Work.OROneRel.wgtPsiThetaBasic

namespace Work.OROneRel

universe u

theorem wgtCompositions {α : Type u} [DecidableEq α] (c : α → ℤ) (t : α) (u : FreeGroup α)
    (hct : c t = 1) (hcu : Work.OROneRel.cohom c u = 1)
    (hFw : Work.OROneRel.FreiheitssatzAt (Work.OROneRel.wW c t u))
    (hc : Work.OROneRel.IsCyclicallyReducedRelator (Work.OROneRel.wW c t u))
    (hA : Work.OROneRel.wW c t u ∉ Subgroup.closure (FreeGroup.of '' Work.OROneRel.wTA c t u))
    (hB : Work.OROneRel.wW c t u ∉ Subgroup.closure (FreeGroup.of '' Work.OROneRel.wTB c t u))
    (hphi : Work.OROneRel.wPhiOfHyp c t u hFw hc hA hB)
    (hchain : Work.OROneRel.wChainHyp c t u hFw hc hA hB)
    (hrel : FreeGroup.lift (Work.OROneRel.wThetaFun c t u hFw hc hA hB) u = 1) :
    ∃ hcompat : Work.OROneRel.wCompatHyp c t u hct hcu hFw hc hA hB,
      ((Work.OROneRel.wPsi c t u hct hcu hFw hc hA hB hcompat).comp
            (Work.OROneRel.wTheta c t u hFw hc hA hB hrel) = MonoidHom.id (Work.OROneRel.wG u)) ∧
      ((Work.OROneRel.wTheta c t u hFw hc hA hB hrel).comp
            (Work.OROneRel.wPsi c t u hct hcu hFw hc hA hB hcompat)
          = MonoidHom.id (Work.OROneRel.wK c t u hFw hc hA hB)) := by
  have hcompat : wCompatHyp c t u hct hcu hFw hc hA hB :=
    wgc_wBaseHom_compat (c := c) (t := t) (u := u) hct hcu hFw hc hA hB hphi
  exact ⟨hcompat,
    wgc_wPsi_comp_wTheta (c := c) (t := t) (u := u) hct hcu hFw hc hA hB hcompat hrel,
    wgc_wTheta_comp_wPsi (c := c) (t := t) (u := u) hct hcu hFw hc hA hB hcompat hrel hchain⟩

end Work.OROneRel
