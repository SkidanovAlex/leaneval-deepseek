import Mathlib
import Submission.Work.SSGRoute.wordBarDefs
import Submission.Work.SSGRoute.EKerDefs
import Submission.Work.SSGRoute.pSeries_inter_lcs_general
import Submission.Work.SSGRoute.freeLie_regular_odd
import Submission.Work.SSGRoute.FF5.EBL
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- The transport `E(j,j) ≅ barLie (Fin n × G) j`, equivariant for the involution `δ`. -/
theorem E_iso_barLie (G : Type*) [Group G] (n : ℕ) (δ : G) (hδ : δ * δ = 1) (hδ1 : δ ≠ 1)
    (j : ℕ) (hj : 1 ≤ j) :
    ∃ e : ↥(Work.SSGRoute.flowQuotSucc 2 G n j j).ker ≃*
        Multiplicative ↥(Work.SSGRoute.barLie (Fin n × G) j),
      ∀ c : ↥(Work.SSGRoute.flowQuotSucc 2 G n j j).ker,
        ((Multiplicative.toAdd (e (Work.SSGRoute.flowKerSmul G n j δ c)) :
            ↥(Work.SSGRoute.barLie (Fin n × G) j)) : Work.SSGRoute.WordBar (Fin n × G))
          = Work.SSGRoute.wordBarσ (Fin n × G) (Work.SSGRoute.basisPerm G n δ)
              ((Multiplicative.toAdd (e c) : ↥(Work.SSGRoute.barLie (Fin n × G) j)) :
                Work.SSGRoute.WordBar (Fin n × G)) := by
  refine ⟨Work.SSGRoute.diagOdd.ebl_iso (G := G) (n := n) j hj, ?_⟩
  intro c
  exact Work.SSGRoute.diagOdd.ebl_iso_flowKerSmul (G := G) (n := n) j hj δ c

end Work.SSGRoute
