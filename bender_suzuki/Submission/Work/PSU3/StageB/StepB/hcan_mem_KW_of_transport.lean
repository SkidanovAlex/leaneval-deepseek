import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.StageB.Omega.API
import Submission.Work.PSU3.StageB.Canon
import Submission.Work.PSU3.StageB.Frame

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageB.StepB

theorem hcan_mem_KW_of_transport {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    (htN : ∀ w : fr.KW, (t : G) * (w : G) * (t : G) ∈ fr.KW)
    {x : ↥Q} (hx1 : (x : G) ≠ 1)
    (hxm : ((Work.PSU3.StageB.hcan hS.split x : ↥(Submission.Blueprint.twoPoint H t)) : G) ∈ fr.KW) :
    (∀ w : fr.KW, ((Work.PSU3.StageB.hcan hS.split (Work.PSU3.StageB.kact hS fr w x) :
        ↥(Submission.Blueprint.twoPoint H t)) : G) ∈ fr.KW) ∧
      (((Work.PSU3.StageB.hcan hS.split (Work.PSU3.StageB.fcan hS.split x) :
        ↥(Submission.Blueprint.twoPoint H t)) : G) ∈ fr.KW) := by
  refine ⟨?_, ?_⟩
  · -- **H3**: `h(x^w) = (t w t)⁻¹ h(x) w` for `x^w = w⁻¹ x w = kact hS fr w x`.
    intro w
    obtain ⟨xa, hxa, -, -, hh⟩ :=
      canon_conj_fun hS.split hx1
        (⟨(w : G), fr.KW_le w.2⟩ : ↥(Submission.Blueprint.twoPoint H t))
    have hxa' : xa = kact hS fr w x := by
      apply Subtype.ext
      rw [hxa, kact_coe]
    rw [← hxa', hh]
    exact (fr.KW).mul_mem ((fr.KW).mul_mem ((fr.KW).inv_mem (htN w)) hxm) w.2
  · -- **H2/H4c**: `h(f(x)) = h(x)⁻¹`.
    rw [(fcan_fcan hS.split hx1).2.1]
    exact (fr.KW).inv_mem hxm

end Work.PSU3.StageB.StepB
