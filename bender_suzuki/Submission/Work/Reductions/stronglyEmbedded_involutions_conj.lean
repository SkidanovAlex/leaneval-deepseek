import Mathlib
import Submission.Work.Reductions.Defs
import Submission.Work.Reductions.stronglyEmbedded_normalizer_eq
import Submission.Work.Reductions.stronglyEmbedded_centralizer_le
import Submission.Work.Reductions.stronglyEmbedded_eq_of_mem_conj
import Submission.Work.ThreePoints.exists_involution_conj_of_odd_orderOf_mul
import Submission.Work.ThreePoints.TwoPointTransitive
import Submission.Work.ThreePoints.involutions_conj_of_stronglyEmbedded
import Submission.Work.ThreePoints.Omega

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Reductions

theorem stronglyEmbedded_involutions_conj {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {u v : G} (hu : orderOf u = 2)
    (hv : orderOf v = 2) : ∃ g : G, g * u * g⁻¹ = v := by
  -- Peterfalvi I Ch. I §2 Prop. 1 (b): in a finite group with a strongly embedded subgroup,
  -- any two involutions are conjugate.
  exact isConj_iff.mp (Work.ThreePoints.involutions_conj_of_stronglyEmbedded hH hu hv)

end Work.Reductions
