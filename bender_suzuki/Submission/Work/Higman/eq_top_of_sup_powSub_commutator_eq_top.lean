import Mathlib
import Submission.Work.Higman.PowSub
import Submission.Work.PGroup.eq_of_sup_frattiniIn_eq
import Submission.Work.PGroup.frattini_eq_agemo_sup_commutator

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman

theorem eq_top_of_sup_powSub_commutator_eq_top {G : Type} [Group G] [Finite G]
    (hG : IsPGroup 2 G) {H : Subgroup G}
    (h : H ⊔ (Work.Higman.powSub (⊤ : Subgroup G) 2 ⊔ ⁅(⊤ : Subgroup G), ⊤⁆) = ⊤) :
    H = ⊤ := by
  -- `℧¹(G) = G ^ (2)`: the `2`-nd powers of `G` generate the same subgroup as `℧¹(G)`.
  have hpow : Work.Higman.powSub (⊤ : Subgroup G) 2 = Work.PGroup.agemo 2 1 ⊤ := by
    simp only [Work.Higman.powSub, Work.PGroup.agemo]
    congr 1
  -- For a finite `2`-group, `Φ(G) = ℧¹(G) · [G,G]`.
  have hfr : Work.PGroup.frattiniIn (⊤ : Subgroup G)
      = Work.Higman.powSub (⊤ : Subgroup G) 2 ⊔ ⁅(⊤ : Subgroup G), ⊤⁆ := by
    rw [Work.PGroup.frattini_eq_agemo_sup_commutator Nat.prime_two ⊤ (hG.to_subgroup ⊤), hpow]
  -- The Frattini subgroup consists of non-generators: `H ⊔ Φ(G) = G → H = G`.
  refine Work.PGroup.eq_of_sup_frattiniIn_eq ⊤ H (hG.to_subgroup ⊤) le_top ?_
  rw [hfr]
  exact h

end Work.Higman
