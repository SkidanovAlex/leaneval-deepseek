import Mathlib
import Submission.Work.GlaubermanZJ.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.GlaubermanZJ

-- Frattini argument (Glauberman 1968, Lemma 3.6): for `H ⊴ G` and `S` a Sylow `p`-subgroup
-- of `H`, one has `G = H · N_G(S)`.  (Mathlib's `Sylow.normalizer_sup_eq_top`.)
theorem frattini_sylow {G : Type*} [Group G] [Finite G] {H : Subgroup G} [H.Normal] {p : ℕ}
    [Fact p.Prime] (S : Sylow p H) :
    (⊤ : Subgroup G) = H ⊔ Subgroup.normalizer (((S : Subgroup H).map H.subtype) : Set G) := by
  rw [eq_comm, sup_comm]
  exact Sylow.normalizer_sup_eq_top S

end Work.GlaubermanZJ
