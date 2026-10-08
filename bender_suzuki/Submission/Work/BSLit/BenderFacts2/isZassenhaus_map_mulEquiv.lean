import Mathlib
import Submission.Work.BSLit.Defs
import Submission.Work.BSLit.BenderFacts2.threePointAPI
import Submission.Work.BSLit.BenderFacts2.isZassenhaus_of_inf_conj_eq_bot
import Submission.Work.BSLit.BenderFacts2.inf_conj_eq_bot_map_mulEquiv

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BSLit.BenderFacts2

-- The two halves of the three-point condition are proved in the modules
-- `…isZassenhaus_of_inf_conj_eq_bot` (reformulated there as the single iff
-- `isZassenhaus_iff_inf_conj_eq_bot`) and, in the reverse direction,
-- `…threePointAPI` (`inf_conj_eq_bot_of_isZassenhaus`).

/-- **`IsZassenhaus` is invariant under group isomorphisms**: `H ≤ G` is Zassenhaus (the pointwise stabiliser of three distinct points of `G ⧸ H` is trivial) iff its image under `e : G ≃* G'` is Zassenhaus. Route: the condition is equivalent to the purely group-theoretic `∀ x y, x ∉ H → y ∉ H → x⁻¹ * y ∉ H → H ⊓ conj x H ⊓ conj y H = ⊥` (the pointwise stabiliser of the three points `H, xH, yH` is `H ⊓ xHx⁻¹ ⊓ yHy⁻¹`, and any triple of distinct points can be moved to that form by an element of `G`), which transports along a `MulEquiv` using `conj (e x) (H.map e) = (conj x H).map e`. -/
theorem isZassenhaus_map_mulEquiv {G G' : Type*} [Group G] [Group G'] (H : Subgroup G)
    (e : G ≃* G') :
    Submission.Blueprint.IsZassenhaus H ↔
      Submission.Blueprint.IsZassenhaus (H.map e.toMonoidHom) := by
  rw [isZassenhaus_iff_inf_conj_eq_bot H,
    isZassenhaus_iff_inf_conj_eq_bot (H.map e.toMonoidHom)]
  exact inf_conj_eq_bot_map_mulEquiv H e

end Work.BSLit.BenderFacts2
