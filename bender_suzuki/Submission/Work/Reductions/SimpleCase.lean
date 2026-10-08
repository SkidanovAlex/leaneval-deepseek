import Mathlib
import Submission.Blueprint.Interfaces
import Submission.Work.Reductions.Defs
import Submission.Work.Reductions.OddResidual
import Submission.Work.Reductions.isSimpleGroup_of_oddCore_eq_bot

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The simple case of the reduction

If `O(G) = 1` and `O^{2'}(G) = G` then `G` is simple, and a simple Bender group already satisfies
the conclusion of Theorem B with `L = G = ⊤`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Submission.Blueprint
open LeanEval.GroupTheory.Defs

namespace Work.Reductions

/-- Case (3) of the reduction: `O(G) = 1`, `O^{2'}(G) = G`. -/
theorem simple_and_benderConclusion_of_top {G : Type} [Group G] [Finite G]
    (hFT : FeitThompsonProp) (hA : ThmAProp) (hfour : HasFourGroup G) {H : Subgroup G}
    (hH : IsStronglyEmbedded H) (hc : oddCore G = ⊥) (hr : oddResidual G = ⊤) :
    IsSimpleGroup G ∧
      (IsSimpleBenderGroup G → BenderConclusion G) := by
  refine ⟨isSimpleGroup_of_oddCore_eq_bot hA hfour hH hc hr, fun hsimple => ?_⟩
  refine ⟨⊤, Subgroup.normal_top, hc ▸ bot_le, by simp, G, inferInstance,
    (Subgroup.topEquiv (G := G)).toMonoidHom, (Subgroup.topEquiv (G := G)).surjective, ?_, hsimple⟩
  have hker : (Subgroup.topEquiv (G := G)).toMonoidHom.ker = ⊥ := by
    ext x
    simp [MonoidHom.mem_ker]
  rw [hker, hc]
  simp

end Work.Reductions
