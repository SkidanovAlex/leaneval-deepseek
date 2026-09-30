/-
# Continuity of the basic maps

The sign-change action, the slack functions and the action on the two copies of `Q̄` are continuous;
these are the continuity inputs of the class-atlas presentation of `M̄`.
-/
import Mathlib
import Submission.Work.FoldInst.Action

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Matrix
open scoped Matrix

namespace Work.FoldInst

@[fun_prop]
theorem continuous_act (g : Fin 4 → ZMod 2) : Continuous (act g) := by
  unfold act HypModel.rot4
  fun_prop

theorem continuous_sideSlack (S : Fin 24) : Continuous (sideSlack S) := by
  unfold sideSlack
  fun_prop

theorem continuous_truncSlack (w : Fin 24) : Continuous (truncSlack w) := by
  unfold truncSlack
  fun_prop

theorem continuous_actX (γ : Gg) : Continuous (actX γ) := by
  unfold actX
  fun_prop

/-- The continuity inputs of the class atlas, bundled. -/
theorem continuous_all :
    (∀ g : Fin 4 → ZMod 2, Continuous (act g)) ∧
    (∀ γ : Gg, Continuous (actX γ)) ∧
    (∀ S : Fin 24, Continuous (sideSlack S)) ∧
    (∀ w : Fin 24, Continuous (truncSlack w)) :=
  ⟨continuous_act, continuous_actX, continuous_sideSlack, continuous_truncSlack⟩

end Work.FoldInst
