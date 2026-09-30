/-
# The two copies of `Q̄` and the sign-change action

The space of the Ratcliffe–Tschantz identification `~₁` is the disjoint union of two copies of the
truncated 24-cell `Q̄`; this file defines that space `Xbar = ZMod 2 × Q̄`, the action of the group
`Gg` of side pairings on it, and the elementary laws of the action.
-/
import Mathlib
import Submission.Work.FoldInst.Basic
import Submission.Work.FoldInst.Polytope

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

/-- In `ZMod 2` negation is the identity. -/
theorem ZMod2_neg (a : ZMod 2) : -a = a := by revert a; decide

/-- `ZMod 2` is an elementary abelian `2`-group. -/
theorem ZMod2_add_self (a : ZMod 2) : a + a = 0 := by revert a; decide

/-- The two copies of `Q̄`. -/
abbrev Xbar := ZMod 2 × Qbar

/-- The type generator of the `t`-th of the five types. -/
def typeGen (t : Fin 5) : Gg := (toG (typeGenK t), (typeGenFlip t : ZMod 2))

/-- The action of the group `Gg` on the two copies of `Q̄`: the Klein sign change on the coordinates
and the copy bit on the first factor. -/
def actX (γ : Gg) (x : Xbar) : Xbar :=
  ⟨x.1 + γ.2, ⟨act γ.1 x.2.1, (Qbar_act γ.1 x.2.1).mpr x.2.2⟩⟩

@[simp] theorem actX_fst (γ : Gg) (x : Xbar) : (actX γ x).1 = x.1 + γ.2 := rfl

@[simp] theorem actX_snd (γ : Gg) (x : Xbar) : (actX γ x).2.1 = act γ.1 x.2.1 := rfl

theorem actX_zero (x : Xbar) : actX 0 x = x := by
  refine Prod.ext ?_ (Subtype.ext ?_)
  · show x.1 + (0 : Gg).2 = x.1
    rw [show (0 : Gg).2 = (0 : ZMod 2) from rfl, add_zero]
  · show act (0 : Gg).1 x.2.1 = x.2.1
    rw [show (0 : Gg).1 = (0 : Fin 4 → ZMod 2) from rfl, act_zero]

theorem actX_add (γ η : Gg) (x : Xbar) :
    actX γ (actX η x) = actX (γ + η) x := by
  refine Prod.ext ?_ (Subtype.ext ?_)
  · show (x.1 + η.2) + γ.2 = x.1 + (γ + η).2
    rw [show (γ + η).2 = γ.2 + η.2 from rfl]
    abel
  · show act γ.1 (act η.1 x.2.1) = act (γ + η).1 x.2.1
    rw [show (γ + η).1 = γ.1 + η.1 from rfl, act_add]

theorem actX_neg (γ : Gg) (x : Xbar) : actX (-γ) x = actX γ x := by
  refine Prod.ext ?_ (Subtype.ext ?_)
  · show x.1 + (-γ).2 = x.1 + γ.2
    rw [show (-γ).2 = -γ.2 from rfl, ZMod2_neg]
  · show act (-γ).1 x.2.1 = act γ.1 x.2.1
    rw [show (-γ).1 = -γ.1 from rfl, act_neg]

end Work.FoldInst
