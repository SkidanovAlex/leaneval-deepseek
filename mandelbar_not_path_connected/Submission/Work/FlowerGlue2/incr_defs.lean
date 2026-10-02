import Mathlib
import Submission.Work.FlowerGlue2.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.FlowerGlue2.incr_defs` — the threshold `rsmall`, the constant `Cin` and their API

This module carries **verbatim** the definitions and the elementary estimates that
`Submission/Work/FlowerGlue2/box_lands_attr.lean` introduced for the per-step increment of the
`c₀`-chart coordinate:

* `Work.FlowerGlue2.rsmall P` — the smallness threshold on `‖ζ‖` for which every per-step
  estimate holds;
* `Work.FlowerGlue2.Cin P = 4‖κ₀‖ + 4A + 2‖h₁‖` — the constant of the first-order term;
* `rsmall_pos`, `rsmall_le_r`, `rsmall_le_one`, `rsmall_mul_le`, `zeta_h_small`, `one_add_ne`,
  `h_norm_bounds'`.

They are duplicated here **because `box_lands_attr.lean` does not currently compile**: it imports
`Submission.Work.FlowerGlue2.box_deep_attr`, a module which was removed from the workspace after
its statement was judged unprovable as written (`NOTES_FALSE_box_deep_attr2.md`).  The definitions
above depend on none of that: they use only `ParNormal.bounds`.  Consumers that want the
increment expansion can therefore avoid the broken import chain entirely by importing this module
(the lemma `Work.FlowerGlue2.incr_expansion_aux` does exactly that).

**If `box_lands_attr.lean` is ever repaired**, it will reintroduce the very same names, and this
module (and *not* the increment lemma) should then be deleted: the two cannot be imported
together.
-/

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open Filter Set Metric
open scoped Topology

namespace Work.FlowerGlue2

open Work.PARIMPL (ParNormal Ft gtc)

noncomputable section

variable {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}

/-- The uniform bounds on the germ inside the chart ball: `‖h ζ‖ ≤ 2` and `1/2 ≤ ‖h ζ‖`. -/
theorem h_norm_bounds' (P : ParNormal d) {ζ : ℂ} (hζ : ‖ζ‖ < P.r) :
    ‖P.h c₀ ζ‖ ≤ 2 ∧ 1 / 2 ≤ ‖P.h c₀ ζ‖ := by
  have hb := P.bounds c₀ (mem_ball_self P.hρ₀)
  exact ⟨hb.2.2.2.1 ζ hζ, hb.2.2.2.2.1 ζ hζ⟩

/-- The smallness threshold on `‖ζ‖` for which all the per-step estimates hold. -/
def rsmall (P : ParNormal d) : ℝ :=
  min (P.r / 2) (min (1 / 64) (1 / (64 * (1 + ‖P.h1 c₀‖ + P.A + ‖P.κ c₀‖))))

/-- The constant of the first-order term of the increment. -/
def Cin (P : ParNormal d) : ℝ := 4 * ‖P.κ c₀‖ + 4 * P.A + 2 * ‖P.h1 c₀‖

theorem rsmall_pos (P : ParNormal d) : 0 < rsmall P := by
  have h1 : 0 < P.r / 2 := by linarith [P.hr]
  have h2 : (0 : ℝ) < 1 / 64 := by norm_num
  have h3 : (0 : ℝ) < 1 / (64 * (1 + ‖P.h1 c₀‖ + P.A + ‖P.κ c₀‖)) := by
    apply one_div_pos.mpr
    have hn : (0 : ℝ) ≤ ‖P.h1 c₀‖ := norm_nonneg _
    have hA : (0 : ℝ) ≤ P.A := P.hA
    have hk : (0 : ℝ) ≤ ‖P.κ c₀‖ := norm_nonneg _
    linarith
  exact lt_min h1 (lt_min h2 h3)

theorem rsmall_le_r (P : ParNormal d) : rsmall P < P.r := by
  have h1 : rsmall P ≤ P.r / 2 := min_le_left _ _
  linarith [P.hr]

theorem rsmall_le_one (P : ParNormal d) : rsmall P ≤ 1 / 64 :=
  le_trans (min_le_right _ _) (min_le_left _ _)

theorem rsmall_mul_le (P : ParNormal d) :
    rsmall P * (1 + ‖P.h1 c₀‖ + P.A + ‖P.κ c₀‖) ≤ 1 / 64 := by
  have h : rsmall P ≤ 1 / (64 * (1 + ‖P.h1 c₀‖ + P.A + ‖P.κ c₀‖)) :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  have hpos : 0 < 1 + ‖P.h1 c₀‖ + P.A + ‖P.κ c₀‖ := by
    have hn : (0 : ℝ) ≤ ‖P.h1 c₀‖ := norm_nonneg _
    have hA : (0 : ℝ) ≤ P.A := P.hA
    have hk : (0 : ℝ) ≤ ‖P.κ c₀‖ := norm_nonneg _
    linarith
  calc rsmall P * (1 + ‖P.h1 c₀‖ + P.A + ‖P.κ c₀‖)
      ≤ 1 / (64 * (1 + ‖P.h1 c₀‖ + P.A + ‖P.κ c₀‖))
          * (1 + ‖P.h1 c₀‖ + P.A + ‖P.κ c₀‖) :=
        mul_le_mul_of_nonneg_right h (by linarith)
    _ = 1 / 64 := by field_simp

theorem zeta_h_small (P : ParNormal d) {ζ : ℂ} (hζ : ‖ζ‖ ≤ rsmall P) :
    ‖ζ * P.h c₀ ζ‖ ≤ 1 / 2 := by
  have hr : ‖ζ‖ < P.r := lt_of_le_of_lt hζ (rsmall_le_r P)
  have h2 := (h_norm_bounds' P hr).1
  have h64 : ‖ζ‖ ≤ 1 / 64 := le_trans hζ (rsmall_le_one P)
  rw [norm_mul]
  nlinarith [norm_nonneg ζ, norm_nonneg (P.h c₀ ζ)]

theorem one_add_ne (P : ParNormal d) {ζ : ℂ} (hζ : ‖ζ‖ ≤ rsmall P) :
    1 + ζ * P.h c₀ ζ ≠ 0 := by
  intro h
  have h2 : ‖ζ * P.h c₀ ζ‖ = 1 := by
    have h' : ζ * P.h c₀ ζ = -1 := by linear_combination h
    rw [h', norm_neg, norm_one]
  have h3 := zeta_h_small P hζ
  linarith

end

end Work.FlowerGlue2
