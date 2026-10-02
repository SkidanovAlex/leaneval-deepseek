/-
Copyright: subproject `Submission/Work/PARIMPL2/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL2.Lavaurs.exists_Rch'` — the chart radius with the `R * P.r` condition

`RchOK' P R` is `RchOK P R` together with `16 ≤ R * P.r` (the condition that the model orbit,
which stays within `8/R` of the chart origin, is inside the germ ball `‖ζ‖ < P.r`).  It is
produced by `exists_Rch` for all `R` above a (larger) threshold.
-/
import Submission.Work.PARIMPL2.Lavaurs.Windows
import Submission.Work.PARIMPL2.Lavaurs.exists_Rch
import Submission.Work.PARIMPL2.Lavaurs.exists_log_mul_le

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL2.Lavaurs

open Work.PARIMPL (ParNormal)

variable {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}

/-- The chart-radius condition with the smallness conditions of the model transit. -/
theorem exists_Rch' (P : ParNormal d) :
    ∃ Rch : ℝ, 4 ≤ Rch ∧ ∀ R ≥ Rch, Work.PARIMPL2.RchOK' P R := by
  obtain ⟨Rch₀, h4, hRch₀⟩ := exists_Rch P
  obtain ⟨Rlog, _hRlog1, hRlog⟩ := exists_log_mul_le (‖P.h1 c₀‖ + 2) (by positivity)
  refine ⟨max Rch₀ (max (16 / P.r + 1) (max (64 * (P.A + ‖P.h1 c₀‖ + 2)) Rlog)), ?_, ?_⟩
  · have : Rch₀ ≤ max Rch₀ (max (16 / P.r + 1) (max (64 * (P.A + ‖P.h1 c₀‖ + 2)) Rlog)) :=
      le_max_left _ _
    linarith
  · intro R hR
    have h1 : Rch₀ ≤ R := le_trans (le_max_left _ _) hR
    have h2 : 16 / P.r + 1 ≤ R :=
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hR)
    have h3 : 64 * (P.A + ‖P.h1 c₀‖ + 2) ≤ R :=
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hR))
    have h4' : Rlog ≤ R :=
      le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _) |>.trans hR)
    refine ⟨hRch₀ R h1, ?_, h3, hRlog R h4'⟩
    have h := (div_le_iff₀ P.hr).mp (by linarith : 16 / P.r ≤ R)
    linarith

end Work.PARIMPL2.Lavaurs

end
