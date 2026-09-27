import Mathlib
import Submission.Work.EQ.Defs
import Submission.Work.EQ.GermMain

/-!
# The linearised local stable germ of the equichordal half map

The existence proof is in `Submission/Work/EQ/GermMain.lean`: the germ is `hOf (rhoLim a)`
where `rhoLim a` is the fixed point of the contraction `ThetaOf a`.
-/

namespace Work.EQ

open Complex Metric

/-- **Local analytic stable curve, linearised (Rychlik §5.7, §10).** For every eccentricity
`0 < a < 1` the germ functional equation has a holomorphic solution with `h 0 = 0`,
`h' 0 = -1`, real on the real axis. -/
theorem exists_stableGerm {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ∃ (h : ℂ → ℂ) (r : ℝ), IsStableGerm a h r :=
  ⟨hOf (rhoLim a), germR a, isStableGerm_hOf ha0 ha1⟩

end Work.EQ
