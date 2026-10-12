import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.lpSpace
import Submission.Work.BoseBoxFock.SymBlocks
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

theorem SymQ3TC_blocks {m : ℕ} [NeZero m] {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (f g : Mode → Fin m → ℝ) (F : Work.BoseB7.FockData Mode)
    (E : Work.BoseB7.Q3Env Mode) :
    Work.BoseBoxFock.Q3TC f g F E =
      (((E.z / E.ell ^ 3 : ℝ)) : ℂ)
        • (Work.BoseBoxFock.BQa f g (F.PHset E) E + Work.BoseBoxFock.BQb f g (F.PHset E) E) := by
  rw [Q3TC, BQa, BQb, BQ3a, BQ3b]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [smul_add]

end Work.BoseBoxFock
