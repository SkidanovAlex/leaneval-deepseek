import Mathlib.Tactic.Abel
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Algebra.Module.LinearMap.End
import Submission.Work.BoseB7.Estimates
import Submission.Work.BoseB7.bCommutator_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB7

theorem bCommutator_swap_apply {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) (h : Work.BoseB7.EstHyp F E)
    (s k : Mode) (y : F.H) :
    F.bOp E.alpha (s - k) (F.bOpDag E.alpha (-k) y)
      = F.bOpDag E.alpha (-k) (F.bOp E.alpha (s - k) y)
        + ((1 - E.alpha k * E.alpha (s - k)) * (E.hatChiSq s - E.hatChi k * E.hatChi (s - k))) • y := by
  -- The squeezed-commutator kernel, evaluated at the state `y` (`bCommutator_eq`).
  have hpt : F.bOp E.alpha (s - k) (F.bOpDag E.alpha (-k) y)
      - F.bOpDag E.alpha (-k) (F.bOp E.alpha (s - k) y)
      = (F.ccrK (s - k) (-k) - E.alpha (s - k) * E.alpha (-k) * F.ccrK k (k - s)) • y := by
    have hh := LinearMap.congr_fun (bCommutator_eq F E s k) y
    simpa [FockData.bCommutator] using hh
  -- The scalar kernel reduces to the box kernel (FS `eq:Commutator_general`) and
  -- the parities of `χ̂` and `α`.
  have hcoef : F.ccrK (s - k) (-k) - E.alpha (s - k) * E.alpha (-k) * F.ccrK k (k - s)
      = (1 - E.alpha k * E.alpha (s - k)) *
          (E.hatChiSq s - E.hatChi k * E.hatChi (s - k)) := by
    rw [h.hasKernel (s - k) (-k), h.hasKernel k (k - s)]
    have e1 : (s - k) - (-k) = s := by abel
    have e2 : k - (k - s) = s := by abel
    have e3 : -(s - k) = k - s := by abel
    rw [e1, e2, h.hatChiEven k, h.alphaEven k, ← e3, h.hatChiEven (s - k)]
    ring
  rw [← hcoef, ← hpt]
  abel

end Work.BoseB7
