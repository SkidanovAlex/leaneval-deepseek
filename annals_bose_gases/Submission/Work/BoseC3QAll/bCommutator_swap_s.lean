import Mathlib.Tactic.Abel
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Algebra.Module.LinearMap.End
import Submission.Work.BoseB7.bCommutator_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseC3QAll.bCommutator_swap_s`

The pointwise form of the squeezed commutator `[b_{s-k}, b_{-k}†]`: with
`p = s - k`, `q = -k`, the identity

`b_p b_q† = b_q† b_p + [(1 - α_k α_{s-k})(χ̂²(s) - χ̂(k)χ̂(s-k))]`

holds for *every* state `y`, as soon as the box commutator kernel `ccrK` is the
FS kernel `χ̂²(i-j) - χ̂(i)χ̂(j)` (`hker`), `χ̂` is even (`hχ`) and `α` is even
(`hα`).

The operator-level identity `bCommutator_eq` gives
`[b_p, b_q†] = ccrK p q - α_p α_q ccrK (-q) (-p) • 1`; the two kernels are
evaluated by `hker` and simplified with the parities.  This is the hypothesis
form (explicit `hker`, `hχ`, `hα`) of `Work.BoseB7.bCommutator_swap_apply`,
which takes the bundled `EstHyp`.
-/

namespace Work.BoseC3QAll

theorem bCommutator_swap_s {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) (s k : Mode)
    (h1 : F.ccrK (s - k) (-k) = E.hatChiSq s - E.hatChi k * E.hatChi (s - k))
    (h2 : F.ccrK k (k - s) = E.hatChiSq s - E.hatChi k * E.hatChi (s - k))
    (hχ : ∀ s : Mode, E.hatChi (-s) = E.hatChi s)
    (hα : ∀ k : Mode, E.alpha (-k) = E.alpha k) (y : F.H) :
    F.bOp E.alpha (s - k) (F.bOpDag E.alpha (-k) y)
      = F.bOpDag E.alpha (-k) (F.bOp E.alpha (s - k) y)
        + ((1 - E.alpha k * E.alpha (s - k)) * (E.hatChiSq s - E.hatChi k * E.hatChi (s - k))) • y := by
  -- the squeezed-commutator kernel `[b_{s-k}, b_{-k}†]`, evaluated at `y`
  have hpt : F.bOp E.alpha (s - k) (F.bOpDag E.alpha (-k) y)
      - F.bOpDag E.alpha (-k) (F.bOp E.alpha (s - k) y)
      = (F.ccrK (s - k) (-k) - E.alpha (s - k) * E.alpha (-k) * F.ccrK k (k - s)) • y := by
    have hh := LinearMap.congr_fun (Work.BoseB7.bCommutator_eq F E s k) y
    simpa [Work.BoseB7.FockData.bCommutator] using hh
  -- the scalar kernel in the `χ̂`, `χ̂²` language, using the parities of `α, χ̂`
  have hcoef : F.ccrK (s - k) (-k) - E.alpha (s - k) * E.alpha (-k) * F.ccrK k (k - s)
      = (1 - E.alpha k * E.alpha (s - k)) *
          (E.hatChiSq s - E.hatChi k * E.hatChi (s - k)) := by
    rw [h1, h2, hα k]
    ring
  rw [← hcoef, ← hpt]
  abel

end Work.BoseC3QAll
