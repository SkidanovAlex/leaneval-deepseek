import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring.RingNF
import Submission.Work.BoseB6Est.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `fsTau` vanishes below the lower cutoff

`Work.BoseB6.fsTau εT c₁ c₂ r = (1−ε_T)[|r|−c₁]₊² + ε_T[|r|−c₂]₊²`.  For
`0 ≤ r ≤ c₁ ≤ c₂` both truncated brackets vanish (`|r| = r`), so `fsTau` is
identically zero there — independently of `ε_T`.
-/

namespace Work.BoseB6Est

theorem fsTau_eq_zero {εT c1 c2 r : ℝ} (hc1 : 0 ≤ c1) (hc12 : c1 ≤ c2) (hr0 : 0 ≤ r) (hrc : r ≤ c1) :
    Work.BoseB6.fsTau εT c1 c2 r = 0 := by
  have habs : |r| = r := abs_of_nonneg hr0
  rw [Work.BoseB6.fsTau, habs]
  have h1 : max (r - c1) 0 = 0 := max_eq_right (by linarith)
  have h2 : max (r - c2) 0 = 0 := max_eq_right (by linarith)
  rw [h1, h2]
  ring

end Work.BoseB6Est
