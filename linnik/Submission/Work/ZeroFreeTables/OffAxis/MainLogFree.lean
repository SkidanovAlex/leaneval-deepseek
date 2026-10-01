/-
# ZeroFreeTables/OffAxis/MainLogFree

The off-axis assembly with the **unified log-free non-principal zero-density estimate**
`Work.ZeroDensity.LogFree.logFreeNP σ₀ c` (`JUTILA_UNIFIED_LEAD.md` §3) in place of the
over-strong all-character hypothesis `FamDensityEpsRange (4/5) 1 2`.

`OffAxis/exists_stripFree_height_of_logFreeNP` turns the log-free estimate into the strip
provider that `hbOffAxis_of_strip` consumes, so this file is the one-line wiring.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.Main
import Submission.Work.ZeroFreeTables.OffAxis.exists_stripFree_height_of_logFreeNP

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

open Work.ZeroFreeTables.OffAxis

/-- **`HBOffAxis` from the height-`L` certificates and the unified log-free estimate.** -/
theorem hbOffAxis_of_rect_logFreeNP (hC : RectCertC) (hS : RectCertS)
    {σ₀ c : ℝ} (hσ0 : σ₀ < 1) (hc : 0 < c)
    (h : Work.ZeroDensity.LogFree.logFreeNP σ₀ c) : HBOffAxis :=
  hbOffAxis_of_strip hC hS (exists_stripFree_height_of_logFreeNP hσ0 hc h)

end Work.ZeroFreeTables
