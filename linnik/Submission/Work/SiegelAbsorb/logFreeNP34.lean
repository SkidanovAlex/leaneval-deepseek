import Mathlib
import Submission.Work.ZeroDensity.LogFree.logFreeNPOfParams

/-!
# U1 of `AREA6_ROUTE_LEAD.md`: the crude log-free non-principal estimate at `σ₀ = 3/4`

(Namespace `Work.SiegelAbsorb` and directory `Submission/Work/SiegelAbsorb/`, as used by the
requested units of wave 1; the design note proposed `LinnikAreas/SiegelAbsorb/`.)

The parameter packet `params34` (`σ₀ = 3/4`, `2x = 4.38 < 9/2`) turns
`Work.ZeroDensity.LogFree.logFreeNPOfParams` into

`logFreeNP (3/4) (9/2)`,

the *crude* global input of the Siegel-absorption route for AREA 6: every zero with `β < 93/100`
has kernel weight `≤ e^{-(49/10)λ}`, so the crude count `≪ e^{(9/2)λ}` suffices, and the middle
`σ`-range of the Montgomery/HuxleyNPWide routes drops out.
-/

namespace Work.SiegelAbsorb

noncomputable section

open Work.ZeroDensity.LogFree

/-- **Parameter packet** `σ₀ = 3/4`, `η = w = 1/100`, `u = 11/10`, `v = 111/100`, `x = 219/100`;
the conditions P1, P2 of the unified route hold by `norm_num`. -/
def params34 : Work.ZeroDensity.LogFree.Params where
  σ₀ := 3 / 4
  η := 1 / 100
  w := 1 / 100
  u := 11 / 10
  v := 111 / 100
  x := 219 / 100
  hσ₀ := by norm_num
  hσ₀1 := by norm_num
  hη := by norm_num
  hw := by norm_num
  hwu := by norm_num
  huv := by norm_num
  hvx := by norm_num
  P1 := by norm_num
  P2 := by norm_num

/-- **U1**: `logFreeNP (3/4) (9/2)` (`2x = 4.38 < 9/2`). -/
theorem logFreeNP_34_nineHalves : Work.ZeroDensity.LogFree.logFreeNP (3 / 4) (9 / 2) := by
  obtain ⟨C, hC, hh⟩ := Work.ZeroDensity.LogFree.logFreeNPOfParams params34
  refine ⟨C, hC, ?_⟩
  intro q hq _inst σ T hσ hσ1 hT
  have hσ' : params34.σ₀ ≤ σ := by simpa only [params34] using hσ
  have hbase : (1 : ℝ) ≤ (q : ℝ) * T := by
    have h2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    nlinarith
  have hexp : 2 * params34.x * (1 - σ) ≤ (9 / 2) * (1 - σ) := by
    have h0 : (0 : ℝ) ≤ 1 - σ := by linarith
    have hx : 2 * params34.x ≤ 9 / 2 := by norm_num [params34]
    nlinarith
  refine le_trans (hh q hq σ T hσ' hσ1 hT) ?_
  refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hC)
  exact Real.rpow_le_rpow_of_exponent_le hbase hexp

end

end Work.SiegelAbsorb
