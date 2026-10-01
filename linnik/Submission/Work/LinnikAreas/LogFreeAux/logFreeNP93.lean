import Mathlib
import Submission.Work.ZeroDensity.LogFree.logFreeNPOfParams

/-!
# `logFreeNP (93/100) (12/5)` — a clean, importable copy of the LogFree instance II

`Work.ZeroDensity.LogFree.logFreeNP_93_100_twelveFifths`
(`Submission/Work/ZeroDensity/LogFree/logFreeNPInstances.lean`) is the proved, axiom-clean
instance `logFreeNP (93/100) (12/5)` of the unified log-free non-principal zero-density estimate,
and it is one of the two inputs AREA 6 needs
(`Submission/Work/LinnikAreas/area6OfCoreNodes.lean`).

That module cannot however be imported into the AREA 6 chain: it imports
`Submission.Work.ZeroFreeTables.OtherLamCountBounded_of_logFreeNP`, whose transitive imports
include `Submission.Work.ZeroFreeTables.P3.CompletedDerivPF`, which clashes (environment already
contains `Work.ZeroFreeTables.P3.iteratedDeriv_logDeriv_decompose.match_1_1`) with the copy of the
same module under `Submission.Work.LinnikAreas.P3Rect.Work_ZeroFreeTables_P3_CompletedDerivPF` that
the AREA 6 chain pulls in — the pre-existing duplicate-module defect recorded in
`Submission/Work/LinnikAreas/BGTZ/NOTES_workspace_blockers.md`.  (The LogFree chapter notes the
same defect in `LogFree/logFreeNPOfParams.lean:611`.)

This file therefore re-derives the instance from `logFreeNPOfParams` alone (`paramsII` is copied
under the fresh name `params93`, and the proof is the one given in the chapter), so that the AREA 6
chain can use it without importing the clashing module.  `#print axioms` = `[propext,
Classical.choice, Quot.sound]`.
-/

namespace Work.LinnikAreas.LogFreeAux

noncomputable section

open Work.ZeroDensity.LogFree

/-- **Parameter packet II** of `JUTILA_UNIFIED_LEAD.md` §3 (`σ₀ = 93/100`, `2x = 2.37`); a copy of
`Work.ZeroDensity.LogFree.paramsII` under a fresh name. -/
def params93 : Work.ZeroDensity.LogFree.Params where
  σ₀ := 93 / 100
  η := 1 / 1000
  w := 1 / 1000
  u := 59 / 100
  v := 119 / 200
  x := 237 / 200
  hσ₀ := by norm_num
  hσ₀1 := by norm_num
  hη := by norm_num
  hw := by norm_num
  hwu := by norm_num
  huv := by norm_num
  hvx := by norm_num
  P1 := by norm_num
  P2 := by norm_num

/-- **`logFreeNP (93/100) (12/5)`** (`2x = 2.37 < 12/5`), from `logFreeNPOfParams` alone. -/
theorem logFreeNP_93_100_clean : Work.ZeroDensity.LogFree.logFreeNP (93 / 100) (12 / 5) := by
  obtain ⟨C, hC, hh⟩ := Work.ZeroDensity.LogFree.logFreeNPOfParams params93
  refine ⟨C, hC, ?_⟩
  intro q hq _inst σ T hσ hσ1 hT
  have hσ' : params93.σ₀ ≤ σ := by simpa only [params93] using hσ
  have hbase : (1 : ℝ) ≤ (q : ℝ) * T := by
    have h2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    nlinarith
  have hexp : 2 * params93.x * (1 - σ) ≤ (12 / 5) * (1 - σ) := by
    have h0 : (0 : ℝ) ≤ 1 - σ := by linarith
    have hx : 2 * params93.x ≤ 12 / 5 := by norm_num [params93]
    nlinarith
  refine le_trans (hh q hq σ T hσ' hσ1 hT) ?_
  refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hC)
  exact Real.rpow_le_rpow_of_exponent_le hbase hexp

end

end Work.LinnikAreas.LogFreeAux
