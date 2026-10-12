import ChallengeDeps
import Submission.Work.SmallBoxA0.kinP_state_block
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `SmallBoxA0` — the `kinPWord` block bound in bundle form (per state)

`Work.SmallBoxA0.kinP_state_bundle` is `Work.SmallBoxA0.kinP_state_block` packaged
as a statement about the bundle `Work.SmallBoxA0.KinPStateData`.  The bundle
carries the standing smallbox hypotheses, FS's regime conditions and D1's own
inputs (no Bogoliubov residual field): the rung is the PROVED D1, with its
explicit constant `Work.SmallBoxA0.d1C` exposed.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.SmallBoxA0

open Submission BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **The per-state `kinPWord` block bound, bundle form.**  For every
`D : KinPStateData`,

    (¼((D.n+1)/s³ − μ)² − ½μ²)·8π(av)s³ − (272π+40)·μ²(av)s³·Γ − (272π+40)·μ(av)
      ≤ kinPEnergy D.n s μ (wPairC s v) (wPairC s (g0 v h)) c₀ cgap Φ .

No Bogoliubov residual is assumed: the rung is the PROVED
`Work.SmallBoxA0.lm_appbogolubov_pWord_explicitC`. -/
theorem kinP_state_bundle (D : KinPStateData) :
    ((1 / 4 : ℝ) * (((((D.n + 1 : ℕ) : ℝ)) / D.s ^ 3) - D.μ) ^ 2 - (1 / 2 : ℝ) * D.μ ^ 2)
          * (8 * π * (a D.v) * D.s ^ 3)
      - (272 * π + 40) * D.μ ^ 2 * (a D.v) * D.s ^ 3 * kinPGamma D.R0 D.s D.K_B D.μ D.v
      - (272 * π + 40) * D.μ * (a D.v)
    ≤ kinPEnergy D.n D.s D.μ (wPairC D.s D.v) (wPairC D.s (g0 D.v D.h)) D.c₀ D.cgap D.Φ :=
  kinP_state_block (n := D.n) (s := D.s) (μ := D.μ) (R0 := D.R0) (K_B := D.K_B) (Ct := D.Ct)
    (c0 := D.c₀) (cgap := D.cgap) (v := D.v) D.h D.hs D.hμ D.hR0 D.hKB D.hv_nonneg D.hvrad
    D.hv_memL1 D.hv_supp D.hRs D.hμs D.hCt D.hc0 D.hav D.hdil D.hWfin D.hNewton
    D.hΦc D.hnorm D.hwin D.hD D.hbox D.hη D.hbracket D.hcorrreg D.hcgap D.hchi

end Work.SmallBoxA0
