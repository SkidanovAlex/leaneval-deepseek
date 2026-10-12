import ChallengeDeps
import Submission.Work.UBBInputs6.Apriori
import Submission.Work.UBBInputs6.BogoliubovSide
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.UBBInputs6.Residuals` — the round-6 ledger

The round-6 answer to the lead's assignment is the following **two named residual lists**, each
a bundle at the corpus carrier (`abox`, `kinWord`, `cnPlus`, `sboxE`) with every member tied to
a named corpus module or a named mathematical statement of FS:

## (A) the a-priori side — `AprioriResiduals`

| member | FS | corpus |
|---|---|---|
| `bundle.hloc : KineticLocalisation d b` | `lem:LocKinEn` (BS Thm 3.10) | `Work.SmallBoxTBWord.tBLocalisation`; the *only* external input (no-substitute analysis `Work/SmallBoxTBWord/NOTES.md` §4) |
| `bundle.hK.hlow`, `bundle.hK.hsum` | `thm:smallbox` (the ESY/trial-state upper bound `hEgc`) | `Submission.BoseGases.smallbox_dl_energy_bound` (delivered) + the count↔density bridge of `Work/UBBInputs2/README.md` §4(c) |
| `bundle.hK.hmass` | the discarded-mass bound | **delivered**: `Work.SmallBoxSliding.compl_mass_le` (+ `hmass_of_complMass`) |
| `bundle.hLP : LocPotentialCorpus` | `lem:LocPotential` | the delivered `Work.SmallBoxSliding.qLHSwordB_integral_u` + the word comparison |
| `bundle.hint`, `bundle.hintRef` | integrability | genuine at the corpus trial space `CSBox`; delivered for compactly supported states (`integrable_qLHSBIntegrand`) |

`aprioriNPlusCov_of_residuals` proves that this list gives FS `eq:apriorinn+` **with the
explicit FS window** `fsWindowC v b J K_B`; that is the first input of the round-6 pair.

## (B) the Bogoliubov side — `BogoliubovResiduals`

| member | FS | corpus |
|---|---|---|
| `layer : TwoTermErrorCov v h J W ε₀ c₁ E` | `thm:BogHamDiag` + `lem:BogIntegral` at the box, with the Bogoliubov errors still present | per-small-box layers: `Work.BlockBound4.diagW_lm_appbogolubov_explicitC` (`D1`), `Work.FSKernelCompare.w2c_acube_integral_ge_w1c` + `Work.SmallBoxKernelMass` (`w₂`-mass), `Submission.LhyIntegral` (sharp constant) |
| `hE : E N L ≤ c₁ − lhyC` | the absorption of the errors into the LHY slack | this file's arithmetic (`bogoliubovWindowedCov_of_twoTermError`) |

`bogoliubovWindowedCov_of_residuals` proves that this list gives FS §9–11 at the window,
`BogoliubovWindowedCov v h J W ε₀ η₀`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.UBBInputs6

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open _root_.BoseGases
open Submission.BoseGases
open Work.UBB
open Work.UBBInputs
open Work.UBBInputs2
open Work.UBBInputs4
open Work.UBBInputs5

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. (A) the a-priori residual list -/

/-- **The round-6 a-priori residual list**: the sliding-localisation bundle
`SlidingBundle` (Bratteli–Solovej Thm 3.10 + the per-box energy fields + `lem:LocPotential` +
integrability) together with the easy side conditions (`0 < b`, `0 ≤ a v`, `0 ≤ R'`). -/
structure AprioriResiduals (v : ℝ³ → ℝ) (h : ScatSol v) (b K_B R' J ε₀ : ℝ) (d M : ℕ)
    (R0 : ℝ) : Prop where
  hb : 0 < b
  ha : 0 ≤ a v
  hR' : 0 ≤ R'
  bundle : SlidingBundle v h b K_B R' J ε₀ d M R0

/-- **FS `eq:apriorinn+` from the round-6 a-priori residual list.** -/
theorem aprioriNPlusCov_of_residuals {v : ℝ³ → ℝ} {h : ScatSol v}
    {b K_B R' J ε₀ : ℝ} {d M : ℕ} {R0 : ℝ}
    (hR : AprioriResiduals v h b K_B R' J ε₀ d M R0) :
    AprioriNPlusCov v h J (fsWindowC v b J K_B) ε₀ :=
  aprioriNPlusCov_of_slidingBundle hR.hb hR.ha hR.hR' hR.bundle

/-! ## 2. (B) the Bogoliubov residual list -/

/-- **The round-6 Bogoliubov residual list**: the intermediate two-term Bogoliubov bound with
its relative error `E`, plus the pure arithmetic absorption of that error into the slack of the
LHY constant. -/
structure BogoliubovResiduals (v : ℝ³ → ℝ) (h : ScatSol v) (J : ℝ) (W : ℕ → ℝ → ℝ)
    (ε₀ η₀ c₁ : ℝ) (E : ℕ → ℝ → ℝ) : Prop where
  ha : 0 ≤ a v
  hc₁ : lhyC ≤ c₁
  hE : ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ → E N L ≤ c₁ - lhyC
  layer : TwoTermErrorCov v h J W ε₀ c₁ E

/-- **FS §9–11 at the window from the round-6 Bogoliubov residual list.** -/
theorem bogoliubovWindowedCov_of_residuals {v : ℝ³ → ℝ} {h : ScatSol v} {J : ℝ}
    {W : ℕ → ℝ → ℝ} {ε₀ η₀ c₁ : ℝ} {E : ℕ → ℝ → ℝ}
    (hR : BogoliubovResiduals v h J W ε₀ η₀ c₁ E) :
    BogoliubovWindowedCov v h J W ε₀ η₀ :=
  bogoliubovWindowedCov_of_twoTermError hR.ha hR.hc₁ hR.hE hR.layer

/-! ## 3. The round-6 pair, with the shared window pinned -/

/-- **The round-6 input pair**: the a-priori list (A) and the Bogoliubov list (B), *together
with* the reconciliation that the Bogoliubov window is the a-priori window produced by the
sliding localisation.  This pinning is what makes the pair a genuine decomposition of FS's
`thm:LHY-Box`: both inputs are consumed at one and the same window function `W`. -/
structure Round6Inputs (v : ℝ³ → ℝ) (h : ScatSol v) (J ε₀ η₀ c₁ : ℝ) (W : ℕ → ℝ → ℝ)
    (b K_B R' : ℝ) (d M : ℕ) (R0 : ℝ) (E : ℕ → ℝ → ℝ) : Prop where
  apriori : AprioriResiduals v h b K_B R' J ε₀ d M R0
  bogoliubov : BogoliubovResiduals v h J W ε₀ η₀ c₁ E
  window : W = fsWindowC v b J K_B

/-- The round-6 pair gives FS `eq:apriorinn+` at the shared window. -/
theorem aprioriNPlusCov_of_round6Inputs {v : ℝ³ → ℝ} {h : ScatSol v} {J ε₀ η₀ c₁ : ℝ}
    {W : ℕ → ℝ → ℝ} {b K_B R' : ℝ} {d M : ℕ} {R0 : ℝ} {E : ℕ → ℝ → ℝ}
    (hR : Round6Inputs v h J ε₀ η₀ c₁ W b K_B R' d M R0 E) :
    AprioriNPlusCov v h J W ε₀ := by
  rw [hR.window]
  exact aprioriNPlusCov_of_residuals hR.apriori

/-- The round-6 pair gives FS §9–11 at the shared window. -/
theorem bogoliubovWindowedCov_of_round6Inputs {v : ℝ³ → ℝ} {h : ScatSol v} {J ε₀ η₀ c₁ : ℝ}
    {W : ℕ → ℝ → ℝ} {b K_B R' : ℝ} {d M : ℕ} {R0 : ℝ} {E : ℕ → ℝ → ℝ}
    (hR : Round6Inputs v h J ε₀ η₀ c₁ W b K_B R' d M R0 E) :
    BogoliubovWindowedCov v h J W ε₀ η₀ :=
  bogoliubovWindowedCov_of_residuals hR.bogoliubov

end Work.UBBInputs6
