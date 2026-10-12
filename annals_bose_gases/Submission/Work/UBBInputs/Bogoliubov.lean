import ChallengeDeps
import Submission.Work.UBBInputs.Sliding
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs.Bogoliubov` — input (3): FS §9–11 under the shared window

The deep input, in the normalisation-correct form `BogoliubovLowCov`: a *low*
state (`WordDens ≤ Theta`) inside the shared `n₊`-window (`cnPlus/∫Φ² ≤ W N L`)
has shifted energy density at least `Lambda (a v) C η₀ ρ`.

Two interfaces are provided:

* **`BogoliubovGain`** — the same statement written with the *free background*
  `−4πρ²(a v)` split off, so that the sharp constant appears **additively** as
  the gain coefficient `4πρ²(a v)·lhyC·√(ρ(a v)³)` and the error as
  `4πρ²(a v)·K·(ρ(a v)³)^{1/2+η₀}`.  `bogoliubovLowCov_iff_gain` proves the two
  are the same statement (a `Lambda`-unfolding plus `Real.sqrt_eq_rpow`); this
  is the form in which the rigidity statement is visible: `lhyC` (provenance:
  `Work.UBB.LhyConstant`, the Bogoliubov model integral `Submission.LhyIntegral`)
  and the exponent `1/2 + η₀` are the *only* non-free data; `K` and `C` are
  existentially quantified.
* **monotonicity in the window and in the error coefficient**
  (`bogoliubovLowCov_mono_window`), which is what lets the a-priori chapter and
  this chapter share *one* window function `W`.

## Roadmap (the delivered bricks of the residual)

The residual `BogoliubovLowCov` is FS §9–11 at the big box:

1. *second quantisation* (`prop:Hamilton2ndQuant`) — the per-sector
   `Work.PotWords.qLHSword` splitting (`potsplit_expect`) plus the corpus
   `Work.SmallBoxBogolubov*` layer;
2. *`c`-number substitution* (`thm:Kafz`) and the `K(z)` bound — the
   per-`p` two-mode Bogoliubov diagonalisation at the faithful word, DELIVERED
   as `Work.BlockBound4.diagW_lm_appbogolubov_explicitC` (FS
   `lm:appbogolubov`, `eq:refinedaprioribog`), whose corpus-energy sibling is
   `Submission.BoseGases.lm_appbogolubov_pWord_holds`
   (`Work.SmallBoxD1Final`), together with the `w₂`-mass completion
   (`Work.SmallBoxKernelMass`, `Work.FSKernelCompare`) and the sharp integral
   evaluation (`Submission.LhyIntegral` via `Work.UBB.lhy_model_integral_lhyC`);
3. *the localisation of the Bogoliubov analysis* (`lem:LocMatrices`) — the
   one layer which is NOT delivered at the big box: the delivered D1/block
   bounds are per *small* box, and the passage to the big box is the same
   sliding/`u`-averaging structure as in `Sliding.lean` (FS `eq:BSsliding2`
   again, this time at the `Λ`-level rather than the background level).  Note
   that this layer is genuinely needed: the a-priori/DL background
   `−4πρ²(a v)L³(1 + K_B³√(ρ(a v)³))` is *below* `Λ` for small `ρ`
   (`Λ − DLbg = 4πρ²(a v)L³[(lhyC + K_B³)√(ρ(a v)³) − K(ρ(a v)³)^{1/2+η₀}] > 0`),
   so no a-priori bound can supply the LHY term — the positive correction can
   only come from the state-level Bogoliubov analysis (this is exactly the
   remark recorded in the UBB chapter's §3);
4. the a-priori window bookkeeping (`AprioriNPlusCov`) is *not* part of this
   residual — it is `Sliding.lean`'s output, and `Sliding.spectralInput_of_cov`
   composes the two.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.UBBInputs

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open _root_.BoseGases
open Submission.BoseGases
open Work.UBB

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **`BogoliubovLowCov` ⟺ `BogoliubovGain`**: the sharp expression is the
additive gain over the free background `−4πρ²(a v)`. -/
theorem bogoliubovLowCov_of_gain {v : ℝ³ → ℝ} {h : ScatSol v} {J ε₀ η₀ : ℝ}
    {W : ℕ → ℝ → ℝ} (hg : BogoliubovGain v h J W ε₀ η₀) :
    BogoliubovLowCov v h J W ε₀ η₀ := by
  rcases hg with ⟨K, hK, hK'⟩
  refine ⟨K, hK, fun L hL N hN Φ hw hl => ?_⟩
  have hres := hK' L hL N hN Φ hw hl
  unfold Lambda
  rw [Real.sqrt_eq_rpow]
  linarith [hres]

/-- The converse direction. -/
theorem gain_of_bogoliubovLowCov {v : ℝ³ → ℝ} {h : ScatSol v} {J ε₀ η₀ : ℝ}
    {W : ℕ → ℝ → ℝ} (hB : BogoliubovLowCov v h J W ε₀ η₀) :
    BogoliubovGain v h J W ε₀ η₀ := by
  rcases hB with ⟨C, hC, hC'⟩
  refine ⟨C, hC, fun L hL N hN Φ hw hl => ?_⟩
  have hres := hC' L hL N hN Φ hw hl
  unfold Lambda at hres
  rw [Real.sqrt_eq_rpow] at hres
  linarith [hres]

/-- **The two forms of the Bogoliubov input are the same statement.** -/
theorem bogoliubovLowCov_iff_gain {v : ℝ³ → ℝ} {h : ScatSol v} {J ε₀ η₀ : ℝ}
    {W : ℕ → ℝ → ℝ} :
    BogoliubovLowCov v h J W ε₀ η₀ ↔ BogoliubovGain v h J W ε₀ η₀ :=
  ⟨gain_of_bogoliubovLowCov, bogoliubovLowCov_of_gain⟩

/-- `SpectralInput` (the deep input without any window hypothesis) trivially
gives the covariant Bogoliubov bound: dropping a hypothesis. -/
theorem bogoliubovLowCov_of_spectralInput {v : ℝ³ → ℝ} {h : ScatSol v} {J ε₀ η₀ : ℝ}
    {W : ℕ → ℝ → ℝ} (hS : SpectralInput v h J ε₀ η₀) :
    BogoliubovLowCov v h J W ε₀ η₀ := by
  rcases hS with ⟨C, hC, hlow⟩
  exact ⟨C, hC, fun L hL N hN Φ _ hl => hlow L hL N hN Φ hl⟩

/-- The same at the gain interface. -/
theorem gain_of_spectralInput {v : ℝ³ → ℝ} {h : ScatSol v} {J ε₀ η₀ : ℝ}
    {W : ℕ → ℝ → ℝ} (hS : SpectralInput v h J ε₀ η₀) :
    BogoliubovGain v h J W ε₀ η₀ :=
  gain_of_bogoliubovLowCov (bogoliubovLowCov_of_spectralInput hS)

/-- **Monotonicity in the shared window, hypothesis side**: the window is a
*hypothesis* of `BogoliubovLowCov`, so a *larger* window makes the statement
stronger.  Hence a Bogoliubov bound at `W'` gives one at any `W ≤ W'`; this is
the direction a caller needs when the a-priori chapter produces the (possibly
smaller) window it can prove. -/
theorem bogoliubovLowCov_mono_window {v : ℝ³ → ℝ} {h : ScatSol v} {J ε₀ η₀ : ℝ}
    {W W' : ℕ → ℝ → ℝ} (hWW : ∀ N L, W N L ≤ W' N L)
    (hB : BogoliubovLowCov v h J W' ε₀ η₀) : BogoliubovLowCov v h J W ε₀ η₀ := by
  rcases hB with ⟨C, hC, hC'⟩
  refine ⟨C, hC, fun L hL N hN Φ hw hl => ?_⟩
  refine hC' L hL N hN Φ ?_ hl
  have hXn : (0 : ℝ) ≤ sqNormN N L (Φ : X N → ℝ) := le_of_lt Φ.sq_pos
  calc cnPlus L (Φ : X N → ℝ) ≤ W N L * sqNormN N L (Φ : X N → ℝ) := hw
    _ ≤ W' N L * sqNormN N L (Φ : X N → ℝ) := mul_le_mul_of_nonneg_right (hWW N L) hXn

/-- **Monotonicity in the shared window, conclusion side**: enlarging the
window weakens the a-priori conclusion `cnPlus ≤ W·∫Φ²`.  Together with
`bogoliubovLowCov_mono_window` this shows the two sibling inputs can always be
reconciled on the *same* window: prove the a-priori window at the smaller `W`
and the Bogoliubov bound at the larger one. -/
theorem aprioriNPlusCov_mono_window {v : ℝ³ → ℝ} {h : ScatSol v} {J ε₀ : ℝ}
    {W W' : ℕ → ℝ → ℝ} (hWW : ∀ N L, W N L ≤ W' N L)
    (hA : AprioriNPlusCov v h J W ε₀) : AprioriNPlusCov v h J W' ε₀ := by
  intro L hL N hN Φ hlow
  have hXn : (0 : ℝ) ≤ sqNormN N L (Φ : X N → ℝ) := le_of_lt Φ.sq_pos
  calc cnPlus L (Φ : X N → ℝ) ≤ W N L * sqNormN N L (Φ : X N → ℝ) := hA L hL N hN Φ hlow
    _ ≤ W' N L * sqNormN N L (Φ : X N → ℝ) := mul_le_mul_of_nonneg_right (hWW N L) hXn

end Work.UBBInputs
