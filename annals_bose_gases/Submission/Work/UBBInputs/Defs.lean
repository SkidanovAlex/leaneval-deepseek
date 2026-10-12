import ChallengeDeps
import Submission.Work.DLWire.Chain
import Submission.Work.SmallBoxSliding.Band
import Submission.Work.SmallBoxSliding.Jensen
import Submission.Work.SmallBoxSliding.boxMass_integral_u
import Submission.Work.SmallBoxSliding.chiSmallB_continuous_joint
import Submission.Work.SmallBoxSliding.integral_chiMass_eq
import Submission.Work.SmallBoxSliding.integral_chiSmallB_sq_u
import Submission.Work.SmallBoxSliding.nBoxInd_integral_u
import Submission.Work.SmallBoxSliding.qLHSwordB_integral_u
import Submission.Work.SmallBoxTBWord.Sliding
import Submission.Work.SmallBoxTBWord.boxP_contDiff
import Submission.Work.SmallBoxTBWord.chiSmallNormSq_eq_choose
import Submission.Work.SmallBoxTBWord.tBamp_eq_kinFT
import Submission.Work.SmallBoxTBWord.tBamp_indep_slot
import Submission.Work.SmallBoxTBWord.tBdiagForm_chiScale_eq_T0Form
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs` — the three named inputs of `Work.DLWire.hpres_of_dlSlide`

**Assignment.** Deliver the UBB *named inputs* — the three non-ESY inputs of the
delivered end-to-end chain `Work.DLWire.hpres_of_dlSlide` — from the delivered
pieces, naming honestly whatever remains:

1. `Work.UBB.WordBridge v h` (FS `thm:CompareBoxEnergy` + `eq:CompareGC` at the
   finite box);
2. `Work.DLWire.DLSlide v h b K_B R' J ε₀` (FS `eq:BSsliding2`);
3. `Work.UBB.BogoliubovLow v h J W ε₀ η₀` (FS §9–11, where `lhyC = 128/(15√π)`
   enters).

## What this chapter contains

* **`Defs.lean`** (this file) — the vocabulary: the *normalisation-correct*
  repairs `DLSlideCov`, `AprioriNPlusCov`, `BogoliubovLowCov` of the three
  delivered inputs (§2 below says why they are needed), and the residuals
  `WordBridgeResidual`, `SlidingSumData`, `SlidingRawNorm`, `BogoliubovGain`.
* **`Normalisation.lean`** — the machine-checked scaling analysis: the three
  delivered inputs are *not* normalisation-correct (they carry a
  scale-invariant hypothesis `WordDens ≤ Θ` together with a *non*-invariant
  conclusion `cnPlus ≤ W`), and the repairs; plus the calibration
  `BogoliubovLow ↔ SpectralInput` (the delivered window is vacuous in the
  delivered normalisation).
* **`WordBridgeFile.lean`**, **`Sliding.lean`**, **`Bogoliubov.lean`** — the
  reductions of the three (repaired) inputs to precisely named residuals.
* **`Chain.lean`** — the end-to-end chain `hpres` from the three repaired
  inputs, through the delivered `Work.UBB` assembly.
* **`README.md`** — the ledger and the roadmap.

## 1. The normalisation issue (read this first)

The corpus `CSBox N L` (`Work/SboxEB.lean`) is the *unnormalised* trial space:
smooth, nonzero, positive `abox`-`L²`-norm.  But

* `WordDens`, `EnergyWord` are *homogeneous of degree `0`* in the state
  (`Submission.Work.SboxHomogeneity.sboxE_smul`: `sboxE (c•Φ) = c²·sboxE Φ`,
  divided by `∫(cΦ)² = c²∫Φ²`), while
* `cnPlus` is homogeneous of degree `2` (`cnPlus_smul`), and the `eB`-infimum
  normalisation of the corpus's own window statements is the *covariant* one
  (`Work.EBWindowed`: "window `cnPlus(Φ) ≤ B·∫Φ²`").

So a statement of the shape

    (∀ Φ, WordDens Φ ≤ Θ → cnPlus Φ ≤ W)          (†)

is quantor-mismatched: it is scale-invariant in the hypothesis and quadratic in
the conclusion.  Lemma `aprioriNPlus_forces_cnPlus_zero` below derives from (†)
alone that **every low state has `cnPlus = 0`** — i.e. the delivered
`Work.UBB.AprioriNPlus` (and `Work.DLWire.DLSlide`, whose conclusion has the
same mismatch: `R' + (b/2L²)·cnPlus` is quadratic while `EnergyWord` is
invariant) are *not* the statements FS prove.  FS's `eq:BSsliding2`/
`eq:apriorinn+` are statements about **normalised** states (their `Ψ` has
`‖Ψ‖ = 1` in the sector).

The repairs are `DLSlideCov`, `AprioriNPlusCov`, `BogoliubovLowCov` in §2: they
multiply the window/`cnPlus` slot by the state's `abox`-norm `∫Φ²`.  They are
equivalent to the "`∫Φ² = 1`" restriction of the delivered statements, and
`SpectralInput` (which is already scale-correct) follows from
`AprioriNPlusCov + BogoliubovLowCov` exactly as before.  The delivered
`SpectralInput` ⟹ `hpres` route (`Work.UBB.fsShape_of_inputs` /
`boxShape_of_inputs` / `Consumer.hpres_of_UBB`) is untouched.

## 2. The vocabulary

* `sqNormN N L Φ = ∫_{abox N L} Φ²` — the state's squared `abox`-norm;
* `DLSlideCov`, `AprioriNPlusCov`, `BogoliubovLowCov` — the three repaired
  inputs;
* `WordBridgeResidual v h` — FS's finite-box comparison *per state* (the honest
  residual of (1); `Work.UBB.WordBridge` follows by the infimum step,
  `WordBridgeFile.lean`);
* `SlidingSumData` — the residual bundle of the sliding localisation (FS
  `eq:BSsliding2`), with the Bratteli–Solovej–Thm-3.10 field
  `Work.SmallBoxTBWord.Sliding.tBLocalisation` alongside the per-box lower
  bound integrated over the good set; `SlidingRawNorm` is its consequence;
* `BogoliubovGain` — FS §9–11 in the "sharp gain over the free background"
  normalisation (`Defs`/`Bogoliubov.lean`).
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

/-- The squared `abox`-`L²`-norm of a state, `∫_{abox N L} Φ²` — the covariant
normalisation slot of every repaired statement of this chapter. -/
noncomputable def sqNormN (N : ℕ) (L : ℝ) (Φ : X N → ℝ) : ℝ :=
  ∫ x in abox N L, (Φ x) ^ 2

@[simp] lemma sqNormN_def (N : ℕ) (L : ℝ) (Φ : X N → ℝ) :
    sqNormN N L Φ = ∫ x in abox N L, (Φ x) ^ 2 := rfl

lemma sqNormN_pos {N : ℕ} {L : ℝ} (Φ : CSBox N L) : 0 < sqNormN N L (Φ : X N → ℝ) :=
  Φ.sq_pos

/-- **The covariant per-state sliding inequality** — FS `eq:BSsliding2`
(`thm:aprioriHLambda`, step 2) in the normalisation-correct form: the excited
count is normalised by the state's `abox`-norm, so the statement is
scale-invariant.

This is the repair of `Work.DLWire.DLSlide` (see `Normalisation.lean`:
`dlSlide_forces_cnPlus_zero`): the delivered `DLSlide` forces `cnPlus = 0` on
every low state and is therefore not FS's statement.
`dlSlideCov_iff_dlSlideNorm` shows this form is exactly the delivered statement
restricted to states of `abox`-norm `1`. -/
def DLSlideCov (v : ℝ³ → ℝ) (h : ScatSol v) (b K_B R' J ε₀ : ℝ) : Prop :=
  ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ → ∀ Φ : CSBox N L,
    WordDens N L (dens N L) v h (Φ : X N → ℝ) ≤ Theta (a v) J (dens N L) →
    R' + (b / (2 * L ^ 2)) * (cnPlus L (Φ : X N → ℝ) / sqNormN N L (Φ : X N → ℝ))
      - 4 * π * (dens N L) ^ 2 * (a v) * L ^ 3
          * (1 + K_B ^ 3 * (dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ))
      ≤ EnergyWord N L (dens N L) v h Φ

/-- `Work.DLWire.DLSlide` restricted to states of `abox`-norm one.  (Everything
in the conclusion is then an unnormalised word; this is the literal shape FS
prove, and `dlSlideCov_iff_dlSlideNorm` shows `DLSlideCov` is its
scale-covariant closure.) -/
def DLSlideNorm (v : ℝ³ → ℝ) (h : ScatSol v) (b K_B R' J ε₀ : ℝ) : Prop :=
  ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ → ∀ Φ : CSBox N L,
    sqNormN N L (Φ : X N → ℝ) = 1 →
    WordDens N L (dens N L) v h (Φ : X N → ℝ) ≤ Theta (a v) J (dens N L) →
    R' + (b / (2 * L ^ 2)) * cnPlus L (Φ : X N → ℝ)
      - 4 * π * (dens N L) ^ 2 * (a v) * L ^ 3
          * (1 + K_B ^ 3 * (dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ))
      ≤ EnergyWord N L (dens N L) v h Φ

/-- **The covariant a-priori `n₊` window** — FS `thm:aprioriHLambda`,
`eq:apriorinn+` second conjunct, normalisation-correct: a low state's excited
count per unit `abox`-norm is at most `W N L`.

This is the repair of `Work.UBB.AprioriNPlus` (see
`aprioriNPlus_forces_cnPlus_zero`). -/
def AprioriNPlusCov (v : ℝ³ → ℝ) (h : ScatSol v) (J : ℝ) (W : ℕ → ℝ → ℝ)
    (ε₀ : ℝ) : Prop :=
  ∀ L : ℝ, 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ →
    ∀ Φ : CSBox N L,
      WordDens N L (dens N L) v h (Φ : X N → ℝ) ≤ Theta (a v) J (dens N L) →
      cnPlus L (Φ : X N → ℝ) ≤ W N L * sqNormN N L (Φ : X N → ℝ)

/-- **The covariant Bogoliubov window bound** — FS §9–11 (second quantisation,
`c`-number substitution, Bogoliubov diagonalisation) under the *shared* window
`W`, normalisation-correct.

This is the repair of `Work.UBB.BogoliubovLow`.  The window hypothesis
`cnPlus/∫Φ² ≤ W N L` is scale-invariant, so — unlike the delivered form — it is
a genuine restriction (`Normalisation.lean`:
`spectralInput_iff_bogoliubovLow`: the delivered `BogoliubovLow` is *equivalent*
to `Work.UBB.SpectralInput`, i.e. its window is vacuous).

The sharp `lhyC = 128/(15√π)` enters through `Lambda`
(`Work.UBB.LhyConstant` records its provenance as the Bogoliubov model
integral); the error exponent `1/2 + η₀` is explicit and the coefficient `C` is
free. -/
def BogoliubovLowCov (v : ℝ³ → ℝ) (h : ScatSol v) (J : ℝ) (W : ℕ → ℝ → ℝ)
    (ε₀ η₀ : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ L : ℝ, 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ →
      ∀ Φ : CSBox N L,
        cnPlus L (Φ : X N → ℝ) ≤ W N L * sqNormN N L (Φ : X N → ℝ) →
        WordDens N L (dens N L) v h (Φ : X N → ℝ) ≤ Theta (a v) J (dens N L) →
        Lambda (a v) C η₀ (dens N L) ≤ WordDens N L (dens N L) v h (Φ : X N → ℝ)

/-- **The word/Hamiltonian dictionary, per state** — FS `thm:CompareBoxEnergy` +
`eq:CompareGC` at the finite box, in the corpus vocabulary: for *every* box
state `Ψ` of the canonical (Dirichlet) box, the canonical energy density of `Ψ`
dominates the corpus per-box word infimum plus the exact chemical-potential
shift `8π(a v)ρ²`.

This is the honest residual of input (1).  Its content is FS's chain
`e_Λ(ρ) + 8π(a v)ρ² ≤ e(ρ)`, i.e. the conjunction of

* *(identification)* the corpus word `kinWord + qLHSword` at the chosen kernels
  (`wPairC L v`, `wPairC L (g0 v h)`, masses `∬w₁ = 8π(a v)L³`,
  `Q0Chosen.w1c_acube_integral`) **is** the `H_Λ(ρ)` quadratic form — FS
  `eq:w_u`/`eq:defW_12`/`eq:DefU`; and
* *(averaging)* `H_ρ ≥ ∫_u H_{Λ,u}(ρ) du` and `H_{Λ,u}(ρ) ≥ E_Λ(ρ)·1` for every
  `u` (each `H_{Λ,u}` is unitarily equivalent to `H_Λ`), FS's own argument in
  `thm:CompareBoxEnergy` — note that FS have **no** per-state domination
  `word(Ψ) ≤ (H_ρ-form)(Ψ)`, only the `u`-averaged inequality.

`Work.UBB.WordBridge v h` follows by the infimum step
(`wordBridge_of_residual`).  Direction: the corpus word is the *shifted* energy,
so the canonical energy is the *bigger* one. -/
def WordBridgeResidual (v : ℝ³ → ℝ) (h : ScatSol v) : Prop :=
  ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, ∀ Ψ : CInfty0Box N L,
    wordInf N L (dens N L) v h + 8 * π * (a v) * (dens N L) ^ 2
      ≤ Rayl N L v Ψ / L ^ 3

/-- FS `eq:BSsliding2` in the exact shape the delivered sliding chapter
consumes: the *unnormalised* per-state sliding inequality at the corpus per-box
word, for states of `abox`-norm one.  `SlidingSumData` produces it
(`slidingRawNorm_of_data`), and it is equivalent to `DLSlideCov`
(`dlSlideCov_iff_slidingRawNorm`). -/
def SlidingRawNorm (v : ℝ³ → ℝ) (h : ScatSol v) (b K_B R' J ε₀ : ℝ) : Prop :=
  ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ → ∀ Φ : CSBox N L,
    sqNormN N L (Φ : X N → ℝ) = 1 →
    WordDens N L (dens N L) v h (Φ : X N → ℝ) ≤ Theta (a v) J (dens N L) →
    R' + (b / (2 * L ^ 2)) * cnPlus L (Φ : X N → ℝ)
      - 4 * π * (dens N L) ^ 2 * (a v) * L ^ 3
          * (1 + K_B ^ 3 * (dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ))
      ≤ kinWord N L (Φ : X N → ℝ)
        + qLHSword (N := N) L (dens N L) (wPairC L v) (wPairC L (g0 v h))
            (Φ : X N → ℝ)

/-- **The residual bundle of the sliding localisation** (FS `eq:BSsliding2`,
`thm:aprioriHLambda` step 2), for a state of `abox`-norm one.

Its fields, and where each is meant to come from:

* `tBLocalisation N L d b ε c Φ` — **the Bratteli–Solovej Thm 3.10 field**
  (FS cite it verbatim: *"It was proved in [BS] Theorem 3.10 that …"*), i.e.
  `(b/2ℓ²)·cnPlus + ∫_u 𝒯_{B(u)} du ≤ kinWord`; the named residual of
  `Work.SmallBoxTBWord` (`NOTES.md` §4), where the corpus proves the two
  structural halves (a) `tBword_gap_absorbs` and (b) `tBwordKin_le_kinWord`)
  and machine-checks that neither can supply the *integrated* inequality;
* `hbox u` — the per-box lower bound `eBf u ≤ 𝒯_B(u) + (localised potential
  word)`, i.e. FS `thm:smallbox` (delivered, PROVED:
  `Submission.BoseGases.smallbox_dl_energy_bound_at_count`) together with the
  faithful-word/sliding-word comparison (`Work.BlockBound4.diagWWord_le_kinWord_gap`);
* `hpot` — FS `lem:LocPotential`: the `u`-integral of the localised potential
  word (whose telescoped value is the reference word `qLHSwordChi`,
  `Work.SmallBoxSliding.qLHSwordB_integral_u`);
* the integrability fields — corpus bookkeeping on the smooth/compact data;
* `hlow` — the pointwise lower bound on the discarded boxes (FS's
  `−C·χ_{B(u)}²`-mass control; the CLOSED `compl_mass_le` +
  `chiSmallB_badband_integral_law` supply the `hmass` side);
* `hmass` — the discarded `χ`-mass bound;
* `hsum` — **the per-box lower bound integrated over the good set**: the DL
  per-box bound summed over the sliding family, giving the a-priori remainder
  `R'` and the background `−4πρ²(a v)L³(1 + K_B³(ρ(a v)³)^{1/2})` up to the
  discarded-mass loss `C·B`.  This is the half the deliverable calls
  "PROVED": it is `smallbox_dl_energy_bound_at_count` at each box count, and
  the remaining work is the count↔localised-density bookkeeping (the sliding
  chapter's per-box density is the real `n(u)/|B(u)|`, while the DL bundle is
  indexed by the discrete count), which is why it is carried as a field here.

`slidingRawNorm_of_data` turns the bundle into `SlidingRawNorm` using the
delivered `Work.SmallBoxTBWord.Sliding.sliding_sum_bound_of_tBLocalisation`. -/
def SlidingSumData (v : ℝ³ → ℝ) (h : ScatSol v) (b K_B R' J ε₀ : ℝ)
    (d M : ℕ) : Prop :=
  ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ → ∀ Φ : CSBox N L,
    sqNormN N L (Φ : X N → ℝ) = 1 →
    WordDens N L (dens N L) v h (Φ : X N → ℝ) ≤ Theta (a v) J (dens N L) →
    ∃ (ε c C B : ℝ) (eBf : ℝ³ → ℝ),
      0 ≤ C ∧
      Work.SmallBoxTBWord.tBLocalisation N L d b ε c (Φ : X N → ℝ) ∧
      (∀ u : ℝ³, eBf u ≤ Work.SmallBoxTBWord.tBwordB N L d ε c u (Φ : X N → ℝ)
        + Work.SmallBoxSliding.qLHSwordB h M L d (dens N L) u (Φ : X N → ℝ)) ∧
      ((∫ u : ℝ³, Work.SmallBoxSliding.qLHSwordB h M L d (dens N L) u (Φ : X N → ℝ))
        ≤ qLHSword (N := N) L (dens N L) (wPairC L v) (wPairC L (g0 v h))
            (Φ : X N → ℝ)) ∧
      Integrable (fun u : ℝ³ => Work.SmallBoxTBWord.tBwordB N L d ε c u (Φ : X N → ℝ)) ∧
      Integrable (fun u : ℝ³ => Work.SmallBoxSliding.qLHSwordB h M L d (dens N L) u
        (Φ : X N → ℝ)) ∧
      Integrable eBf ∧
      Integrable (fun u : ℝ³ => Work.SmallBoxSliding.chiMass M L d u) ∧
      (∀ u : ℝ³, - C * Work.SmallBoxSliding.chiMass M L d u ≤ eBf u) ∧
      ((∫ u in (Work.SmallBoxSliding.goodSet L d (dens N L))ᶜ,
          Work.SmallBoxSliding.chiMass M L d u) ≤ B) ∧
      (R' - 4 * π * (dens N L) ^ 2 * (a v) * L ^ 3
          * (1 + K_B ^ 3 * (dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ)) + C * B
        ≤ ∫ u in Work.SmallBoxSliding.goodSet L d (dens N L), eBf u)

/-- **The Bratteli–Solovej Thm 3.10 citation, as a single named proposition.**
FS cite it verbatim for `eq:BSsliding2` — *"It was proved in [BS] Theorem 3.10
that …"* — in the form

    (b/2ℓ²)·cnPlus ℓ Φ + ∫_u 𝒯_{B(u)} du ≤ kinWord N ℓ Φ

(`𝒯_{B(u)}` = the renormalised box kinetic of FS `eq:HBU`/`eq:appTB`, the
corpus object `Work.SmallBoxTBWord.tBwordB`).  This is the *other paper*'s
input: `Work.SmallBoxTBWord/NOTES.md` §4 records, with machine-checked support,
why it is not a word-level consequence of anything in the corpus (the
`Q_B`-projection is free for the slot derivative — `Free.kinWordB_projection_free`
— and the plain indicator-box kinetic integrates *exactly* to `kinWord`, leaving
no room for `(b/2ℓ²)cnPlus`; a proof needs the functional calculus of `√−Δ`
with the sliding `Q_{B(u)}`-projections, i.e. BS Lemma 3.3).

It is stated here uniformly over the count, the box side and the state, so that
a prover can attack it as one self-contained operator inequality. -/
def SlidingLocalisation (d b : ℝ) : Prop :=
  ∀ (N : ℕ) (L ε c : ℝ) (Φ : X N → ℝ),
    Work.SmallBoxTBWord.tBLocalisation N L d b ε c Φ

/-- **The remaining fields of the sliding residual bundle** — everything in
`SlidingSumData` except the Bratteli–Solovej citation `SlidingLocalisation`:
the per-box lower bound (`hbox`, intended from the PROVED
`Submission.BoseGases.smallbox_dl_energy_bound_at_count`), FS `lem:LocPotential`
(`hpot`), the integrability bookkeeping, the discarded-mass pair (`hlow`,
`hmass`) and the integrated per-box bound (`hsum`). -/
def BoxSumBound (v : ℝ³ → ℝ) (h : ScatSol v) (b K_B R' J ε₀ : ℝ)
    (d M : ℕ) : Prop :=
  ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ → ∀ Φ : CSBox N L,
    sqNormN N L (Φ : X N → ℝ) = 1 →
    WordDens N L (dens N L) v h (Φ : X N → ℝ) ≤ Theta (a v) J (dens N L) →
    ∃ (ε c C B : ℝ) (eBf : ℝ³ → ℝ),
      0 ≤ C ∧
      (∀ u : ℝ³, eBf u ≤ Work.SmallBoxTBWord.tBwordB N L d ε c u (Φ : X N → ℝ)
        + Work.SmallBoxSliding.qLHSwordB h M L d (dens N L) u (Φ : X N → ℝ)) ∧
      ((∫ u : ℝ³, Work.SmallBoxSliding.qLHSwordB h M L d (dens N L) u (Φ : X N → ℝ))
        ≤ qLHSword (N := N) L (dens N L) (wPairC L v) (wPairC L (g0 v h))
            (Φ : X N → ℝ)) ∧
      Integrable (fun u : ℝ³ => Work.SmallBoxTBWord.tBwordB N L d ε c u (Φ : X N → ℝ)) ∧
      Integrable (fun u : ℝ³ => Work.SmallBoxSliding.qLHSwordB h M L d (dens N L) u
        (Φ : X N → ℝ)) ∧
      Integrable eBf ∧
      Integrable (fun u : ℝ³ => Work.SmallBoxSliding.chiMass M L d u) ∧
      (∀ u : ℝ³, - C * Work.SmallBoxSliding.chiMass M L d u ≤ eBf u) ∧
      ((∫ u in (Work.SmallBoxSliding.goodSet L d (dens N L))ᶜ,
          Work.SmallBoxSliding.chiMass M L d u) ≤ B) ∧
      (R' - 4 * π * (dens N L) ^ 2 * (a v) * L ^ 3
          * (1 + K_B ^ 3 * (dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ)) + C * B
        ≤ ∫ u in Work.SmallBoxSliding.goodSet L d (dens N L), eBf u)

/-- **The Bogoliubov gain** — FS §9–11 written with the *free background*
`−4πρ²(a v)L³` split off: a low state in the shared window has word exceeding
the free background by the LHY term `4πρ²(a v)L³·lhyC·√(ρ(a v)³)`, up to the
free error coefficient `K` and the rigid exponent `1/2 + η₀`.

`BogoliubovGain ↔ BogoliubovLowCov` (`bogoliubovLowCov_iff_gain`) — this is the
form in which the *sharp constant* is visibly additive, and hence the form in
which `Work.UBB.LhyConstant`'s provenance (`lhyC` = the Bogoliubov model
integral `Submission.LhyIntegral`) is the only rigid input. -/
def BogoliubovGain (v : ℝ³ → ℝ) (h : ScatSol v) (J : ℝ) (W : ℕ → ℝ → ℝ)
    (ε₀ η₀ : ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧
    ∀ L : ℝ, 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ →
      ∀ Φ : CSBox N L,
        cnPlus L (Φ : X N → ℝ) ≤ W N L * sqNormN N L (Φ : X N → ℝ) →
        WordDens N L (dens N L) v h (Φ : X N → ℝ) ≤ Theta (a v) J (dens N L) →
        - (4 * π * (dens N L) ^ 2 * (a v))
            + 4 * π * (dens N L) ^ 2 * (a v) * lhyC
                * (dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ)
            - 4 * π * (dens N L) ^ 2 * (a v) * K
                * (dens N L * (a v) ^ 3) ^ (1 / 2 + η₀)
          ≤ WordDens N L (dens N L) v h (Φ : X N → ℝ)

end Work.UBBInputs
