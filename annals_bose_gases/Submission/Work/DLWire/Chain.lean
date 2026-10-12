import ChallengeDeps
import Submission.Work.DLWire.SmallBox
import Submission.Work.UBB.Apriori
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.DLWire.Chain` — the end-to-end UBB chain with the re-wired DL bound

This module runs FS's a-priori chain end to end with the **re-wired** DL bound
(`Submission.BoseGases.smallbox_dl_energy_bound`,
`Submission/Work/DLWire/SmallBox.lean`) as the per-box input, and records the
exact named inputs that remain for the lead's final `hpres` wiring.

## The chain (every step PROVED here)

```
  re-wired DL bound  ──►  per-box lower profile  ──┐
   (DLWire/SmallBox)      (DLWire/SmallBox,        │
                           `…_at_count`)           │   FS eq:BSsliding2
                                                   │  (the named localisation)
                                                   ▼
        DLSlide v h b K_B R' J ε₀   ── aprioriNPlus_of_dlSlide ──►  AprioriNPlus
                                                   │
        BogoliubovLow v h J W ε₀ η₀  ───────────────┼── Work.UBB.uniformBoxBound
                                                   ▼
                                 Work.UBB.UBB v η₀ ── Work.UBB.hpres_of_UBB
                                                   ▼
                             hpres  (the paper's thm:LHY-Background at pressure level)
```

* `DLSlide v h b K_B R' J ε₀` — FS `eq:BSsliding2` (`thm:aprioriHLambda`, step
  2) at the corpus per-box word `Work.UBB.EnergyWord`: for every *low* state
  (`WordDens ≤ Theta`) of a box `(L, N)` in the dilute window,

      `R' + (b/2L²)·cnPlus Φ − 4πρ²(av)L³(1 + K_B³(ρ(av)³)^{1/2}) ≤ EnergyWord Φ`,   `ρ = N/L³`.

  **Its per-box half is now PROVED**: the sliding-sum identity
  `Work.SmallBoxSliding.Sliding.sliding_sum_identity` instantiates its per-box
  energy `eBf` from the per-box bound (`smallbox_dl_energy_bound`), and the
  re-wired DL bound supplies that slot at *every* count
  (`smallbox_dl_energy_bound_at_count`), in the faithful word
  `Work.BlockBound4.diagWeBAt`; `Work.BlockBound4.diagWWord_le_kinWord_gap`
  converts faithful to honest.  What remains is FS's operator-level
  localisation (cited from Bratteli–Solovej, Thm 3.10; corpus residual
  `Work.SmallBoxTBWord.Sliding.tBLocalisation`) plus the telescoping identity
  of `Work.SmallBoxSliding.Words`/`Telescope`.
* `aprioriNPlus_of_dlSlide` (PROVED) — `DLSlide` gives FS `eq:apriorinn+`'s
  excited-count window with the explicit `W` (`Work.UBB.aprioriNPlus_of_state`).
* `UBB_of_dlSlide` (PROVED) — `WordBridge` + `DLSlide` + `BogoliubovLow` give
  `Work.UBB.UBB v η₀` (`Work.UBB.uniformBoxBound`).
* `hpres_of_dlSlide` (PROVED) — the same gives the paper's pressure-level
  `hpres` (`Work.UBB.hpres_of_UBB`), i.e. the single remaining gap of
  `Submission.theorem_1_2`.

## The ledger of named inputs (for the lead)

1. `Work.UBB.WordBridge v h` — the word/Hamiltonian dictionary (FS
   `thm:CompareBoxEnergy`);
2. `DLSlide v h b K_B R' J ε₀` — FS `eq:BSsliding2`; **its per-box energy slot
   is the PROVED re-wired DL bound**, the remaining content is the
   Bratteli–Solovej localisation + the telescoping;
3. `Work.UBB.BogoliubovLow v h J W ε₀ η₀` — FS §9–11, where the sharp
   `lhyC = 128/(15√π)` enters;
4. the **ESY/`hEgc` side** (`eq:aprioriPsi`: existence of a low-energy trial
   state, `Work.SecondOrder.Main.exists_hEgc_of_quasiFreeBound'`,
   `Work.ESYRound5.Main.exists_hEgc_of_round5Data`) is a NAMED hypothesis of
   the sibling ESY chapters.  It is **not consumed by UBB**: "Φ is low" is a
   *hypothesis* of `DLSlide`/`BogoliubovLow`, and the states above the
   threshold are handled by the dichotomy (`Work.UBB.theta_ge_lambda`).  It is
   needed for the thermodynamic limit and for non-vacuity, and stays a named
   ESY hypothesis.
-/

noncomputable section

open MeasureTheory Metric Filter
open _root_.BoseGases
open Submission BoseGases
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.DLWire

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **FS `eq:BSsliding2` at the corpus word** (`thm:aprioriHLambda`, step 2):
the per-state sliding localisation.  This is the exact hypothesis of
`Work.UBB.aprioriNPlus_of_state` (and of `Work.SmallBoxSliding.cnPlus_and_R_le`),
so it is definitionally the shape the corpus's sliding chapter consumes.

Its **per-box energy slot is the PROVED re-wired DL bound** (see the module
note); the remaining content is the operator-level localisation
(`Work.SmallBoxTBWord.Sliding.tBLocalisation`, FS's citation of
Bratteli–Solovej Thm 3.10) together with the telescoping identity of
`Work.SmallBoxSliding.Words`/`Telescope`. -/
def DLSlide (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (b K_B R' J ε₀ : ℝ) : Prop :=
  ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ,
    Work.UBB.dens N L * (a v) ^ 3 ≤ ε₀ → ∀ Φ : CSBox N L,
      Work.UBB.WordDens N L (Work.UBB.dens N L) v h (Φ : X N → ℝ)
          ≤ Work.UBB.Theta (a v) J (Work.UBB.dens N L) →
      R' + (b / (2 * L ^ 2)) * cnPlus L (Φ : X N → ℝ)
        - 4 * π * (Work.UBB.dens N L) ^ 2 * (a v) * L ^ 3
            * (1 + K_B ^ 3 * (Work.UBB.dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ))
        ≤ Work.UBB.EnergyWord N L (Work.UBB.dens N L) v h Φ

/-- **The a-priori `n₊` window from the sliding localisation** (`PROVED`): FS
`eq:apriorinn+`'s excited-count window, with the explicit FS-shaped window
`W N L = (2L²/b)·4π·(N/L³)²·(a v)·L³·(J+K_B³)·((N/L³)(a v)³)^{1/2}`. -/
theorem aprioriNPlus_of_dlSlide {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v}
    {J b K_B ε₀ R' : ℝ} (hb : 0 < b) (hKB : 0 < K_B) (ha : 0 ≤ a v) (hR' : 0 ≤ R')
    (hslide : DLSlide v h b K_B R' J ε₀) :
    Work.UBB.AprioriNPlus v h J
      (fun N L => (2 * L ^ 2 / b) * (4 * π * (Work.UBB.dens N L) ^ 2 * (a v) * L ^ 3
        * (J + K_B ^ 3) * (Work.UBB.dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ))) ε₀ :=
  Work.UBB.aprioriNPlus_of_state hb hKB ha hR' hslide

/-- **The UBB assembly with the re-wired DL bound** (`PROVED`): the uniform
dilute box bound `Work.UBB.UBB v η₀` from the word/Hamiltonian dictionary, the
per-state sliding localisation (whose per-box half is the re-wired DL bound) and
the Bogoliubov window bound — through `Work.UBB.uniformBoxBound`. -/
theorem UBB_of_dlSlide {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v}
    {J ε₀ η₀ b K_B R' : ℝ} {W : ℕ → ℝ → ℝ}
    (hε₀ : 0 < ε₀) (hA : 0 ≤ a v) (hJ : Work.UBB.lhyC ≤ J)
    (hb : 0 < b) (hKB : 0 < K_B) (hR' : 0 ≤ R')
    (hbridge : Work.UBB.WordBridge v h) (hslide : DLSlide v h b K_B R' J ε₀)
    (hW : W = fun N L => (2 * L ^ 2 / b) * (4 * π * (Work.UBB.dens N L) ^ 2 * (a v) * L ^ 3
        * (J + K_B ^ 3) * (Work.UBB.dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ)))
    (hBog : Work.UBB.BogoliubovLow v h J W ε₀ η₀) :
    Work.UBB.UBB v η₀ := by
  subst hW
  exact Work.UBB.uniformBoxBound hε₀ hA hJ hbridge
    (aprioriNPlus_of_dlSlide hb hKB hA hR' hslide) hBog

/-- **The paper's `hpres` from the re-wired chain** (`PROVED`): the pressure-level
FS `thm:LHY-Background` — the single remaining gap of
`Submission.theorem_1_2` — from the named inputs of the module note (the
word/Hamiltonian dictionary, the sliding localisation at the re-wired DL bound,
and the Bogoliubov window bound), through the CLOSED chain
`Work.UBB.hpres_of_UBB`. -/
theorem hpres_of_dlSlide {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1) {R : ℝ}
    (hR : 0 ≤ R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    {h : Work.UBB.ScatSol v} {J ε₀ η₀ η K b K_B R' : ℝ} {W : ℕ → ℝ → ℝ}
    (hav : 0 < a v) (ha : 0 ≤ a v) (hJ : Work.UBB.lhyC ≤ J)
    (hε₀ : 0 < ε₀) (hη₀ : 0 < η₀) (hη₀le : η₀ ≤ 1 / 2) (hη : 0 < η) (hηlt : η < η₀)
    (hK : 0 < K) (hb : 0 < b) (hKB : 0 < K_B) (hR' : 0 ≤ R')
    (hbridge : Work.UBB.WordBridge v h) (hslide : DLSlide v h b K_B R' J ε₀)
    (hW : W = fun N L => (2 * L ^ 2 / b) * (4 * π * (Work.UBB.dens N L) ^ 2 * (a v) * L ^ 3
        * (J + K_B ^ 3) * (Work.UBB.dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ)))
    (hBog : Work.UBB.BogoliubovLow v h J W ε₀ η₀) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ ρmax : ℝ, 0 < ρmax ∧ ρ < ρmax ∧
      lhyRhs (a v) K (1 / 2 + η) ρ
        ≤ gcPressure v ρmax (8 * π * (a v) * ρ) + 8 * π * (a v) * ρ * ρ :=
  Work.UBB.hpres_of_UBB hv hv1 hR hv_supp hav hη₀ hη₀le hη hηlt hK
    (UBB_of_dlSlide hε₀ ha hJ hb hKB hR' hbridge hslide hW hBog)

end Work.DLWire
