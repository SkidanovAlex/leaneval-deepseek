import ChallengeDeps
import Submission.Work.UBBInputs.Bogoliubov
import Submission.Work.UBBInputs.WordBridgeFile
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs.Chain` — the repaired end-to-end chain

The three inputs of `Work.DLWire.hpres_of_dlSlide` are delivered here in their
normalisation-correct form, and the paper's `hpres` (the single remaining gap of
`Submission.theorem_1_2`) is produced from them through the *delivered* UBB
assembly (`Work.UBB.boxShape_of_inputs` / `Work.UBB.Consumer.hpres_of_UBB`):

```
  WordBridgeResidual v h        (1  FS thm:CompareBoxEnergy + eq:CompareGC)
        │  wordBridge_of_residual
        ▼
  Work.UBB.WordBridge v h ─┐
                           ├─ Work.UBB.fsShape_of_inputs / boxShape_of_inputs
  SpectralInput v h J ε₀ η₀ ┘        (DELIVERED)
        ▲  Sliding.spectralInput_of_cov        │
        │                                      ▼
  AprioriNPlusCov ── aprioriNPlusCov_of_dlSlideCov ── DLSlideCov ◄── SlidingSumData
        │                                              │   slidingRawNorm_of_data
        │                                              │   (FS eq:BSsliding2 = BS Thm 3.10
        │                                              │    + the DL per-box bound)
  BogoliubovLowCov ◄── BogoliubovGain                  │            (FS §9–11)
```

The ESY / `hEgc` side of the ledger is **absent by design** (it is the sibling
`Work.DLWire.Egc` / `Work.SecondOrder` / `Work.ESYRound5` chapters'): "`Φ` is
low" is a hypothesis of `SlidingSumData` and `BogoliubovLowCov`, and states
above the threshold are handled by the delivered dichotomy
(`Work.UBB.theta_ge_lambda`, inside `Work.UBB.fsShape_of_inputs`).
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

/-- The shared FS window function of FS `eq:apriorinn+`. -/
noncomputable def fsWindow (v : ℝ³ → ℝ) (b J K_B : ℝ) (N : ℕ) (L : ℝ) : ℝ :=
  (2 * L ^ 2 / b) * (4 * π * (dens N L) ^ 2 * (a v) * L ^ 3 * (J + K_B ^ 3)
    * (dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ))

/-- **`UBB` from the repaired inputs** (1)+(2)+(3): the canonical per-box
dilute bound `Work.UBB.UBB v η₀`, via the DELIVERED assembly
`Work.UBB.UBB_of_inputs`, from

* the word/Hamiltonian residual `WordBridgeResidual` (⇒ `Work.UBB.WordBridge`
  by the infimum step), and
* the per-state spectral input, produced by
  `Sliding.spectralInput_of_cov` from the covariant sliding data
  `SlidingSumData` (FS `eq:BSsliding2`) and the covariant Bogoliubov window
  bound `BogoliubovLowCov` (FS §9–11) — the two sharing the FS window
  `fsWindow`. -/
theorem UBB_of_UBBInputs {v : ℝ³ → ℝ} {h : ScatSol v} {J ε₀ η₀ b K_B R' : ℝ}
    {W : ℕ → ℝ → ℝ} {d M : ℕ}
    (hv : 0 ≤ v) (ha : 0 ≤ a v) (hJ : lhyC ≤ J) (hε₀ : 0 < ε₀)
    (hb : 0 < b) (hR' : 0 ≤ R')
    (hW : W = fsWindow v b J K_B)
    (hWB : WordBridgeResidual v h)
    (hslide : SlidingSumData v h b K_B R' J ε₀ d M)
    (hBog : BogoliubovLowCov v h J W ε₀ η₀) :
    UBB v η₀ := by
  subst hW
  have hbridge := wordBridge_of_residual hv hWB
  have hslideCov : DLSlideCov v h b K_B R' J ε₀ := dlSlideCov_of_data hslide
  have ha1 : AprioriNPlusCov v h J (fsWindow v b J K_B) ε₀ :=
    aprioriNPlusCov_of_dlSlideCov hb ha hR' hslideCov
  exact UBB_of_inputs hε₀ ha hJ hbridge (spectralInput_of_cov ha1 hBog)

/-- **The paper's `hpres` from the repaired inputs** — FS `thm:LHY-Background`
at the pressure level, i.e. the single remaining gap of
`Submission.theorem_1_2`, from the three inputs (1)+(2)+(3), through the
DELIVERED closed chain `Work.UBB.hpres_of_UBB`.  This is the deliverable of
this chapter: `Work.DLWire.hpres_of_dlSlide` with its three inputs supplied
from the delivered pieces + the named residuals, and modulo the ESY sibling
alone. -/
theorem hpres_of_UBBInputs {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1) {R : ℝ}
    (hR : 0 ≤ R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    {h : ScatSol v} {J ε₀ η₀ η K b K_B R' : ℝ} {W : ℕ → ℝ → ℝ} {d M : ℕ}
    (hav : 0 < a v) (ha : 0 ≤ a v) (hJ : lhyC ≤ J)
    (hε₀ : 0 < ε₀) (hη₀ : 0 < η₀) (hη₀le : η₀ ≤ 1 / 2) (hη : 0 < η) (hηlt : η < η₀)
    (hK : 0 < K) (hb : 0 < b) (hKB : 0 < K_B) (hR' : 0 ≤ R')
    (hW : W = fsWindow v b J K_B)
    (hWB : WordBridgeResidual v h)
    (hslide : SlidingSumData v h b K_B R' J ε₀ d M)
    (hBog : BogoliubovLowCov v h J W ε₀ η₀) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ ρmax : ℝ, 0 < ρmax ∧ ρ < ρmax ∧
      lhyRhs (a v) K (1 / 2 + η) ρ
        ≤ gcPressure v ρmax (8 * π * (a v) * ρ) + 8 * π * (a v) * ρ * ρ :=
  hpres_of_UBB hv hv1 hR hv_supp hav hη₀ hη₀le hη hηlt hK
    (UBB_of_UBBInputs hv ha hJ hε₀ hb hR' hW hWB hslide hBog)

/-- The same from the three inputs with the Bogoliubov step in its **gain form**
`BogoliubovGain` (the additive presentation of the sharp `lhyC`; see
`Bogoliubov.bogoliubovLowCov_iff_gain`). -/
theorem hpres_of_UBBInputs_gain {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1) {R : ℝ}
    (hR : 0 ≤ R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    {h : ScatSol v} {J ε₀ η₀ η K b K_B R' : ℝ} {W : ℕ → ℝ → ℝ} {d M : ℕ}
    (hav : 0 < a v) (ha : 0 ≤ a v) (hJ : lhyC ≤ J)
    (hε₀ : 0 < ε₀) (hη₀ : 0 < η₀) (hη₀le : η₀ ≤ 1 / 2) (hη : 0 < η) (hηlt : η < η₀)
    (hK : 0 < K) (hb : 0 < b) (hKB : 0 < K_B) (hR' : 0 ≤ R')
    (hW : W = fsWindow v b J K_B)
    (hWB : WordBridgeResidual v h)
    (hslide : SlidingSumData v h b K_B R' J ε₀ d M)
    (hBog : BogoliubovGain v h J W ε₀ η₀) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ ρmax : ℝ, 0 < ρmax ∧ ρ < ρmax ∧
      lhyRhs (a v) K (1 / 2 + η) ρ
        ≤ gcPressure v ρmax (8 * π * (a v) * ρ) + 8 * π * (a v) * ρ * ρ :=
  hpres_of_UBBInputs hv hv1 hR hv_supp hav ha hJ hε₀ hη₀ hη₀le hη hηlt hK hb hKB hR'
    hW hWB hslide (bogoliubovLowCov_of_gain hBog)

/-- **The window-free form of the interface**: the convenience variant in which
the Bogoliubov input is stated directly at the FS window `fsWindow v b J K_B`,
so a caller never has to manipulate the `W` variable. -/
theorem hpres_of_UBBInputs_wn {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1) {R : ℝ}
    (hR : 0 ≤ R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    {h : ScatSol v} {J ε₀ η₀ η K b K_B R' : ℝ} {d M : ℕ}
    (hav : 0 < a v) (ha : 0 ≤ a v) (hJ : lhyC ≤ J)
    (hε₀ : 0 < ε₀) (hη₀ : 0 < η₀) (hη₀le : η₀ ≤ 1 / 2) (hη : 0 < η) (hηlt : η < η₀)
    (hK : 0 < K) (hb : 0 < b) (hKB : 0 < K_B) (hR' : 0 ≤ R')
    (hWB : WordBridgeResidual v h)
    (hslide : SlidingSumData v h b K_B R' J ε₀ d M)
    (hBog : BogoliubovLowCov v h J (fsWindow v b J K_B) ε₀ η₀) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ ρmax : ℝ, 0 < ρmax ∧ ρ < ρmax ∧
      lhyRhs (a v) K (1 / 2 + η) ρ
        ≤ gcPressure v ρmax (8 * π * (a v) * ρ) + 8 * π * (a v) * ρ * ρ :=
  hpres_of_UBBInputs hv hv1 hR hv_supp hav ha hJ hε₀ hη₀ hη₀le hη hηlt hK hb hKB hR'
    rfl hWB hslide hBog

/-- The same in the `BogoliubovGain` form. -/
theorem hpres_of_UBBInputs_wn_gain {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1) {R : ℝ}
    (hR : 0 ≤ R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    {h : ScatSol v} {J ε₀ η₀ η K b K_B R' : ℝ} {d M : ℕ}
    (hav : 0 < a v) (ha : 0 ≤ a v) (hJ : lhyC ≤ J)
    (hε₀ : 0 < ε₀) (hη₀ : 0 < η₀) (hη₀le : η₀ ≤ 1 / 2) (hη : 0 < η) (hηlt : η < η₀)
    (hK : 0 < K) (hb : 0 < b) (hKB : 0 < K_B) (hR' : 0 ≤ R')
    (hWB : WordBridgeResidual v h)
    (hslide : SlidingSumData v h b K_B R' J ε₀ d M)
    (hBog : BogoliubovGain v h J (fsWindow v b J K_B) ε₀ η₀) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ ρmax : ℝ, 0 < ρmax ∧ ρ < ρmax ∧
      lhyRhs (a v) K (1 / 2 + η) ρ
        ≤ gcPressure v ρmax (8 * π * (a v) * ρ) + 8 * π * (a v) * ρ * ρ :=
  hpres_of_UBBInputs_wn hv hv1 hR hv_supp hav ha hJ hε₀ hη₀ hη₀le hη hηlt hK hb hKB hR'
    hWB hslide (bogoliubovLowCov_of_gain hBog)

/-- `UBB` from the window-free form of the three inputs. -/
theorem UBB_of_UBBInputs_wn {v : ℝ³ → ℝ} {h : ScatSol v} {J ε₀ η₀ b K_B R' : ℝ}
    {d M : ℕ}
    (hv : 0 ≤ v) (ha : 0 ≤ a v) (hJ : lhyC ≤ J) (hε₀ : 0 < ε₀)
    (hb : 0 < b) (hR' : 0 ≤ R')
    (hWB : WordBridgeResidual v h)
    (hslide : SlidingSumData v h b K_B R' J ε₀ d M)
    (hBog : BogoliubovLowCov v h J (fsWindow v b J K_B) ε₀ η₀) :
    UBB v η₀ :=
  UBB_of_UBBInputs hv ha hJ hε₀ hb hR' rfl hWB hslide hBog

/-- **The consistent instantiation of the remainder**: `Shape.dlSlide_forces_Rprime_nonpos`
shows that the sliding inequality at the *empty* box forces `R' ≤ 0`, so with
the standing `0 ≤ R'` the free a-priori remainder must be taken to be `0`
(which is what FS's own `R_Ψ` is in the `0`-particle sector, `eq:aprioriRn+`).
This variant takes `R' = 0` so that the hypotheses of the chain are jointly
satisfiable: -/
theorem hpres_of_UBBInputs_r0 {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1) {R : ℝ}
    (hR : 0 ≤ R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    {h : ScatSol v} {J ε₀ η₀ η K b K_B : ℝ} {d M : ℕ}
    (hav : 0 < a v) (ha : 0 ≤ a v) (hJ : lhyC ≤ J)
    (hε₀ : 0 < ε₀) (hη₀ : 0 < η₀) (hη₀le : η₀ ≤ 1 / 2) (hη : 0 < η) (hηlt : η < η₀)
    (hK : 0 < K) (hb : 0 < b) (hKB : 0 < K_B)
    (hWB : WordBridgeResidual v h)
    (hslide : SlidingSumData v h b K_B 0 J ε₀ d M)
    (hBog : BogoliubovLowCov v h J (fsWindow v b J K_B) ε₀ η₀) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ ρmax : ℝ, 0 < ρmax ∧ ρ < ρmax ∧
      lhyRhs (a v) K (1 / 2 + η) ρ
        ≤ gcPressure v ρmax (8 * π * (a v) * ρ) + 8 * π * (a v) * ρ * ρ :=
  hpres_of_UBBInputs_wn hv hv1 hR hv_supp hav ha hJ hε₀ hη₀ hη₀le hη hηlt hK hb hKB
    (le_refl 0) hWB hslide hBog

/-- The same, with the sliding input supplied directly in its `DLSlideCov`
form (e.g. by a caller who has already assembled the bundle). -/
theorem hpres_of_UBBInputs' {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1) {R : ℝ}
    (hR : 0 ≤ R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    {h : ScatSol v} {J ε₀ η₀ η K b K_B R' : ℝ} {W : ℕ → ℝ → ℝ}
    (hav : 0 < a v) (ha : 0 ≤ a v) (hJ : lhyC ≤ J)
    (hε₀ : 0 < ε₀) (hη₀ : 0 < η₀) (hη₀le : η₀ ≤ 1 / 2) (hη : 0 < η) (hηlt : η < η₀)
    (hK : 0 < K) (hb : 0 < b) (hKB : 0 < K_B) (hR' : 0 ≤ R')
    (hW : W = fsWindow v b J K_B)
    (hWB : WordBridgeResidual v h)
    (hslide : DLSlideCov v h b K_B R' J ε₀)
    (hBog : BogoliubovLowCov v h J W ε₀ η₀) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ ρmax : ℝ, 0 < ρmax ∧ ρ < ρmax ∧
      lhyRhs (a v) K (1 / 2 + η) ρ
        ≤ gcPressure v ρmax (8 * π * (a v) * ρ) + 8 * π * (a v) * ρ * ρ := by
  subst hW
  have hbridge := wordBridge_of_residual hv hWB
  have ha1 : AprioriNPlusCov v h J (fsWindow v b J K_B) ε₀ :=
    aprioriNPlusCov_of_dlSlideCov hb ha hR' hslide
  exact hpres_of_UBB hv hv1 hR hv_supp hav hη₀ hη₀le hη hηlt hK
    (UBB_of_inputs hε₀ ha hJ hbridge (spectralInput_of_cov ha1 hBog))

end Work.UBBInputs
