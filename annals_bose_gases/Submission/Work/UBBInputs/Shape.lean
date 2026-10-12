import ChallengeDeps
import Submission.Work.SboxEBGroup
import Submission.Work.UBBInputs.Sliding
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs.Shape` — the degenerate sectors and the shape defects

Three machine-checked facts about the *shapes* of the delivered inputs, needed by
the lead's wiring:

* **`wordBridgeResidual_zero`** — the `N = 0` sector of residual (1) is
  automatic (both sides vanish: `dens 0 L = 0`, `wordInf 0 L 0 v h = 0`,
  `Rayl 0 L v Ψ = 0`).  So input (1) needs proving only at `N ≥ 1`.
* **`dlSlide_forces_Rprime_nonpos`** / **`dlSlideCov_forces_Rprime_nonpos`** —
  the `N = 0` sector of FS `eq:BSsliding2` (in the delivered and in the
  repaired form) *forces* `R' ≤ 0`: at the empty box every word vanishes and
  `cnPlus = 0`, so the inequality reads `R' ≤ 0`.  Combined with the lead's
  standing hypothesis `0 ≤ R'` (`Work.UBB.aprioriNPlus_of_state`,
  `Work.DLWire.hpres_of_dlSlide`), this pins `R' = 0` — i.e. the free
  "a-priori remainder" `R'` must be taken to be `0` (which is consistent with
  FS `eq:aprioriRn+`, where `R_Ψ = 0` when the state has no particles).  This
  is not a defect of the *shape* of the inequality — FS's own `n = 0` case is
  the same — but it *is* a constraint on the calling convention.
* **`not_aprioriNPlus_of_low_nontrivial`** — the delivered `AprioriNPlus` is
  *false* as soon as one low state has `cnPlus ≠ 0`
  (`aprioriNPlus_forces_cnPlus_zero`, `Normalisation.lean`).
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

/-! ## 1. The `N = 0` sector of the word bridge -/

/-- `𝓗 0 v Ψ = 0`: both sums of the Hamiltonian are empty. -/
lemma hamiltonian_zero (v : ℝ³ → ℝ) (Ψ : X 0 → ℝ) (x : X 0) :
    𝓗 0 v Ψ x = 0 := by
  simp [BoseGases.𝓗]

/-- `Rayl 0 L v Ψ = 0` for every canonical box state. -/
lemma rayl_zero {v : ℝ³ → ℝ} (L : ℝ) (Ψ : CInfty0Box 0 L) :
    Rayl 0 L v Ψ = 0 := by
  have hnum : (∫ x in box 0 L, (Ψ : X 0 → ℝ) x * 𝓗 0 v (Ψ : X 0 → ℝ) x) = 0 := by
    simp [hamiltonian_zero]
  simp [Rayl, hnum]

/-- The corpus word of a `0`-particle state vanishes. -/
lemma wordDens_zero {v : ℝ³ → ℝ} {h : ScatSol v} (L μ : ℝ) (Φ : X 0 → ℝ) :
    WordDens 0 L μ v h Φ = 0 := by
  rw [WordDens, Submission.BoseGases.sboxE_zero (L) (μ) (wPairC L v) (wPairC L (g0 v h)) Φ]
  simp

/-- `wordInf 0 L μ v h = 0`. -/
lemma wordInf_zero {v : ℝ³ → ℝ} {h : ScatSol v} {L : ℝ} (hL : 0 < L) (μ : ℝ) :
    wordInf 0 L μ v h = 0 := by
  haveI : Nonempty (CSBox 0 L) := nonempty_CSBox 0 hL
  unfold wordInf
  rw [iInf_congr (fun Φ : CSBox 0 L => wordDens_zero L μ (Φ : X 0 → ℝ))]
  exact ciInf_const

/-- **The `N = 0` sector of the word/Hamiltonian residual is automatic.** -/
theorem wordBridgeResidual_zero {v : ℝ³ → ℝ} {h : ScatSol v} {L : ℝ} (hL : 1 ≤ L)
    (Ψ : CInfty0Box 0 L) :
    wordInf 0 L (dens 0 L) v h + 8 * π * (a v) * (dens 0 L) ^ 2 ≤ Rayl 0 L v Ψ / L ^ 3 := by
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL
  rw [wordInf_zero hLpos, rayl_zero L Ψ]
  simp [dens]

/-! ## 2. The `R'` constraint -/

/-- **The empty box forces `R' ≤ 0`** (delivered `DLSlide`). -/
theorem dlSlide_forces_Rprime_nonpos {v : ℝ³ → ℝ} {h : ScatSol v}
    {b K_B R' J ε₀ : ℝ} (hb : 0 < b) (hε₀ : 0 ≤ ε₀) {L : ℝ} (hL : 1 ≤ L)
    (hd : Work.DLWire.DLSlide v h b K_B R' J ε₀) : R' ≤ 0 := by
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL
  haveI : Nonempty (CSBox 0 L) := nonempty_CSBox 0 hLpos
  obtain ⟨Φ⟩ := ‹Nonempty (CSBox 0 L)›
  have hdense : dens 0 L * (a v) ^ 3 ≤ ε₀ := by simp [dens]; exact hε₀
  have hlow : WordDens 0 L (dens 0 L) v h (Φ : X 0 → ℝ) ≤ Theta (a v) J (dens 0 L) := by
    rw [wordDens_zero L (dens 0 L) (Φ : X 0 → ℝ), Theta]
    simp [dens]
  have hres := hd L hL 0 hdense Φ hlow
  have hcn : cnPlus L (Φ : X 0 → ℝ) = 0 := by simp [cnPlus]
  have hen : EnergyWord 0 L (dens 0 L) v h Φ = 0 := by
    rw [energyWord_eq]
    change sboxE 0 L (dens 0 L) (wPairC L v) (wPairC L (g0 v h)) (Φ : X 0 → ℝ)
        / sqNormN 0 L (Φ : X 0 → ℝ) = 0
    rw [Submission.BoseGases.sboxE_zero (L) (dens 0 L) (wPairC L v) (wPairC L (g0 v h)) (Φ : X 0 → ℝ)]
    simp
  rw [hcn, hen] at hres
  simpa [dens] using hres

/-- **The empty box forces `R' ≤ 0`** (repaired `DLSlideCov`). -/
theorem dlSlideCov_forces_Rprime_nonpos {v : ℝ³ → ℝ} {h : ScatSol v}
    {b K_B R' J ε₀ : ℝ} (hε₀ : 0 ≤ ε₀) {L : ℝ} (hL : 1 ≤ L)
    (hd : DLSlideCov v h b K_B R' J ε₀) : R' ≤ 0 := by
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL
  haveI : Nonempty (CSBox 0 L) := nonempty_CSBox 0 hLpos
  obtain ⟨Φ⟩ := ‹Nonempty (CSBox 0 L)›
  have hdense : dens 0 L * (a v) ^ 3 ≤ ε₀ := by simp [dens]; exact hε₀
  have hlow : WordDens 0 L (dens 0 L) v h (Φ : X 0 → ℝ) ≤ Theta (a v) J (dens 0 L) := by
    rw [wordDens_zero L (dens 0 L) (Φ : X 0 → ℝ), Theta]
    simp [dens]
  have hres := hd L hL 0 hdense Φ hlow
  have hcn : cnPlus L (Φ : X 0 → ℝ) = 0 := by simp [cnPlus]
  have hen : EnergyWord 0 L (dens 0 L) v h Φ = 0 := by
    rw [energyWord_eq]
    change sboxE 0 L (dens 0 L) (wPairC L v) (wPairC L (g0 v h)) (Φ : X 0 → ℝ)
        / sqNormN 0 L (Φ : X 0 → ℝ) = 0
    rw [Submission.BoseGases.sboxE_zero (L) (dens 0 L) (wPairC L v) (wPairC L (g0 v h)) (Φ : X 0 → ℝ)]
    simp
  rw [hcn, hen] at hres
  simpa [dens] using hres

/-! ## 3. The delivered `AprioriNPlus` is false for any nontrivial low state -/

/-- **Refutation of the delivered `Work.UBB.AprioriNPlus`**: if some box in the
dilute window carries a low state with `cnPlus ≠ 0`, the delivered a-priori
input is false.  (The repaired `AprioriNPlusCov` is what FS prove; see
`Normalisation.aprioriNPlus_forces_cnPlus_zero`.) -/
theorem not_aprioriNPlus_of_low_nontrivial {v : ℝ³ → ℝ} {h : ScatSol v} {J : ℝ}
    {W : ℕ → ℝ → ℝ} {ε₀ : ℝ}
    (hex : ∃ L : ℝ, 1 ≤ L ∧ ∃ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ ∧
      ∃ Φ : CSBox N L,
        WordDens N L (dens N L) v h (Φ : X N → ℝ) ≤ Theta (a v) J (dens N L) ∧
        cnPlus L (Φ : X N → ℝ) ≠ 0) :
    ¬ AprioriNPlus v h J W ε₀ := by
  rintro hA
  obtain ⟨L, hL, N, hN, Φ, hlow, hcn⟩ := hex
  exact hcn (aprioriNPlus_forces_cnPlus_zero hA hL hN hlow)

end Work.UBBInputs
