import Mathlib
import Submission.Work.UBBInputs6.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.UBBInputs6.Apriori` — the a-priori window at the corpus carrier

This file carries the **first input** of the round-6 pair:

* `aprioriNPlusCov_of_slidingBundle` — FS `eq:apriorinn+` (`AprioriNPlusCov`, the covariant
  window at the corpus carrier) from the round-6 residual bundle `SlidingBundle`, i.e. from

  * the Bratteli–Solovej kinetic localisation `KineticLocalisation` (FS `lem:LocKinEn`, the
    one genuinely external input of the sliding chapter),
  * the per-box energy fields of `BoxSumBoundKernel` (FS `thm:smallbox`; the
    trial-state/ESY `hEgc` side),
  * FS `lem:LocPotential` (`LocPotentialCorpus`) and the integrability bookkeeping,

  with the explicit FS window `fsWindowC v b J K_B`.  The proof is the delivered composition
  `Work.UBBInputs.dlSlideCov_of_kinetic_and_kernel` + `aprioriNPlusCov_of_dlSlideCov`; round 6
  contributes the *bundling* (one named ledger) and the window-shape reconciliation
  (`fsWindowC_eq_shape`).

* `windowCov_transfer` — the **diagnostic** that shows where the round-4 carrier goes wrong:
  the *window* vocabulary is not the problem.  A `CNeu` state of centred-box norm `1` with the
  *word* low-state condition is exactly a `CSBox` state of the corpus's a-priori chapter, so
  `AprioriNPlusCov` at `W` gives `WindowNeu W N L Φ` for it.  What fails (see
  `Work.UBBInputs6.aprioriNPlusNeu_false_of_window_lt_one`) is the *pairing*: round 4's
  low-state condition `LowStateNeu` is measured with the **Dirichlet** box `box N L = [0,L]³`,
  the window with the **centred** box `abox N L`, and the two are not related.

* `aprioriNPlusNeu_trivialWindow` — the positive half of the same finding: round 4's
  `AprioriNPlusNeu` *is* satisfiable, but only with a window of size `≥ N` (the trivial bound
  `cnPlus ≤ N·‖Φ‖²_{abox}`), where the paired Bogoliubov input degenerates to the box theorem.
  Together with the counterexample this pins down the exact satisfiability boundary of the
  round-4/5 list.
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

/-! ## 1. The a-priori window from the round-6 residual bundle -/

/-- **FS `eq:apriorinn+` (covariant window) at the corpus carrier, from the round-6 residual
bundle.**  The window is the explicit FS shape `fsWindowC v b J K_B`. -/
theorem aprioriNPlusCov_of_slidingBundle {v : ℝ³ → ℝ} {h : ScatSol v}
    {b K_B R' J ε₀ : ℝ} {d M : ℕ} {R0 : ℝ}
    (hb : 0 < b) (ha : 0 ≤ a v) (hR' : 0 ≤ R')
    (hB : SlidingBundle v h b K_B R' J ε₀ d M R0) :
    AprioriNPlusCov v h J (fsWindowC v b J K_B) ε₀ := by
  have hslide : DLSlideCov v h b K_B R' J ε₀ :=
    dlSlideCov_of_kinetic_and_kernel hB.hM hB.hd hB.hv_supp hB.hR0 hB.hdR hB.hdRχ
      hB.hint hB.hintRef hB.hloc hB.hK
  exact aprioriNPlusCov_of_dlSlideCov (v := v) (h := h) (b := b) (K_B := K_B)
    (R' := R') (J := J) (ε₀ := ε₀) hb ha hR' hslide

/-- The same composition with the two named pieces **unbundled**: the Bratteli–Solovej
localisation `KineticLocalisation` and the per-box bundle `BoxSumBoundKernel` (plus
`LocPotentialCorpus` and the integrability bookkeeping).  This is the shape of the round-6
ledger: the a-priori input is a **theorem** from these. -/
theorem aprioriNPlusCov_of_kineticLocalisation_and_perBox {v : ℝ³ → ℝ} {h : ScatSol v}
    {b K_B R' J ε₀ : ℝ} {d M : ℕ} {R0 : ℝ}
    (hb : 0 < b) (ha : 0 ≤ a v) (hR' : 0 ≤ R')
    (hM : 1 ≤ M) (hd : (0 : ℝ) < (d : ℝ))
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R0) (hR0 : 0 < R0)
    (hdR : ∀ L : ℝ, 1 ≤ L → R0 ≤ (L * (d : ℝ)) / 16)
    (hdRχ : ∀ L : ℝ, 1 ≤ L → R0 ≤ L * chiR0)
    (hloc : KineticLocalisation (d : ℝ) b)
    (hint : ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, ∀ Φ : CSBox N L,
      Integrable (fun p : ℝ³ × X N =>
        Work.SmallBoxSliding.qLHSBIntegrand h M L (d : ℝ) (dens N L) (Φ : X N → ℝ) p.1 p.2))
    (hintRef : ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, ∀ Φ : CSBox N L,
      IntegrableOn (Work.SmallBoxSliding.qLHSChiIntegrand h M L (d : ℝ) (dens N L)
        (Φ : X N → ℝ)) (abox N L))
    (hK : BoxSumBoundKernel v h b K_B R' J ε₀ d M) :
    AprioriNPlusCov v h J (fsWindowC v b J K_B) ε₀ :=
  aprioriNPlusCov_of_slidingBundle hb ha hR'
    ⟨hM, hd, hv_supp, hR0, hdR, hdRχ, hint, hintRef, hloc, hK⟩

/-! ## 2. The window transfer (the diagnostic) -/

/-- **The window vocabulary transfers.**  Every `CNeu` state with centred-box norm `1` *is* a
corpus `CSBox` state (smooth, nonzero, positive centred-box norm), so the covariant a-priori
window `AprioriNPlusCov` at `W` gives round 4's `WindowNeu W N L Φ` for it, provided the state
satisfies the *word* low-state condition (`WordDens ≤ Theta`, FS `eq:aprioriPsi` at the
corpus word).  Consequently the failure of round 4's `AprioriNPlusNeu`
(`Work.UBBInputs6.aprioriNPlusNeu_false_of_window_lt_one`) cannot be blamed on the window
normalisation: it is the *low-state class* (`LowStateNeu`, an integral over the Dirichlet box
`box N L`) which fails to control the centred-box excited count. -/
theorem windowCov_transfer {v : ℝ³ → ℝ} {h : ScatSol v} {J : ℝ} {W : ℕ → ℝ → ℝ}
    {ε₀ : ℝ} (ha1 : AprioriNPlusCov v h J W ε₀) {L : ℝ} (hL : 1 ≤ L) {N : ℕ}
    (hN : dens N L * (a v) ^ 3 ≤ ε₀) {Φ : CNeu N L} (hsq : aboxSq N L Φ = 1)
    (hlow : WordDens N L (dens N L) v h (Φ : X N → ℝ) ≤ Theta (a v) J (dens N L)) :
    WindowNeu W N L Φ := by
  have hf : (Φ : X N → ℝ) ≠ 0 := Φ.nezero
  have hpos : 0 < ∫ x in abox N L, ((Φ : X N → ℝ) x) ^ 2 := by
    rw [← aboxSq_def, hsq]
    norm_num
  let Ψ : CSBox N L := CSBox.ofFun (N := N) (s := L) Φ.contDiff hf hpos
  have hcoe : (Ψ : X N → ℝ) = (Φ : X N → ℝ) := rfl
  have hwin := ha1 L hL N hN Ψ (by rw [hcoe]; exact hlow)
  rw [WindowNeu]
  have h1 : cnPlus L (Φ : X N → ℝ) ≤ W N L * sqNormN N L (Φ : X N → ℝ) := by
    simpa only [hcoe] using hwin
  have h2 : sqNormN N L (Φ : X N → ℝ) = aboxSq N L Φ := by
    rw [sqNormN_def, aboxSq_def]
  rw [h2] at h1
  first | exact h1 | (rwa [hsq, mul_one] at h1)

/-! ## 3. The trivial window: round 4's a-priori input *is* satisfiable -/

/-- The trivial bound `cnPlus L Φ ≤ N·‖Φ‖²_{abox}` (the corpus `sector_parseval`, delivered as
`Submission.BoseGases.cnPlus_le_norm_sq`): the excited count never exceeds the particle number
times the mass. -/
theorem cnPlus_le_N_mul_aboxSq {N : ℕ} {L : ℝ} (hL : 0 < L) (Φ : CNeu N L) :
    cnPlus L (Φ : X N → ℝ) ≤ (N : ℝ) * aboxSq N L Φ := by
  have h := cnPlus_le_norm_sq (N := N) (ℓ := L) hL (Φ := (Φ : X N → ℝ)) Φ.contDiff.continuous
  rw [aboxSq_def]
  exact h

/-- **Round 4's a-priori input at the trivial window is a theorem**: with the window
`W N L = N` every low state satisfies the covariant window, for *any* low-state condition
(the trivial bound needs no hypothesis on the state beyond smoothness).  Hence
`AprioriNPlusNeu` is satisfiable — but only degenerately: at that window the paired Bogoliubov
input `BogoliubovWindowedNeu` has *every* state as a hypothesis, i.e. it is equivalent to the
box theorem itself (see `Chain.lean`).  Together with the counterexample of `Correction.lean`
this pins the satisfiability boundary of the round-4/5 list. -/
theorem aprioriNPlusNeu_trivialWindow (v : ℝ³ → ℝ) (h : ScatSol v) (J ε₀ : ℝ) :
    AprioriNPlusNeu v h J (fun N _ => (N : ℝ)) ε₀ := by
  intro L hL N _hN Φ _hlow
  exact cnPlus_le_N_mul_aboxSq (lt_of_lt_of_le one_pos hL) Φ

end Work.UBBInputs6
