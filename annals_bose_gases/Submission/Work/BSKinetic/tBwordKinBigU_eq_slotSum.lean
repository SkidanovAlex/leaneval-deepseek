import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.Defs
import Submission.Work.BSKinetic.peel_tBamp_gen
import Submission.Work.BSKinetic.swap_p_abox_tBamp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BSKinetic.tBwordKinBigU_eq_slotSum`

The `N`-body big-box family kinetic word `Work.UBBInputs9.tBwordKinBigU N ℓ c u Φ`
(`tBwordKinInd` at the moving box `Λ(u) = bigBox ℓ u`, window `chiBig ℓ u`, volume `ℓ³`,
symbol `fsKinCoeff c`) is the **slot sum of one-body forms**: for `N = n + 1` particles,

    `tBwordKinBigU (n+1) ℓ c u Φ
       = Σ_{i : Fin (n+1)} ∫_{r ∈ abox n ℓ}
           bsOneBody ℓ (fsKinCoeff c) u (z ↦ Φ (kcInsN n i (z, r)))`.

The three steps are the ones of `bigKinU_one_eq_oneBody` (the `N = 1` case), slot by slot:

* the indicator in FS's `boxQInd` is invisible to the windowed amplitude, because the moving
  window `chiBig ℓ u` is supported in the moving box (`Work.UBBInputs9.A.tBdiagFormInd_eq_tBdiagForm`);
* the `i`-th slot of the ambient integral over `abox (n+1) ℓ` is peeled off
  (`peel_tBamp_gen`), the peeled slot contributing exactly `ℓ³`, which cancels the `(ℓ³)⁻¹`;
  the remaining amplitude is the `p`-convention Fourier transform of the windowed inserted
  fibre `z ↦ chiBig ℓ u z · boxQ … (kcInsN n i (z,r))`;
* the box mean of the moving box `bigBox ℓ u` is the `bsMean` of the fibre over the centred
  cube `acube ℓ` (`boxQ_kcInsN_eq_bsQ`, pure translation invariance of Lebesgue measure), and
  the `p`- and `r`-integrals are interchanged (`swap_p_abox_tBamp`).
-/

noncomputable section
open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BSKinetic

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ## 1  The moving box and its window -/

/-- The moving window `chiBig ℓ u` *is* the `bsWin ℓ u` of this chapter: both are
`chiScale ℓ (· − ℓ • u)`. -/
lemma chiBig_eq_bsWin (ℓ : ℝ) (u : ℝ³) :
    Work.UBBInputs9.chiBig ℓ u = Work.BSKinetic.bsWin ℓ u := rfl

/-- The moving window `chiBig ℓ u` vanishes off the moving box `bigBox ℓ u`. -/
lemma chiBig_eq_zero_of_not_mem {ℓ : ℝ} (hℓ : 0 < ℓ) (u z : ℝ³)
    (hz : z ∉ Work.UBBInputs9.bigBox ℓ u) : Work.UBBInputs9.chiBig ℓ u z = 0 := by
  by_contra h
  exact hz (Submission.BoseGases.chiScale_mem_acube hℓ h)

/-- The moving box `bigBox ℓ u = ℓ • u + acube ℓ` is compact. -/
private lemma isCompact_bigBox {ℓ : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) :
    IsCompact (Work.UBBInputs9.bigBox ℓ u) := by
  have h : Work.UBBInputs9.bigBox ℓ u
      = (fun w : ℝ³ => w + ℓ • u) '' Submission.BoseGases.acube ℓ := by
    ext x
    constructor
    · intro hx
      exact ⟨x - ℓ • u, hx, by abel⟩
    · rintro ⟨w, hw, rfl⟩
      show w + ℓ • u - ℓ • u ∈ Submission.BoseGases.acube ℓ
      simpa only [add_sub_cancel_right] using hw
  rw [h]
  exact (Submission.BoseGases.acube_compact hℓ).image (continuous_id.add continuous_const)

/-- The moving window is continuous. -/
lemma continuous_chiBig {ℓ : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) :
    Continuous (Work.UBBInputs9.chiBig ℓ u) := by
  have h : Work.UBBInputs9.chiBig ℓ u
      = fun x : ℝ³ => Submission.BoseGases.chiScale ℓ (x - ℓ • u) := rfl
  rw [h]
  exact (Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).continuous.comp
    (continuous_id.sub continuous_const)

/-- **Translation of the moving-box integral to the centred cube**:
`∫_{bigBox ℓ u} ψ = ∫_{acube ℓ} ψ(ℓ • u + ·)`. -/
lemma setIntegral_bigBox_eq_add (ℓ : ℝ) (u : ℝ³) (ψ : ℝ³ → ℝ) :
    ∫ z in Work.UBBInputs9.bigBox ℓ u, ψ z
      = ∫ z in Submission.BoseGases.acube ℓ, ψ (ℓ • u + z) := by
  classical
  have hmeasB : MeasurableSet (Work.UBBInputs9.bigBox ℓ u) := by
    have h : Work.UBBInputs9.bigBox ℓ u
        = (fun x : ℝ³ => x - ℓ • u) ⁻¹' Submission.BoseGases.acube ℓ := rfl
    rw [h]
    exact (Submission.BoseGases.acube_measurable ℓ).preimage (by fun_prop)
  rw [← integral_indicator hmeasB,
      ← integral_indicator (Submission.BoseGases.acube_measurable ℓ)]
  rw [← Submission.BoseGases.integral_comp_add_left
        ((Work.UBBInputs9.bigBox ℓ u).indicator ψ) (ℓ • u)]
  apply integral_congr_ae
  filter_upwards with z
  rw [Set.indicator_apply, Set.indicator_apply]
  by_cases hz : z ∈ Submission.BoseGases.acube ℓ
  · have hz' : ℓ • u + z ∈ Work.UBBInputs9.bigBox ℓ u := by
      show ℓ • u + z - ℓ • u ∈ Submission.BoseGases.acube ℓ
      rwa [add_sub_cancel_left]
    rw [if_pos hz', if_pos hz]
  · have hz' : ℓ • u + z ∉ Work.UBBInputs9.bigBox ℓ u := by
      show ¬ (ℓ • u + z - ℓ • u ∈ Submission.BoseGases.acube ℓ)
      rwa [add_sub_cancel_left]
    rw [if_neg hz', if_neg hz]

/-! ## 2  The box mean at the moving box is the fibre mean over the centred cube -/

/-- **The moving-box projection on the inserted configuration.**  At the configuration
`kcInsN n i (z,r)` the mean-free projection `boxQ (ℓ³) (bigBox ℓ u) i Φ` is `bsQ ℓ u` applied
to the inserted fibre `z' ↦ Φ (kcInsN n i (z',r))`; the box mean over `bigBox ℓ u` is the mean
over `acube ℓ` of the shifted fibre (`setIntegral_bigBox_eq_add`). -/
lemma boxQ_kcInsN_eq_bsQ {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (u : ℝ³)
    (Φ : X (n + 1) → ℝ) (i : Fin (n + 1)) (z : ℝ³) (r : X n) :
    Work.SmallBoxTBWord.boxQ (ℓ ^ 3) (Work.UBBInputs9.bigBox ℓ u) i Φ
        (Submission.BoseGases.kcInsN n i (z, r))
      = Work.BSKinetic.bsQ ℓ u (fun z' : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (z', r))) z := by
  simp only [Work.SmallBoxTBWord.boxQ, Work.SmallBoxTBWord.boxP, Work.BSKinetic.bsQ,
    Work.BSKinetic.bsMean]
  have hI : (∫ a in Work.UBBInputs9.bigBox ℓ u,
        Φ (Function.update (Submission.BoseGases.kcInsN n i (z, r)) i a))
      = ∫ a in Work.UBBInputs9.bigBox ℓ u,
          Φ (Submission.BoseGases.kcInsN n i (a, r)) := by
    apply integral_congr_ae
    filter_upwards with a
    rw [Work.SmallBoxBridge.Fourier.update_kcInsN]
  rw [hI, setIntegral_bigBox_eq_add ℓ u
    (fun z' : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (z', r)))]
  ring

/-! ## 3  The pointwise amplitude identity -/

/-- **The windowed amplitude of the `boxQ`-projected state at the inserted configuration is the
`kinFT` of the windowed mean-free inserted fibre.**  This is the `N`-body generalisation of
`tBamp_boxQInd_N1`: the amplitude only sees the `i`-slot values of its argument
(`tBamp_kcInsN_eq_kinFT`), where the window is `chiBig ℓ u = bsWin ℓ u` and the projection is
`bsQ ℓ u` (`boxQ_kcInsN_eq_bsQ`). -/
lemma tBamp_chiBig_boxQ_eq {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (u : ℝ³)
    (Φ : X (n + 1) → ℝ) (i : Fin (n + 1)) (r : X n) (p : ℝ³) :
    Work.SmallBoxTBWord.tBamp (Work.UBBInputs9.chiBig ℓ u) p
        (Work.SmallBoxTBWord.boxQ (ℓ ^ 3) (Work.UBBInputs9.bigBox ℓ u) i Φ) i
        (Submission.BoseGases.kcInsN n i (0, r))
      = kinFT (fun z : ℝ³ => (Work.BSKinetic.bsWin ℓ u z : ℂ) *
            (Work.BSKinetic.bsQ ℓ u
              (fun z' : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (z', r))) z : ℂ)) p := by
  rw [Work.SmallBoxTBWord.tBamp_kcInsN_eq_kinFT]
  congr 1
  funext z
  rw [chiBig_eq_bsWin, boxQ_kcInsN_eq_bsQ hℓ u Φ i z r]

/-! ## 4  The per-slot identity -/

/-- **The `i`-th slot of the big-box family word is the `i`-th one-body slot sum.**  This is the
body of the main theorem, for a single slot: peel the `i`-th coordinate
(`peel_tBamp_gen`), rewrite the amplitude (`tBamp_chiBig_boxQ_eq`) and interchange the
`p`- and `r`-integrals (`swap_p_abox_tBamp`). -/
lemma slot_step {ℓ c : ℝ} (hℓ : 0 < ℓ) (n : ℕ) (u : ℝ³)
    (Φ : X (n + 1) → ℝ) (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin (n + 1)) :
    (((2 * Real.pi) ^ 3)⁻¹) * (∫ p : ℝ³, fsKinCoeff c ‖p‖ *
        ((ℓ ^ 3)⁻¹ * ∫ x in abox (n + 1) ℓ,
          ‖Work.SmallBoxTBWord.tBamp (Work.UBBInputs9.chiBig ℓ u) p
            (Work.SmallBoxTBWord.boxQ (ℓ ^ 3) (Work.UBBInputs9.bigBox ℓ u) i Φ) i x‖ ^ 2))
      = ∫ r in abox n ℓ, bsOneBody ℓ (fsKinCoeff c) u
          (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (z, r))) := by
  have hΦ' : ContDiff ℝ (⊤ : ENat)
      (Work.SmallBoxTBWord.boxQ (ℓ ^ 3) (Work.UBBInputs9.bigBox ℓ u) i Φ) :=
    Work.SmallBoxTBWord.boxQ_contDiff_of_compact (isCompact_bigBox hℓ u) (ℓ ^ 3) i hΦ
  have hpeel : ∀ p : ℝ³,
      (ℓ ^ 3)⁻¹ * ∫ x in abox (n + 1) ℓ,
          ‖Work.SmallBoxTBWord.tBamp (Work.UBBInputs9.chiBig ℓ u) p
            (Work.SmallBoxTBWord.boxQ (ℓ ^ 3) (Work.UBBInputs9.bigBox ℓ u) i Φ) i x‖ ^ 2
        = ∫ r in abox n ℓ,
            ‖kinFT (fun z : ℝ³ => (Work.UBBInputs9.chiBig ℓ u z : ℂ) *
              (Work.SmallBoxTBWord.boxQ (ℓ ^ 3) (Work.UBBInputs9.bigBox ℓ u) i Φ
                (Submission.BoseGases.kcInsN n i (z, r)) : ℂ)) p‖ ^ 2 :=
    fun p => peel_tBamp_gen hℓ (isCompact_bigBox hℓ u) (continuous_chiBig hℓ u)
      (fun z hz => chiBig_eq_zero_of_not_mem hℓ u z hz) hΦ'.continuous i p
  calc (((2 * Real.pi) ^ 3)⁻¹) * (∫ p : ℝ³, fsKinCoeff c ‖p‖ *
        ((ℓ ^ 3)⁻¹ * ∫ x in abox (n + 1) ℓ,
          ‖Work.SmallBoxTBWord.tBamp (Work.UBBInputs9.chiBig ℓ u) p
            (Work.SmallBoxTBWord.boxQ (ℓ ^ 3) (Work.UBBInputs9.bigBox ℓ u) i Φ) i x‖ ^ 2))
      = (((2 * Real.pi) ^ 3)⁻¹) * (∫ p : ℝ³, fsKinCoeff c ‖p‖ *
          (∫ r in abox n ℓ,
            ‖kinFT (fun z : ℝ³ => (Work.UBBInputs9.chiBig ℓ u z : ℂ) *
              (Work.SmallBoxTBWord.boxQ (ℓ ^ 3) (Work.UBBInputs9.bigBox ℓ u) i Φ
                (Submission.BoseGases.kcInsN n i (z, r)) : ℂ)) p‖ ^ 2)) := by
        congr 1
        apply integral_congr_ae
        filter_upwards with p
        rw [hpeel p]
    _ = (((2 * Real.pi) ^ 3)⁻¹) * (∫ p : ℝ³, fsKinCoeff c ‖p‖ *
          (∫ r in abox n ℓ,
            ‖Work.SmallBoxTBWord.tBamp (Work.UBBInputs9.chiBig ℓ u) p
              (Work.SmallBoxTBWord.boxQ (ℓ ^ 3) (Work.UBBInputs9.bigBox ℓ u) i Φ) i
              (Submission.BoseGases.kcInsN n i (0, r))‖ ^ 2)) := by
        congr 1
        apply integral_congr_ae
        filter_upwards with p
        congr 1
        apply integral_congr_ae
        filter_upwards with r
        rw [Work.SmallBoxTBWord.tBamp_kcInsN_eq_kinFT]
    _ = ∫ r in abox n ℓ, (((2 * Real.pi) ^ 3)⁻¹) * ∫ p : ℝ³, fsKinCoeff c ‖p‖ *
          ‖Work.SmallBoxTBWord.tBamp (Work.UBBInputs9.chiBig ℓ u) p
            (Work.SmallBoxTBWord.boxQ (ℓ ^ 3) (Work.UBBInputs9.bigBox ℓ u) i Φ) i
            (Submission.BoseGases.kcInsN n i (0, r))‖ ^ 2 :=
        swap_p_abox_tBamp hℓ u Φ hΦ i
    _ = ∫ r in abox n ℓ, bsOneBody ℓ (fsKinCoeff c) u
          (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (z, r))) := by
        apply integral_congr_ae
        filter_upwards with r
        rw [Work.BSKinetic.bsOneBody]
        congr 1
        apply integral_congr_ae
        filter_upwards with p
        rw [tBamp_chiBig_boxQ_eq hℓ u Φ i r p]

/-! ## 5  The main theorem -/

theorem tBwordKinBigU_eq_slotSum {ℓ c : ℝ} (hℓ : 0 < ℓ) (n : ℕ)
    (u : EuclideanSpace ℝ (Fin 3)) (Φ : Submission.BoseGases.X (n + 1) → ℝ)
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) :
    Work.UBBInputs9.tBwordKinBigU (n + 1) ℓ c u Φ
      = ∑ i : Fin (n + 1), ∫ r in Submission.BoseGases.abox n ℓ,
          Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff c) u
            (fun z : EuclideanSpace ℝ (Fin 3) =>
              Φ (Submission.BoseGases.kcInsN n i (z, r))) := by
  rw [Work.UBBInputs9.tBwordKinBigU, Work.UBBInputs8.tBwordKinInd,
    Work.UBBInputs9.A.tBdiagFormInd_eq_tBdiagForm (fsKinCoeff c) Φ
      (fun z hz => chiBig_eq_zero_of_not_mem hℓ u z hz)]
  rw [Work.SmallBoxTBWord.tBdiagForm]
  apply Finset.sum_congr rfl
  intro i _
  exact slot_step hℓ n u Φ hΦ i

end Work.BSKinetic
