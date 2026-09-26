import Mathlib
import Submission.Work.Drive.sweepProfileInjOnNT
import Submission.Work.Drive.chamferChordThin
import Submission.Work.Drive.noChamferCrossingWindowNtHead
import Submission.Work.Drive.no_chamfer_crossing_window
import Submission.Work.Drive.chordSweepSmooth
import Submission.Work.Drive.chordSweepDefs
import Submission.Work.Drive.sweepLoop_injective
import Submission.Work.Drive.sweepLoopProfileDefs

/-!
# `E1` of the `OFat` endgame: the chamfered sweep loop is a knot

The band arc of the `OFat` lane (`Work.Drive.StripCrosscutAvoidingOFat`) has chords that may carry
*corner-local* middles (within `ρ` of an endpoint, `Work.Drive.OFatR`-avoidance) but are *not*
tangent at either endpoint (`Work.Drive.TCset`-avoidance).  This module proves that the chamfered
sweep loop `Work.Drive.sweepLoopChamfer r D lam σ` of such an arc is injective on one period for all
small enough `lam`, provided the chamfer is deeper than the fatness threshold (`ρ ≤ lam * w`):
the *retained* arc `[ta + lam·w, tb − lam·w]` is then chord-free (`hac`), the two chamfer/arc
crossings are excluded by the non-tangency (`no_chamfer_crossing_window_nt` and its head mirror),
the two chamfer/chord crossings by the same first-order estimate (`no_chamfer_chord_crossing_*`),
and the two chamfers are separated by the non-degeneracy of the chord.

The point-set assembly is `Work.Drive.sweepLoopProfile_injOn_of_separation_nt`
(`Drive/sweepProfileInjOnNT.lean`, the `retained-arc` weakening of the proved
`Work.Drive.sweepLoopProfile_injOn_of_separation`).
-/

noncomputable section

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology

/-! ## Converters between the clamped and the `I`-indexed vocabulary -/

private lemma nt_clampI_coe (s : Set.Icc (0 : ℝ) 1) : clampI (s : ℝ) = s := by
  apply Subtype.ext
  show min 1 (max 0 (s : ℝ)) = (s : ℝ)
  rw [max_eq_right s.2.1, min_eq_right s.2.2]

private lemma nt_taR_coe {d : BandArcData} (D : SweepData d) (s : Set.Icc (0 : ℝ) 1) :
    taR D (s : ℝ) = D.ta s := by simp [taR, nt_clampI_coe]

private lemma nt_tbR_coe {d : BandArcData} (D : SweepData d) (s : Set.Icc (0 : ℝ) 1) :
    tbR D (s : ℝ) = D.tb s := by simp [tbR, nt_clampI_coe]

private lemma nt_sweepW'_coe {d : BandArcData} (D : SweepData d) (s : Set.Icc (0 : ℝ) 1) :
    sweepW' D (s : ℝ) = sweepW D s := by simp [sweepW', sweepW, nt_taR_coe, nt_tbR_coe]

private lemma nt_sweepArc'_coe (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (s : Set.Icc (0 : ℝ) 1)
    (ξ : ℝ) : sweepArc' r D (s : ℝ) ξ = sweepArc r D s ξ := by
  simp [sweepArc', sweepArc, nt_taR_coe, nt_sweepW'_coe]

private lemma nt_sweepChord'_coe (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (s : Set.Icc (0 : ℝ) 1)
    (ξ : ℝ) : sweepChord' r D (s : ℝ) ξ = sweepChord r D s ξ := by
  simp [sweepChord', sweepChord, nt_taR_coe, nt_tbR_coe]

private lemma continuous_clampI_nt : Continuous clampI := by
  unfold clampI
  fun_prop

private lemma continuous_taR_nt {d : BandArcData} (D : SweepData d) :
    Continuous (taR D) := D.cont_ta.comp continuous_clampI_nt

private lemma continuous_tbR_nt {d : BandArcData} (D : SweepData d) :
    Continuous (tbR D) := D.cont_tb.comp continuous_clampI_nt

/-- **From the profile loop to the chamfered loop** (the `period`-cell bookkeeping). -/
private lemma chamfer_injOn_of_profile_nt {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) {s : ℝ}
    (hprof : Set.InjOn (sweepLoopProfile r D lam s) (Set.Ico (0 : ℝ) 1)) :
    Set.InjOn (sweepLoopChamfer r D lam s) (Set.Ico 0 period) := by
  intro t₁ ht₁ t₂ ht₂ h
  have hm₁ := sweepParam_mem t₁
  have hm₂ := sweepParam_mem t₂
  rw [sweepLoopChamfer_eq_profile r D h0 h1, sweepLoopChamfer_eq_profile r D h0 h1] at h
  have hpar : sweepParam t₁ = sweepParam t₂ :=
    hprof ⟨hm₁.1, hm₁.2⟩ ⟨hm₂.1, hm₂.2⟩ h
  rw [sweepParam_eq_div ht₁, sweepParam_eq_div ht₂] at hpar
  have h3 : t₁ / period * period = t₂ / period * period := by rw [hpar]
  rwa [div_mul_cancel₀ t₁ period_ne_zero, div_mul_cancel₀ t₂ period_ne_zero] at h3

/-! ## The tilt margin at the second endpoint -/

private lemma exists_tilt_margin_b {r : ℝ → Space} (hr : IsSmoothKnot r) (ta tb : ℝ → ℝ)
    (hta : Continuous ta) (htb : Continuous tb) {a b : ℝ} (hab : a ≤ b)
    (hpos : ∀ s ∈ Set.Icc a b, 0 < tb s - ta s ∧ tb s - ta s < period)
    (hnt : ∀ s ∈ Set.Icc a b, ∀ m : ℝ, r (tb s) - r (ta s) ≠ m • velocity r (tb s)) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ s ∈ Set.Icc a b,
      μ ≤ ‖chordTilt (r (ta s)) (r (tb s)) (velocity r (tb s))‖ := by
  have hrc : Continuous r := hr.continuous
  have hvc : Continuous (velocity r) := hr.smooth.continuous_deriv (by simp)
  have hAB : ∀ s ∈ Set.Icc a b, r (ta s) ≠ r (tb s) := fun s hs =>
    knot_ne_of_sub_mem_Ioo hr (hpos s hs).1 (hpos s hs).2
  have hdel : ContinuousOn (fun s => r (tb s) - r (ta s)) (Set.Icc a b) :=
    ((hrc.comp htb).sub (hrc.comp hta)).continuousOn
  have hnorm : ContinuousOn (fun s => ‖r (tb s) - r (ta s)‖) (Set.Icc a b) := hdel.norm
  have hinv : ContinuousOn (fun s => (‖r (tb s) - r (ta s)‖)⁻¹) (Set.Icc a b) :=
    hnorm.inv₀ (fun s hs => norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm (hAB s hs))))
  have hcd : ContinuousOn (fun s => chordDir (r (ta s)) (r (tb s))) (Set.Icc a b) := by
    show ContinuousOn (fun s => (‖r (tb s) - r (ta s)‖)⁻¹ • (r (tb s) - r (ta s))) (Set.Icc a b)
    exact hinv.smul hdel
  have hv : ContinuousOn (fun s => velocity r (tb s)) (Set.Icc a b) := (hvc.comp htb).continuousOn
  have hinner : ContinuousOn
      (fun s => inner ℝ (velocity r (tb s)) (chordDir (r (ta s)) (r (tb s)))) (Set.Icc a b) :=
    hv.inner hcd
  have htilt : ContinuousOn
      (fun s => chordTilt (r (ta s)) (r (tb s)) (velocity r (tb s))) (Set.Icc a b) := by
    show ContinuousOn (fun s => velocity r (tb s)
      - inner ℝ (velocity r (tb s)) (chordDir (r (ta s)) (r (tb s)))
        • chordDir (r (ta s)) (r (tb s))) (Set.Icc a b)
    exact hv.sub (hinner.smul hcd)
  have hF : ContinuousOn
      (fun s => ‖chordTilt (r (ta s)) (r (tb s)) (velocity r (tb s))‖) (Set.Icc a b) :=
    htilt.norm
  obtain ⟨s₀, hs₀, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨a, le_rfl, hab⟩ hF
  refine ⟨‖chordTilt (r (ta s₀)) (r (tb s₀)) (velocity r (tb s₀))‖, ?_, fun s hs => hmin hs⟩
  exact norm_pos_iff.mpr
    (chordTilt_ne_zero_of_not_smul (hAB s₀ hs₀) (hr.regular (tb s₀)) (hnt s₀ hs₀))

/-! ## The main theorem -/

/-- **`E1` of the `OFat` endgame.**  On a compact window `[a,b] ⊂ (0,1)` of sweep parameters, on
the non-tangent band arc of the `OFat` lane whose retained arc carries no middle at distance `≥ ρ`
from an endpoint, the chamfered sweep loop is injective on one period for all small enough `lam`,
as soon as the cut depth `lam * w` is at least `ρ`. -/
theorem chamferLoop_injOn_nt {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d) {a b ρ : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) (hρ : 0 ≤ ρ)
    (hV : ∀ σ ∈ Set.Icc a b, r (taR D σ) ≠ r (tbR D σ))
    (hntA : ∀ σ ∈ Set.Icc a b, ∀ m : ℝ,
      r (tbR D σ) - r (taR D σ) ≠ m • velocity r (taR D σ))
    (hntB : ∀ σ ∈ Set.Icc a b, ∀ m : ℝ,
      r (tbR D σ) - r (taR D σ) ≠ m • velocity r (tbR D σ))
    (hnoFat : ∀ σ ∈ Set.Icc a b, ∀ u : ℝ, taR D σ + ρ ≤ u → u ≤ tbR D σ - ρ →
      r u ∉ openSegment ℝ (r (taR D σ)) (r (tbR D σ))) :
    ∃ L : ℝ, 0 < L ∧ L ≤ 1 / 4 ∧ ∀ lam : ℝ, 0 < lam → lam ≤ L →
      ∀ σ ∈ Set.Icc a b, ρ ≤ lam * sweepW' D σ →
        Set.InjOn (sweepLoopChamfer r D lam σ) (Set.Ico 0 period) := by
  classical
  have hp : 0 < period := period_pos
  have hposab : ∀ σ ∈ Set.Icc a b, 0 < tbR D σ - taR D σ ∧ tbR D σ - taR D σ < period := by
    intro σ hσ
    have hσI : σ ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨lt_of_lt_of_le ha hσ.1, lt_of_le_of_lt hσ.2 hb⟩
    obtain ⟨h1, h2⟩ := sweepW_pos_lt D ⟨σ, ⟨hσI.1.le, hσI.2.le⟩⟩ hσI
    have hcl : clampI σ = (⟨σ, ⟨hσI.1.le, hσI.2.le⟩⟩ : Set.Icc (0 : ℝ) 1) :=
      nt_clampI_coe ⟨σ, ⟨hσI.1.le, hσI.2.le⟩⟩
    have hw : tbR D σ - taR D σ = sweepW D ⟨σ, ⟨hσI.1.le, hσI.2.le⟩⟩ := by
      simp only [sweepW', tbR, taR, hcl, sweepW]
    rw [hw]
    exact ⟨h1, h2⟩
  -- the two arc/chamfer crossing theorems
  obtain ⟨LtailC, hLtailC, htailC⟩ :=
    no_chamfer_crossing_window_nt hr (taR D) (tbR D) (continuous_taR_nt D) (continuous_tbR_nt D)
      ha hab hb hposab hntA hntB
  obtain ⟨LheadC, hLheadC, hheadC⟩ :=
    no_chamfer_crossing_window_nt_head hr (taR D) (tbR D) (continuous_taR_nt D) (continuous_tbR_nt D)
      ha hab hb hposab hntA hntB
  -- the two tilt margins
  obtain ⟨μa, hμa, hμa'⟩ :=
    exists_tilt_margin hr (taR D) (tbR D) (continuous_taR_nt D) (continuous_tbR_nt D) hab.le
      hposab hntA
  obtain ⟨μb, hμb, hμb'⟩ :=
    exists_tilt_margin_b hr (taR D) (tbR D) (continuous_taR_nt D) (continuous_tbR_nt D) hab.le
      hposab hntB
  -- the two chamfer/chord crossing theorems
  obtain ⟨Kca, hKca, hca⟩ := no_chamfer_chord_crossing_tail hr
  obtain ⟨Kcb, hKcb, hcb⟩ := no_chamfer_chord_crossing_head hr
  -- a Lipschitz constant and a lower bound for the chord length on the window
  obtain ⟨M, hMpos, hlip⟩ := exists_curve_lipschitz hr
  have hcontL : ContinuousOn (fun σ : ℝ => ‖r (tbR D σ) - r (taR D σ)‖) (Set.Icc a b) :=
    (((hr.continuous.comp (continuous_tbR_nt D)).sub
      (hr.continuous.comp (continuous_taR_nt D))).norm).continuousOn
  have hposL : ∀ σ ∈ Set.Icc a b, 0 < ‖r (tbR D σ) - r (taR D σ)‖ := by
    intro σ hσ
    refine norm_pos_iff.mpr (sub_ne_zero.mpr ?_)
    exact (hV σ hσ).symm
  obtain ⟨σL, hσLmem, hLmin⟩ := isCompact_Icc.exists_isMinOn ⟨a, le_rfl, hab.le⟩ hcontL
  have hσL : 0 < ‖r (tbR D σL) - r (taR D σL)‖ := hposL σL hσLmem
  -- the constants
  have hμaK : 0 < μa / (4 * (Kca * period)) := by positivity
  have hμbK : 0 < μb / (4 * (Kcb * period)) := by positivity
  have hden : 0 < 8 * M * period := by positivity
  set Lc : ℝ := min (min (min LtailC LheadC) (min (μa / (4 * (Kca * period)))
      (μb / (4 * (Kcb * period)))))
      (min (1 / 4) (‖r (tbR D σL) - r (taR D σL)‖ / (8 * M * period))) with hLcdef
  have hLcpos : 0 < Lc := by
    rw [hLcdef]
    exact lt_min (lt_min (lt_min hLtailC hLheadC) (lt_min hμaK hμbK))
      (lt_min (by norm_num) (div_pos hσL hden))
  refine ⟨Lc, hLcpos, ?_, ?_⟩
  · -- `L ≤ 1/4`
    rw [hLcdef]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  · intro lam hlam hle σ hσ hρl
    have hle' : lam ≤ min (min (min LtailC LheadC) (min (μa / (4 * (Kca * period)))
        (μb / (4 * (Kcb * period)))))
        (min (1 / 4) (‖r (tbR D σL) - r (taR D σL)‖ / (8 * M * period))) := by
      rw [← hLcdef]; exact hle
    -- the slice data
    have hσ0 : a ≤ σ := hσ.1
    have hσ1 : σ ≤ b := hσ.2
    have hσI : σ ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨lt_of_lt_of_le ha hσ0, lt_of_le_of_lt hσ1 hb⟩
    set s : Set.Icc (0 : ℝ) 1 := ⟨σ, ⟨hσI.1.le, hσI.2.le⟩⟩ with hs
    have hcl : clampI σ = s := nt_clampI_coe s
    have hsR : (s : ℝ) = σ := rfl
    obtain ⟨hW0, hWT⟩ := sweepW_pos_lt D s (by rw [hsR]; exact hσI)
    have hw : sweepW' D σ = sweepW D s := by
      simp only [sweepW', tbR, taR, hcl, sweepW, hs]
    have hwEq : sweepW' D σ = tbR D σ - taR D σ := rfl
    have hwpos : 0 < sweepW' D σ := by rw [hw]; exact hW0
    have hwper : sweepW' D σ < period := by rw [hw]; exact hWT
    have hlamL₁ : lam ≤ LtailC :=
      le_trans hle' (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
    have hlamL₂ : lam ≤ LheadC :=
      le_trans hle' (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
    have hlamμa : lam ≤ μa / (4 * (Kca * period)) :=
      le_trans hle' (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
    have hlamμb : lam ≤ μb / (4 * (Kcb * period)) :=
      le_trans hle' (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
    have hlam14 : lam ≤ 1 / 4 :=
      le_trans hle' (le_trans (min_le_right _ _) (min_le_left _ _))
    have hlamch : lam ≤ ‖r (tbR D σL) - r (taR D σL)‖ / (8 * M * period) :=
      le_trans hle' (le_trans (min_le_right _ _) (min_le_right _ _))
    -- the retained window of the arc
    have key1 : ∀ ξ ∈ Set.Icc lam (1 - lam),
        taR D σ + ρ ≤ taR D σ + ξ * sweepW' D σ ∧
        taR D σ + ξ * sweepW' D σ ≤ tbR D σ - ρ := by
      intro ξ hξ
      have ha : lam * sweepW' D σ ≤ ξ * sweepW' D σ :=
        mul_le_mul_of_nonneg_right hξ.1 hwpos.le
      have hb : ξ * sweepW' D σ ≤ (1 - lam) * sweepW' D σ :=
        mul_le_mul_of_nonneg_right hξ.2 hwpos.le
      have hc : (1 - lam) * sweepW' D σ = sweepW' D σ - lam * sweepW' D σ := by ring
      rw [hwEq] at hρl ha hb hc ⊢
      exact ⟨by linarith [hρl, ha], by linarith [hb, hc, hρl]⟩
    -- the retained arc is chord-free
    have hac : ∀ ξ ∈ Set.Icc lam (1 - lam), ∀ ξ' ∈ Set.Ioo (0 : ℝ) 1,
        sweepArc' r D σ ξ ≠ sweepChord' r D σ ξ' := by
      intro ξ hξ ξ' hξ' heq
      obtain ⟨h1, h2⟩ := key1 ξ hξ
      have hmem : sweepArc' r D σ ξ ∈ openSegment ℝ (r (taR D σ)) (r (tbR D σ)) := by
        rw [heq, sweepChord', openSegment_eq_image ℝ]
        exact ⟨ξ', hξ', rfl⟩
      exact hnoFat σ hσ (taR D σ + ξ * sweepW' D σ) h1 h2 hmem
    -- the arc and the chord are injective on `[0,1]`
    have harc : Set.InjOn (sweepArc' r D σ) (Set.Icc (0 : ℝ) 1) := by
      intro ξ hξ ξ' hξ' h
      have h' : sweepArc r D s ξ = sweepArc r D s ξ' := by
        rw [← nt_sweepArc'_coe r D s ξ, ← nt_sweepArc'_coe r D s ξ', hsR]
        exact h
      exact sweepArc_injOn_Icc hr D s hW0 hWT hξ hξ' h'
    have hAB : r (D.ta s) ≠ r (D.tb s) :=
      sweepChord_endpoints_ne hr D (by rw [hsR]; exact hσI.1.ne') (by rw [hsR]; exact hσI.2.ne)
    have hchord : Set.InjOn (sweepChord' r D σ) (Set.Icc (0 : ℝ) 1) := by
      intro ξ hξ ξ' hξ' h
      have h' : sweepChord r D s ξ = sweepChord r D s ξ' := by
        rw [← nt_sweepChord'_coe r D s ξ, ← nt_sweepChord'_coe r D s ξ', hsR]
        exact h
      exact sweepChord_injOn_Icc r D s hAB hξ hξ' h'
    have hlam_ioo : lam ∈ Set.Ioo (0 : ℝ) 1 := ⟨hlam, by linarith⟩
    -- the tail chamfer meets the arc only at its own endpoint
    have harc_tail : ∀ c ∈ Set.Icc (0 : ℝ) 1, ∀ ξ ∈ Set.Icc lam (1 - lam),
        (1 - c) • sweepChord' r D σ lam + c • sweepArc' r D σ lam = sweepArc' r D σ ξ →
          ξ = lam := by
      intro c hc ξ hξ heq
      rcases lt_or_ge c 1 with hclt | hcge
      · rcases eq_or_lt_of_le hc.1 with hc0 | hc0
        · -- `c = 0`: the chord point is an arc point, impossible by the chord-freeness
          subst hc0
          simp only [sub_zero, one_smul, zero_smul, add_zero] at heq
          exact absurd heq.symm (hac ξ hξ lam hlam_ioo)
        · -- `0 < c < 1`: the thin-crossing theorem
          obtain ⟨h1, h2⟩ := key1 ξ hξ
          have h1tr : taR D σ + lam * (tbR D σ - taR D σ) ≤ taR D σ + ξ * sweepW' D σ := by
            have ha : lam * sweepW' D σ ≤ ξ * sweepW' D σ :=
              mul_le_mul_of_nonneg_right hξ.1 hwpos.le
            rw [hwEq] at ha ⊢
            linarith [ha]
          have h2b : taR D σ + ξ * sweepW' D σ ≤ tbR D σ := by linarith [h2, hρ]
          have hceq : (1 - c) • ((1 - lam) • r (taR D σ) + lam • r (tbR D σ))
              + c • r (taR D σ + lam * sweepW' D σ)
              = r (taR D σ + ξ * sweepW' D σ) := by
            have h1' : sweepChord' r D σ lam = (1 - lam) • r (taR D σ) + lam • r (tbR D σ) :=
              rfl
            have h2' : sweepArc' r D σ lam = r (taR D σ + lam * sweepW' D σ) := rfl
            have h3' : sweepArc' r D σ ξ = r (taR D σ + ξ * sweepW' D σ) := rfl
            rw [h1', h2', h3'] at heq
            exact heq
          have hcross := htailC lam (taR D σ + ξ * sweepW' D σ) c hlam hlamL₁ hc0 hclt σ hσ
            h1tr h2b hceq
          have h3 : ξ * (tbR D σ - taR D σ) = lam * (tbR D σ - taR D σ) := by
            have hc' := hcross
            rw [hwEq] at hc'
            linarith [hc']
          exact mul_right_cancel₀ (ne_of_gt (by rw [← hwEq]; exact hwpos)) h3
      · -- `c = 1`: the arc point equals the arc's own cut point
        have hc1 : c = 1 := le_antisymm hc.2 hcge
        subst hc1
        simp only [sub_self, zero_smul, zero_add, one_smul] at heq
        exact (harc ⟨by linarith [hlam.le], by linarith [hlam.le]⟩
          ⟨by linarith [hξ.1, hlam.le], by linarith [hξ.2, hlam.le]⟩ heq).symm
    -- the head chamfer meets the arc only at its own endpoint
    have harc_head : ∀ c ∈ Set.Icc (0 : ℝ) 1, ∀ ξ ∈ Set.Icc lam (1 - lam),
        (1 - c) • sweepArc' r D σ (1 - lam) + c • sweepChord' r D σ (1 - lam)
          = sweepArc' r D σ ξ → ξ = 1 - lam := by
      intro c hc ξ hξ heq
      rcases lt_or_ge c 1 with hclt | hcge
      · rcases eq_or_lt_of_le hc.1 with hc0 | hc0
        · -- `c = 0`: the arc's own cut point equals an arc point
          subst hc0
          simp only [sub_zero, one_smul, zero_smul, add_zero] at heq
          exact (harc ⟨by linarith [hlam.le], by linarith [hlam.le]⟩
            ⟨by linarith [hξ.1, hlam.le], by linarith [hξ.2]⟩ heq).symm
        · -- `0 < c < 1`: the head thin-crossing theorem
          obtain ⟨h1, h2⟩ := key1 ξ hξ
          have hxhi : taR D σ + ξ * sweepW' D σ ≤ tbR D σ - lam * sweepW' D σ := by
            have hb : ξ * sweepW' D σ ≤ (1 - lam) * sweepW' D σ :=
              mul_le_mul_of_nonneg_right hξ.2 hwpos.le
            have hc : (1 - lam) * sweepW' D σ = sweepW' D σ - lam * sweepW' D σ := by ring
            rw [hwEq] at hb hc ⊢
            linarith [hb, hc]
          have hxlo : taR D σ + lam * (tbR D σ - taR D σ) ≤ taR D σ + ξ * sweepW' D σ := by
            have ha : lam * sweepW' D σ ≤ ξ * sweepW' D σ :=
              mul_le_mul_of_nonneg_right hξ.1 hwpos.le
            rw [hwEq] at ha ⊢
            linarith [ha]
          have hceq : (1 - c) • r (tbR D σ - lam * sweepW' D σ)
              + c • (lam • r (taR D σ) + (1 - lam) • r (tbR D σ))
              = r (taR D σ + ξ * sweepW' D σ) := by
            have h1' : sweepArc' r D σ (1 - lam) = r (tbR D σ - lam * sweepW' D σ) := by
              rw [sweepArc']
              congr 1
              rw [hwEq]
              ring
            have h2' : sweepChord' r D σ (1 - lam)
                = lam • r (taR D σ) + (1 - lam) • r (tbR D σ) := by
              rw [sweepChord']
              rw [show (1 : ℝ) - (1 - lam) = lam by ring]
            have h3' : sweepArc' r D σ ξ = r (taR D σ + ξ * sweepW' D σ) := rfl
            rw [h1', h2', h3'] at heq
            exact heq
          have hcross := hheadC lam (taR D σ + ξ * sweepW' D σ) c hlam hlamL₂ hc0 hclt σ hσ
            hxlo hxhi hceq
          have h3 : ξ * (tbR D σ - taR D σ) = (1 - lam) * (tbR D σ - taR D σ) := by
            have hc' := hcross
            rw [hwEq] at hc'
            linarith [hc']
          exact mul_right_cancel₀ (ne_of_gt (by rw [← hwEq]; exact hwpos)) h3
      · -- `c = 1`: the chord's cut point equals an arc point, impossible by chord-freeness
        have hc1 : c = 1 := le_antisymm hc.2 hcge
        subst hc1
        simp only [sub_self, zero_smul, zero_add, one_smul] at heq
        exact absurd heq.symm
          (hac ξ ⟨by linarith [hξ.1, hlam.le], by linarith [hξ.2]⟩ (1 - lam)
            ⟨by linarith, by linarith⟩)
    -- the two chamfer/chord separations
    have hμaKlt : lam * (Kca * period) < μa := by
      have h1 : lam * (Kca * period) ≤ (μa / (4 * (Kca * period))) * (Kca * period) :=
        mul_le_mul_of_nonneg_right hlamμa (by positivity)
      have h2 : (μa / (4 * (Kca * period))) * (Kca * period) = μa / 4 := by
        field_simp
      rw [h2] at h1
      linarith
    have hμbKlt : lam * (Kcb * period) < μb := by
      have h1 : lam * (Kcb * period) ≤ (μb / (4 * (Kcb * period))) * (Kcb * period) :=
        mul_le_mul_of_nonneg_right hlamμb (by positivity)
      have h2 : (μb / (4 * (Kcb * period))) * (Kcb * period) = μb / 4 := by
        field_simp
      rw [h2] at h1
      linarith
    have hchord_tail : ∀ c ∈ Set.Icc (0 : ℝ) 1, ∀ ξ ∈ Set.Icc lam (1 - lam),
        (1 - c) • sweepChord' r D σ lam + c • sweepArc' r D σ lam = sweepChord' r D σ ξ →
          c = 0 := by
      intro c hc ξ hξ heq
      by_contra hcne
      have hc0 : 0 < c := lt_of_le_of_ne hc.1 (Ne.symm hcne)
      have h1 : (1 - c) • ((1 - lam) • r (taR D σ) + lam • r (tbR D σ))
          + c • r (taR D σ + lam * sweepW' D σ)
          = (1 - ξ) • r (taR D σ) + ξ • r (tbR D σ) := by
        have h2 : sweepChord' r D σ lam = (1 - lam) • r (taR D σ) + lam • r (tbR D σ) := by
          rfl
        have h3 : sweepArc' r D σ lam = r (taR D σ + lam * sweepW' D σ) := by
          rfl
        have h4 : sweepChord' r D σ ξ = (1 - ξ) • r (taR D σ) + ξ • r (tbR D σ) := by
          rfl
        rw [h2, h3, h4] at heq
        exact heq
      exact hca μa period hμa hp (taR D σ) (tbR D σ) lam c ξ hlam hμaKlt hwpos hwper
        (le_of_lt hwper) (hμa' σ hσ) hc0 hc.2 hξ h1
    have hchord_head : ∀ c ∈ Set.Icc (0 : ℝ) 1, ∀ ξ ∈ Set.Icc lam (1 - lam),
        (1 - c) • sweepArc' r D σ (1 - lam) + c • sweepChord' r D σ (1 - lam)
          = sweepChord' r D σ ξ → c = 1 := by
      intro c hc ξ hξ heq
      by_contra hcne
      have hclt : c < 1 := lt_of_le_of_ne hc.2 hcne
      rcases eq_or_lt_of_le hc.1 with hc0 | hc0
      · -- `c = 0`
        subst hc0
        simp only [sub_zero, one_smul, zero_smul, add_zero] at heq
        exact absurd heq (hac (1 - lam) ⟨by linarith [hlam14], le_rfl⟩ ξ
          ⟨by linarith [hξ.1, hlam.le], by linarith [hξ.2]⟩)
      · have h1 : (1 - c) • r (tbR D σ - lam * sweepW' D σ)
            + c • (lam • r (taR D σ) + (1 - lam) • r (tbR D σ))
            = (1 - ξ) • r (taR D σ) + ξ • r (tbR D σ) := by
          have h2 : sweepArc' r D σ (1 - lam) = r (tbR D σ - lam * sweepW' D σ) := by
            rw [sweepArc']
            congr 1
            rw [hwEq]
            ring
          have h3 : sweepChord' r D σ (1 - lam)
              = lam • r (taR D σ) + (1 - lam) • r (tbR D σ) := by
            rw [sweepChord']
            rw [show (1 : ℝ) - (1 - lam) = lam by ring]
          have h4 : sweepChord' r D σ ξ = (1 - ξ) • r (taR D σ) + ξ • r (tbR D σ) := by
            rfl
          rw [h2, h3, h4] at heq
          exact heq
        exact hcb μb period hμb hp (taR D σ) (tbR D σ) lam c ξ hlam hμbKlt hwpos hwper
          (le_of_lt hwper) (hμb' σ hσ) hc0 hclt hξ h1
    -- the two chamfers are separated
    have hchamfers : ∀ c ∈ Set.Icc (0 : ℝ) 1, ∀ c' ∈ Set.Icc (0 : ℝ) 1,
        (1 - c) • sweepChord' r D σ lam + c • sweepArc' r D σ lam ≠
          (1 - c') • sweepArc' r D σ (1 - lam) + c' • sweepChord' r D σ (1 - lam) := by
      intro c hc c' hc' hEq
      have hLσ : ‖r (tbR D σ) - r (taR D σ)‖ ≤ M * period := by
        have h1 := hlip (tbR D σ) (taR D σ)
        have hwpos' : 0 < tbR D σ - taR D σ := by rw [← hwEq]; exact hwpos
        rw [abs_of_pos hwpos'] at h1
        have h2 : M * (tbR D σ - taR D σ) ≤ M * period :=
          mul_le_mul_of_nonneg_left (by rw [← hwEq]; exact hwper.le) hMpos.le
        linarith [h1, h2]
      set X : Space := (1 - c) • sweepChord' r D σ lam + c • sweepArc' r D σ lam with hX
      set Y : Space := (1 - c') • sweepArc' r D σ (1 - lam) + c' • sweepChord' r D σ (1 - lam)
        with hY
      have hXY : X = Y := by rw [hX, hY]; exact hEq
      have hP : ‖X - r (taR D σ)‖ ≤ 2 * (M * period * lam) := by
        rw [hX]
        have h1 : sweepChord' r D σ lam - r (taR D σ)
            = lam • (r (tbR D σ) - r (taR D σ)) := by
          rw [sweepChord']; module
        have h2 : sweepArc' r D σ lam - r (taR D σ)
            = r (taR D σ + lam * sweepW' D σ) - r (taR D σ) := rfl
        have h3 : ‖sweepChord' r D σ lam - r (taR D σ)‖ ≤ M * period * lam := by
          rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos hlam]
          calc lam * ‖r (tbR D σ) - r (taR D σ)‖ ≤ lam * (M * period) :=
                mul_le_mul_of_nonneg_left hLσ hlam.le
            _ = M * period * lam := by ring
        have h4 : ‖sweepArc' r D σ lam - r (taR D σ)‖ ≤ M * period * lam := by
          rw [h2]
          have h5 := hlip (taR D σ + lam * sweepW' D σ) (taR D σ)
          have h6 : |taR D σ + lam * sweepW' D σ - taR D σ| = lam * sweepW' D σ := by
            rw [show taR D σ + lam * sweepW' D σ - taR D σ = lam * sweepW' D σ by ring,
              abs_of_pos (mul_pos hlam hwpos)]
          rw [h6] at h5
          have h7 : M * (lam * sweepW' D σ) ≤ M * (lam * period) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hwper.le hlam.le) hMpos.le
          have h8 : M * (lam * period) = M * period * lam := by ring
          linarith [h5, h7, h8.le, h8.ge]
        have h9 : (1 - c) • sweepChord' r D σ lam + c • sweepArc' r D σ lam - r (taR D σ)
            = (1 - c) • (sweepChord' r D σ lam - r (taR D σ))
              + c • (sweepArc' r D σ lam - r (taR D σ)) := by module
        rw [h9]
        calc ‖(1 - c) • (sweepChord' r D σ lam - r (taR D σ))
              + c • (sweepArc' r D σ lam - r (taR D σ))‖
            ≤ ‖(1 - c) • (sweepChord' r D σ lam - r (taR D σ))‖
              + ‖c • (sweepArc' r D σ lam - r (taR D σ))‖ := norm_add_le _ _
          _ ≤ (1 - c) * (M * period * lam) + c * (M * period * lam) := by
              refine add_le_add ?_ ?_
              · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hc.2)]
                exact mul_le_mul_of_nonneg_left h3 (sub_nonneg.mpr hc.2)
              · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc.1]
                exact mul_le_mul_of_nonneg_left h4 hc.1
          _ = M * period * lam := by ring
          _ ≤ 2 * (M * period * lam) := by
              have hk := mul_pos (mul_pos hMpos hp) hlam
              linarith
      have hQ : ‖Y - r (tbR D σ)‖ ≤ 2 * (M * period * lam) := by
        rw [hY]
        have h1 : sweepChord' r D σ (1 - lam) - r (tbR D σ)
            = lam • (r (taR D σ) - r (tbR D σ)) := by
          rw [sweepChord']; module
        have h3 : ‖sweepChord' r D σ (1 - lam) - r (tbR D σ)‖ ≤ M * period * lam := by
          rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos hlam]
          have h5 : ‖r (taR D σ) - r (tbR D σ)‖ = ‖r (tbR D σ) - r (taR D σ)‖ :=
            norm_sub_rev _ _
          rw [h5]
          calc lam * ‖r (tbR D σ) - r (taR D σ)‖ ≤ lam * (M * period) :=
                mul_le_mul_of_nonneg_left hLσ hlam.le
            _ = M * period * lam := by ring
        have h4 : ‖sweepArc' r D σ (1 - lam) - r (tbR D σ)‖ ≤ M * period * lam := by
          have h2 : sweepArc' r D σ (1 - lam) = r (tbR D σ - lam * sweepW' D σ) := by
            rw [sweepArc']
            congr 1
            rw [hwEq]
            ring
          rw [h2]
          have h5 := hlip (tbR D σ - lam * sweepW' D σ) (tbR D σ)
          have h6 : |tbR D σ - lam * sweepW' D σ - tbR D σ| = lam * sweepW' D σ := by
            rw [show tbR D σ - lam * sweepW' D σ - tbR D σ = -(lam * sweepW' D σ) by ring,
              abs_neg, abs_of_pos (mul_pos hlam hwpos)]
          rw [h6] at h5
          have h7 : M * (lam * sweepW' D σ) ≤ M * (lam * period) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hwper.le hlam.le) hMpos.le
          have h8 : M * (lam * period) = M * period * lam := by ring
          linarith [h5, h7, h8.le, h8.ge]
        have h9 : (1 - c') • sweepArc' r D σ (1 - lam) + c' • sweepChord' r D σ (1 - lam)
            - r (tbR D σ)
            = (1 - c') • (sweepArc' r D σ (1 - lam) - r (tbR D σ))
              + c' • (sweepChord' r D σ (1 - lam) - r (tbR D σ)) := by module
        rw [h9]
        calc ‖(1 - c') • (sweepArc' r D σ (1 - lam) - r (tbR D σ))
              + c' • (sweepChord' r D σ (1 - lam) - r (tbR D σ))‖
            ≤ ‖(1 - c') • (sweepArc' r D σ (1 - lam) - r (tbR D σ))‖
              + ‖c' • (sweepChord' r D σ (1 - lam) - r (tbR D σ))‖ := norm_add_le _ _
          _ ≤ (1 - c') * (M * period * lam) + c' * (M * period * lam) := by
              refine add_le_add ?_ ?_
              · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hc'.2)]
                exact mul_le_mul_of_nonneg_left h4 (sub_nonneg.mpr hc'.2)
              · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc'.1]
                exact mul_le_mul_of_nonneg_left h3 hc'.1
          _ = M * period * lam := by ring
          _ ≤ 2 * (M * period * lam) := by
              have hk := mul_pos (mul_pos hMpos hp) hlam
              linarith
      have hmain : ‖r (tbR D σ) - r (taR D σ)‖ ≤ 4 * (M * period * lam) := by
        have hstep : r (tbR D σ) - r (taR D σ)
            = (r (tbR D σ) - Y) + ((Y - X) + (X - r (taR D σ))) := by rw [← hXY]; abel
        rw [hstep]
        have h2 := norm_add_le (r (tbR D σ) - Y) ((Y - X) + (X - r (taR D σ)))
        have h3 := norm_add_le (Y - X) (X - r (taR D σ))
        have h0 : ‖Y - X‖ = 0 := by rw [hXY, sub_self, norm_zero]
        have h4 : ‖r (tbR D σ) - Y‖ = ‖Y - r (tbR D σ)‖ := norm_sub_rev _ _
        have h5 : (0 : ℝ) ≤ ‖Y - X‖ := norm_nonneg _
        linarith [h2, h3, h0, h4, hP, hQ, h5]
      have hmin : ‖r (tbR D σL) - r (taR D σL)‖ ≤ ‖r (tbR D σ) - r (taR D σ)‖ := hLmin hσ
      have hlamsmall : 4 * (M * period * lam) < ‖r (tbR D σL) - r (taR D σL)‖ := by
        have h2 : lam * (8 * M * period) ≤ ‖r (tbR D σL) - r (taR D σL)‖ := by
          have h1' : lam ≤ ‖r (tbR D σL) - r (taR D σL)‖ / (8 * M * period) := hlamch
          rw [le_div_iff₀ hden] at h1'
          linarith [h1']
        have h3 : 4 * (M * period * lam) = lam * (4 * M * period) := by ring
        rw [h3]
        have h4 : lam * (4 * M * period) < lam * (8 * M * period) :=
          mul_lt_mul_of_pos_left (by linarith [mul_pos hMpos hp]) hlam
        linarith [h2, h4]
      linarith [hmain, hmin, hlamsmall]
    exact chamfer_injOn_of_profile_nt D hlam (by linarith)
      (sweepLoopProfile_injOn_of_separation_nt D hlam hlam14 harc hchord hac harc_head harc_tail
        hchord_tail hchord_head hchamfers)

end Work.Drive
