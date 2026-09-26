import Mathlib
import Submission.Work.Drive.ofatSchedSlotOfCrosscut
import Submission.Work.Drive.ofatNeedleTroughGlue
import Submission.Work.Drive.ofatEndgameSWiring
import Submission.Work.Drive.sweepData_of_stripCrosscutOFatS

/-!
# The `OFat` endgame from its top end

`Work.Drive.OFatCrosscutEndgameS r` (`Drive/ofatEndgameSWiring.lean`) is the pin of the uniform-`ρ₀`
design: a bottom–top crosscut of the period strip avoiding `OFatObstructionS r' ρ δs` forces
`r'` to be unknotted.

Everything of that theorem is available *except* the construction of the sweep family from a knot
`C¹`-close to `r'` down to the needle slice (`Work.Drive.sweepNeedleFam`): the crosscut ⟹ band arc +
`SweepData` + middle-freeness + non-tangency (`Work.Drive.bandArcData_sweepData_of_stripCrosscutOFatS`),
the scheduling slot from the crosscut data (`Work.Drive.schedSlot_of_ballData`), the needle end
(`Work.Drive.needleEndEps_noHav`) and the glue
(`Work.Drive.unknotted_of_needleTrough`).

This module isolates the missing piece as the *named* hypothesis `Work.Drive.NeedleTopEnd` and proves
the endgame from it.  The top end is stated at a needle slice `ε` **in the bottom trough of the
schedule** (`4 * schedC D σ ≤ δs` on `[ε/2, 3ε/2]`), which is what makes the blurred scheduled slice
*equal* to the standard needle (`Work.Drive.sweepFamOf_schedLoop_eq_needle`); the trough slice exists
for any `δs > 0` because `schedC D 0 = 0`.
-/

noncomputable section

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant Set

/-- **The top end of the endgame, at a prescribed needle slice.**  The family from a knot
`C¹`-close to `r` down to the needle slice `sweepNeedleFam r D lam δ₁ δ₂ ε`, with all widths below
the prescribed budget `Δ` and the chamfer fraction below `Δ`. -/
def NeedleTopEnd (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (ε : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ Δ : ℝ, 0 < Δ →
    ∃ (lam δ₁ δ₂ : ℝ) (r0 : ℝ → Space) (H : ℝ → ℝ → Space),
      (0 < lam ∧ lam < 1 / 2 ∧ 0 < δ₁ ∧ 0 < δ₂ ∧ δ₂ ≤ ε / 2 ∧
        lam ≤ Δ ∧ δ₁ ≤ Δ ∧ δ₂ ≤ Δ) ∧
      IsSmoothKnot r0 ∧
      (∀ t : ℝ, ‖r0 t - r t‖ < δ ∧ ‖velocity r0 t - velocity r t‖ < δ) ∧
      ContDiff ℝ 1 (fun p : ℝ × ℝ => H p.1 p.2) ∧
      (∀ s t : ℝ, H (t + period) s = H t s) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1, IsCInfKnot (fun t : ℝ => H t s)) ∧
      (∀ t : ℝ, H t 0 = r0 t) ∧
      (∀ t : ℝ, H t 1 = sweepNeedleFam r D lam δ₁ δ₂ ε t)

/-! ## `clampI` bridges (local copies; the originals are `private` elsewhere) -/

private lemma clampI_of_mem_Ioo' {σ : ℝ} (h : σ ∈ Set.Ioo (0 : ℝ) 1) :
    clampI σ = ⟨σ, le_of_lt h.1, le_of_lt h.2⟩ := by
  apply Subtype.ext
  simp only [clampI, Subtype.coe_mk]
  rw [max_eq_right (le_of_lt h.1), min_eq_right (le_of_lt h.2)]

private lemma taR_eq_clampI' {d : BandArcData} (D : SweepData d) {σ : ℝ}
    (h : σ ∈ Set.Ioo (0 : ℝ) 1) :
    taR D σ = D.ta ⟨σ, le_of_lt h.1, le_of_lt h.2⟩ := by
  rw [taR, clampI_of_mem_Ioo' h]

private lemma tbR_eq_clampI' {d : BandArcData} (D : SweepData d) {σ : ℝ}
    (h : σ ∈ Set.Ioo (0 : ℝ) 1) :
    tbR D σ = D.tb ⟨σ, le_of_lt h.1, le_of_lt h.2⟩ := by
  rw [tbR, clampI_of_mem_Ioo' h]

private lemma not_smul_of_cross3_ne'' {v w : Space} (h : cross3 v w ≠ 0) (m : ℝ) : v ≠ m • w := by
  intro heq
  rcases eq_or_ne m 0 with hm | hm
  · subst hm
    rw [zero_smul] at heq
    exact h ((Commons.Analysis.CrossProduct.cross3_eq_zero_iff_smul v w).mpr (Or.inl heq))
  · refine h ((Commons.Analysis.CrossProduct.cross3_eq_zero_iff_smul v w).mpr (Or.inr ⟨m⁻¹, ?_⟩))
    rw [heq, smul_smul, inv_mul_cancel₀ hm, one_smul]

/-- **The `OFat` endgame, from the top end.** -/
theorem ofatEndgameS_of_topEnd
    (htop : ∀ (r : ℝ → Space) (hr : IsSmoothKnot r) {d : BandArcData} (D : SweepData d)
        {δs ε : ℝ},
      0 < δs → 0 < ε → ε < 1 / 2 →
      (∀ σ ∈ Set.Icc (ε / 2) (3 * ε / 2), 4 * schedC D σ ≤ δs) →
      (∀ Lmax : ℝ, 0 < Lmax → ∀ ε' σ₀ : ℝ, 0 < ε' → ε' < σ₀ → σ₀ < 1 →
        SchedSlot r D δs Lmax ε' σ₀) →
      NeedleTopEnd r D ε) :
    ∀ r : ℝ → Space, OFatCrosscutEndgameS r := by
  intro r hr
  obtain ⟨εb, μ, V, hεb0, hμ0, hV0, hall⟩ := exists_ballData r hr
  obtain ⟨εs, hεs0, hsepr⟩ := separation_of_far_parameters hr
  refine ⟨min εb εs, lt_min hεb0 hεs0, 1, one_pos, ?_⟩
  intro δs hδs0 hδs1
  obtain ⟨s, hs0, hsepL⟩ := hsepr (δs / 4) (by linarith)
  refine ⟨min (μ / 2) (min (δs / 3) (s / (2 * V + 1))), ?_, ?_⟩
  · have : 0 < s / (2 * V + 1) := by positivity
    positivity
  · intro r' hr' htc hinfl hclose ρ hρ0 hρρ0 hcc
    -- the C²- and C¹-closeness at the two ball radii
    have hclb : ∀ t : ℝ, ‖r' t - r t‖ < εb ∧ ‖velocity r' t - velocity r t‖ < εb ∧
        ‖deriv (deriv r') t - deriv (deriv r) t‖ < εb :=
      fun t => ⟨lt_of_lt_of_le (hclose t).1 (min_le_left _ _),
        lt_of_lt_of_le (hclose t).2.1 (min_le_left _ _),
        lt_of_lt_of_le (hclose t).2.2 (min_le_left _ _)⟩
    have hcls : ∀ t : ℝ, ‖r' t - r t‖ < εs ∧ ‖velocity r' t - velocity r t‖ < εs :=
      fun t => ⟨lt_of_lt_of_le (hclose t).1 (min_le_right _ _),
        lt_of_lt_of_le (hclose t).2.1 (min_le_right _ _)⟩
    -- the crosscut
    obtain ⟨γ, hbot, htopc, hint, havoid⟩ := hcc
    obtain ⟨d, D, hns, hmid, hshort, hnt⟩ :=
      bandArcData_sweepData_of_stripCrosscutOFatS (r := r') (ρ := ρ) (δs := δs) γ hbot htopc hint
        havoid
    -- the needle end
    obtain ⟨e₁, he₁0, he₁1, hneedleL⟩ :=
      needleEndEps_noHav hr' hinfl D (needleShiftedAngVelDep_noHav hr' hinfl D)
    -- the bottom trough of the schedule
    have hC0 : schedC D 0 = 0 := by
      have hW0 : sweepW' D 0 = 0 := by
        have hc0 : clampI (0 : ℝ) = (0 : Set.Icc (0 : ℝ) 1) := by
          apply Subtype.ext
          simp [clampI]
        rw [sweepW', taR, tbR, hc0]
        exact sub_eq_zero.mpr D.left_eq.symm
      rw [schedC, hW0]
      exact min_eq_left (by linarith [period_pos])
    have htol : 0 < δs / 8 := by linarith
    obtain ⟨η, hη0, hη⟩ := Metric.continuous_iff.mp (continuous_schedC D) 0 (δs / 8) htol
    set ε : ℝ := min (min (η / 3) (e₁ / 2)) (1 / 4) with hεdef
    have hε0 : 0 < ε := by
      rw [hεdef]
      exact lt_min (lt_min (by linarith) (by linarith)) (by norm_num)
    have hε1 : ε < 1 / 2 := by
      rw [hεdef]
      have h : ε ≤ 1 / 4 := by rw [hεdef]; exact min_le_right _ _
      linarith
    have hεe₁ : ε ≤ e₁ := by
      have h1 : ε ≤ e₁ / 2 := by
        rw [hεdef]
        exact le_trans (min_le_left _ _) (min_le_right _ _)
      linarith
    have hεη : 3 * ε / 2 < η := by
      have h1 : ε ≤ η / 3 := by
        rw [hεdef]
        exact le_trans (min_le_left _ _) (min_le_left _ _)
      linarith
    have htrough : ∀ σ ∈ Set.Icc (ε / 2) (3 * ε / 2), 4 * schedC D σ ≤ δs := by
      intro σ hσ
      have hσ0 : 0 ≤ σ := le_trans (by linarith [hε0]) hσ.1
      have hση : σ < η := lt_of_le_of_lt hσ.2 hεη
      have hdist : dist σ (0 : ℝ) < η := by
        rw [Real.dist_eq, sub_zero, abs_of_nonneg hσ0]; exact hση
      have h5 := hη σ hdist
      rw [Real.dist_eq, hC0, sub_zero] at h5
      have h6 : |schedC D σ| < δs / 8 := h5
      have h7 : schedC D σ < δs / 8 := (abs_lt.mp h6).2
      linarith
    -- the scheduling slot, from the crosscut data and the ball data
    have hslot : ∀ Lmax : ℝ, 0 < Lmax → ∀ ε' σ₀ : ℝ, 0 < ε' → ε' < σ₀ → σ₀ < 1 →
        SchedSlot r' D δs Lmax ε' σ₀ := by
      intro Lmax hLmax ε' σ₀ hε'0 hε'σ₀ hσ₀1
      have hρμ : 2 * ρ ≤ μ := by
        have h := le_trans hρρ0 (min_le_left (μ / 2) _); linarith
      have hρδs : 2 * ρ < δs := by
        have h := le_trans hρρ0 (le_trans (min_le_right (μ / 2) _) (min_le_left (δs / 3) _))
        linarith
      have hρs : 2 * V * ρ < s := by
        have h := le_trans hρρ0 (le_trans (min_le_right (μ / 2) _) (min_le_right (δs / 3) _))
        have hV1 : (0 : ℝ) < 2 * V + 1 := by linarith
        have h2 : 2 * V * ρ ≤ 2 * V * (s / (2 * V + 1)) :=
          mul_le_mul_of_nonneg_left h (by linarith)
        have h3 : 2 * V * (s / (2 * V + 1)) < s := by
          rw [mul_div, div_lt_iff₀ hV1]
          nlinarith [hs0, hV0]
        linarith
      exact schedSlot_of_ballData r hall r' hr' hclb hδs0 hρ0 hρμ hρδs hLmax hε'0 hε'σ₀ hσ₀1
        (hsepL r' hr' hcls) hs0 hρs D hmid hshort hnt
    -- the non-tangency and chord non-degeneracy in the `ℝ`-parametrised form
    have hntA' : ∀ sg : ℝ, 0 < sg → sg < 1 →
        cross3 (r' (tbR D sg) - r' (taR D sg)) (velocity r' (taR D sg)) ≠ 0 := by
      intro sg hsg0 hsg1
      have hsg : sg ∈ Set.Ioo (0 : ℝ) 1 := ⟨hsg0, hsg1⟩
      have h := (hnt ⟨sg, le_of_lt hsg0, le_of_lt hsg1⟩ (ne_of_gt hsg0) (ne_of_lt hsg1)).1
      simpa only [taR_eq_clampI' D hsg, tbR_eq_clampI' D hsg] using h
    have hntB' : ∀ sg : ℝ, 0 < sg → sg < 1 →
        cross3 (r' (tbR D sg) - r' (taR D sg)) (velocity r' (tbR D sg)) ≠ 0 := by
      intro sg hsg0 hsg1
      have hsg : sg ∈ Set.Ioo (0 : ℝ) 1 := ⟨hsg0, hsg1⟩
      have h := (hnt ⟨sg, le_of_lt hsg0, le_of_lt hsg1⟩ (ne_of_gt hsg0) (ne_of_lt hsg1)).2
      simpa only [taR_eq_clampI' D hsg, tbR_eq_clampI' D hsg] using h
    have hV' : ∀ sg : ℝ, 0 < sg → sg < 1 → r' (taR D sg) ≠ r' (tbR D sg) := by
      intro sg hsg0 hsg1 heq
      have h := not_smul_of_cross3_ne'' (hntA' sg hsg0 hsg1) 0
      rw [zero_smul] at h
      exact h (sub_eq_zero.mpr heq.symm)
    exact unknotted_of_needleTrough hr' D hV' hntB' hntA' hε0 hε1
      (htop (d := d) (D := D) (δs := δs) (ε := ε) r' hr' hδs0 hε0 hε1 htrough hslot)
      ⟨e₁, he₁0, he₁1, hεe₁, hneedleL⟩

end Work.Drive
