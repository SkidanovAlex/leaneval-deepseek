import Mathlib
import Submission.Work.Drive.AB.needleShiftedPinDep
import Submission.Work.Drive.Generic.unknotted_of_needleEndEps
import Submission.Work.Drive.Generic.needleChartLoop_margin
import Submission.Work.Drive.Generic.needleChart_oscBounds
import Submission.Work.Drive.Generic.shiftedNeedle_deriv_eq_doubleAverage
import Submission.Work.Drive.Generic.needleShiftedAngVelDep_of_bounds

/-!
# The needle end of the `OFat` lane: the `havoid`-free transcription

The needle end (`Work.Drive.Generic.needleEndEps_of_angVelDep`, the pin of the generic-case lane) is
stated with an `O`-avoidance hypothesis `havoid` of the band arc as an *argument*, but the proofs in
the chain do not use it:

* `Work.Drive.Generic.needleChartLoop_margin` is `nclm_margin_of_chartDataC hr hinfl D
  (nclm_chartDataE hr hinfl D)` — no `havoid`;
* the repaired chart pin `Work.Drive.needleShiftedChartPinDep_of_angVelDep` uses
  `exists_needleChartFrame`, `shiftedNeedle_singleRay`, `needleShiftedNotOnLine_of_infl` and the
  angular-velocity clause — no `havoid`;
* the family assembly (`flatteningCore_of_chartData` → `flatteningData_of_core` →
  `shifted_needle_family`) is pointwise in the box — no `havoid`.

This module therefore transcribes the chain without the `havoid` binder, so that the endgame of the
`OFat` lane (whose crosscut avoids only `OFatObstruction = OFatR ∪ TCset`, **not** the whole trisecant
locus) can use it.  The statements are the same modulo the removal of the unused argument; the proofs
are the proofs of the originals.
-/

noncomputable section

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-- `Work.Drive.Generic.needleChartLoop_margin` without its unused `havoid` argument. -/
theorem needleChartLoop_margin_noHav {r : ℝ → Space} (hr : IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t])
    {d : BandArcData} (D : Work.Drive.SweepData d) :
    Work.Drive.ChartLoopMargin r D :=
  Work.Drive.Generic.nclm_margin_of_chartDataC hr hinfl D
    (Work.Drive.Generic.nclm_chartDataE hr hinfl D)

/-- `Work.Drive.needleShiftedAngVelDep_proved` without its unused `havoid` argument. -/
theorem needleShiftedAngVelDep_noHav {r : ℝ → Space} (hr : IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t])
    {d : BandArcData} (D : Work.Drive.SweepData d) :
    Work.Drive.NeedleShiftedAngVelDep r D :=
  Work.Drive.Generic.needleShiftedAngVelDep_of_bounds hr D
    (fun {lam δ₁ δ₂ ε} h1 h2 h3 h4 h5 h6 c' u t =>
      Work.Drive.Generic.shiftedNeedle_deriv_eq_doubleAverage hr D h1 h2 h3 h4 h5 h6 c' u t)
    (needleChartLoop_margin_noHav hr hinfl D)
    (Work.Drive.Generic.needleChart_oscBounds hr D)

/-- **The repaired chart pin without `havoid`** (the statement of
`Work.Drive.needleShiftedChartPinDep_of_angVelDep` with `NeedleShiftedChartPinDep r D havoid`
unfolded). -/
theorem needleShiftedChartPin_noHav {r : ℝ → Space} (hr : IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t])
    {d : BandArcData} (D : Work.Drive.SweepData d)
    (hang : Work.Drive.NeedleShiftedAngVelDep r D) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∃ Λ : ℝ, 0 < Λ ∧ ∀ (lam δ₁ δ₂ : ℝ), 0 < lam → lam ≤ Λ → lam < 1 / 2 → 0 < δ₁ → δ₁ ≤ Λ →
        0 < δ₂ → δ₂ ≤ Λ → δ₂ ≤ ε / 2 → Work.Drive.ShiftedNeedleChartData r D lam δ₁ δ₂ ε := by
  obtain ⟨ε₁, L₁, hε₁, hL₁, hframe⟩ := Work.Drive.exists_needleChartFrame hr D
  obtain ⟨ε₂, L₂, hε₂, hL₂, hray⟩ := Work.Drive.shiftedNeedle_singleRay hr D
  obtain ⟨ε₃, hε₃, hangε⟩ := hang
  obtain ⟨ε₄, L₄, hε₄, hL₄, hnos⟩ := Work.Drive.needleShiftedNotOnLine_of_infl hr hinfl D
  refine ⟨min (min ε₁ ε₂) (min ε₃ ε₄),
    lt_min (lt_min hε₁ hε₂) (lt_min hε₃ hε₄), ?_⟩
  intro ε hε0 hεε₀
  have hε₁' : ε ≤ ε₁ := le_trans hεε₀ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hε₂' : ε ≤ ε₂ := le_trans hεε₀ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hε₃' : ε ≤ ε₃ := le_trans hεε₀ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hε₄' : ε ≤ ε₄ := le_trans hεε₀ (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨Λ₃, hΛ₃, hang'⟩ := hangε ε hε0 hε₃'
  refine ⟨min (min L₁ L₂) (min Λ₃ L₄),
    lt_min (lt_min hL₁ hL₂) (lt_min hΛ₃ hL₄), ?_⟩
  intro lam δ₁ δ₂ h1 h2 h3 h4 h5 h6 h7 h8
  have hL₁' : lam ≤ L₁ := le_trans h2 (le_trans (min_le_left _ _) (min_le_left _ _))
  have hL₂' : lam ≤ L₂ := le_trans h2 (le_trans (min_le_left _ _) (min_le_right _ _))
  have hL₃' : lam ≤ Λ₃ := le_trans h2 (le_trans (min_le_right _ _) (min_le_left _ _))
  have hL₄' : lam ≤ L₄ := le_trans h2 (le_trans (min_le_right _ _) (min_le_right _ _))
  have hδ₁L₁ : δ₁ ≤ L₁ := le_trans h5 (le_trans (min_le_left _ _) (min_le_left _ _))
  have hδ₁L₂ : δ₁ ≤ L₂ := le_trans h5 (le_trans (min_le_left _ _) (min_le_right _ _))
  have hδ₁L₃ : δ₁ ≤ Λ₃ := le_trans h5 (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδ₁L₄ : δ₁ ≤ L₄ := le_trans h5 (le_trans (min_le_right _ _) (min_le_right _ _))
  have hδ₂L₁ : δ₂ ≤ L₁ := le_trans h7 (le_trans (min_le_left _ _) (min_le_left _ _))
  have hδ₂L₂ : δ₂ ≤ L₂ := le_trans h7 (le_trans (min_le_left _ _) (min_le_right _ _))
  have hδ₂L₃ : δ₂ ≤ Λ₃ := le_trans h7 (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδ₂L₄ : δ₂ ≤ L₄ := le_trans h7 (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨e₀, v, -, hv, hev₀, hVpos, hVv, hbase₀⟩ :=
    hframe lam δ₁ δ₂ ε h1 hL₁' h3 h4 hδ₁L₁ h6 hδ₂L₁ hε0 hε₁' h8
      (hnos lam δ₁ δ₂ ε h1 hL₄' h3 h4 hδ₁L₄ h6 hδ₂L₄ hε0 hε₄' h8)
  set u : Space := Work.Drive.chartUp r D lam δ₁ δ₂ ε v with hu
  have hu_ne : u ≠ 0 := by
    intro h0
    have hc0 : Work.Drive.chartUp r D lam δ₁ δ₂ ε v = 0 := by rw [← hu, h0]
    have hz : Work.Drive.shiftedNeedle r D lam δ₁ δ₂ ε 0 - Work.Drive.chordEndA r D δ₂ ε
        = (Work.Drive.nCoord r D lam δ₁ δ₂ ε v 0) • v := by
      have := hc0
      rw [Work.Drive.chartUp] at this
      exact sub_eq_zero.mp this
    have hve₀ : inner ℝ v e₀ = 0 := by rw [real_inner_comm]; exact hev₀
    have hzero : inner ℝ (Work.Drive.shiftedNeedle r D lam δ₁ δ₂ ε 0
        - Work.Drive.chordEndA r D δ₂ ε) e₀ = 0 := by
      rw [hz, real_inner_smul_left, hve₀, mul_zero]
    rw [Work.Drive.nHeight] at hbase₀
    linarith
  have hu_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
  have he_ne : ‖u‖ ≠ 0 := ne_of_gt hu_pos
  have hnorm_e : ‖(‖u‖)⁻¹ • u‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg u)), inv_mul_cancel₀ he_ne]
  have horth_e : inner ℝ ((‖u‖)⁻¹ • u) v = 0 := by
    rw [real_inner_smul_left, hu, Work.Drive.inner_chartUp_v r D lam δ₁ δ₂ ε hv, mul_zero]
  have hu_inner : inner ℝ (Work.Drive.shiftedNeedle r D lam δ₁ δ₂ ε 0
      - Work.Drive.chordEndA r D δ₂ ε) u = ‖u‖ ^ 2 := by
    rw [hu]
    exact Work.Drive.inner_shiftedNeedle_chartUp r D lam δ₁ δ₂ ε hv
  have hheight : Work.Drive.nHeight r D lam δ₁ δ₂ ε ((‖u‖)⁻¹ • u) 0 = ‖u‖ := by
    rw [Work.Drive.nHeight]
    exact Work.Drive.inner_smul_unit_of_inner_eq _ _ hu_inner
  refine ⟨(‖u‖)⁻¹ • u, v, ‖u‖ / 2, hnorm_e, hv, horth_e, hVpos, hVv,
    by linarith, by rw [hheight]; linarith, ?_, ?_⟩
  · intro t ht0 htp hcoord
    exact hray lam δ₁ δ₂ ε h1 hL₂' h3 h4 hδ₁L₂ h6 hδ₂L₂ hε0 hε₂' h8 _ v hnorm_e hv horth_e
      hVpos hVv _ (by linarith) (by rw [hheight]; linarith) t ht0 htp hcoord
  · intro t
    exact hang' lam δ₁ δ₂ h1 hL₃' h3 h4 hδ₁L₃ h6 hδ₂L₃ h8 v hv hVv t

/-- **The needle end with the per-`ε` width budget, without `havoid`.** -/
theorem needleEndDep_of_chartPin_noHav {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : Work.Drive.SweepData d)
    (hpin : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∃ Λ : ℝ, 0 < Λ ∧ ∀ (lam δ₁ δ₂ : ℝ), 0 < lam → lam ≤ Λ → lam < 1 / 2 → 0 < δ₁ → δ₁ ≤ Λ →
        0 < δ₂ → δ₂ ≤ Λ → δ₂ ≤ ε / 2 → Work.Drive.ShiftedNeedleChartData r D lam δ₁ δ₂ ε) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ Λ : ℝ, 0 < Λ ∧
      ∀ (lam δ₁ δ₂ : ℝ), 0 < lam → lam ≤ Λ → lam < 1 / 2 → 0 < δ₁ → δ₁ ≤ Λ →
        0 < δ₂ → δ₂ ≤ Λ → δ₂ ≤ ε / 2 →
        ∃ (c f1 f2 : Space) (R : ℝ) (F : ℝ → ℝ → Space),
          ContDiff ℝ 1 (fun p : ℝ × ℝ => F p.1 p.2) ∧
          (∀ s t : ℝ, F (t + period) s = F t s) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, IsCInfKnot (fun t : ℝ => F t s)) ∧
          (∀ t : ℝ, F t 0 = Work.Drive.sweepNeedleFam r D lam δ₁ δ₂ ε t) ∧
          (∀ t : ℝ, F t 1 = c + R • (Real.cos t • f1 + Real.sin t • f2)) ∧
          0 < R ∧ ‖f1‖ = 1 ∧ ‖f2‖ = 1 ∧ inner ℝ f1 f2 = 0 := by
  obtain ⟨ε₀, hε₀, hmain⟩ := hpin
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε0 hεε₀
  obtain ⟨Λ, hΛ, hchart⟩ := hmain ε hε0 hεε₀
  refine ⟨Λ, hΛ, ?_⟩
  intro lam δ₁ δ₂ h1 h2 h3 h4 h5 h6 h7 h8
  have hcore : Work.Drive.FlatteningCore (Work.Drive.shiftedNeedle r D lam δ₁ δ₂ ε) :=
    Work.Drive.flatteningCore_of_chartData D (Work.Drive.contDiff_shiftedNeedle hr D h4 h6)
      (hchart lam δ₁ δ₂ h1 h2 h3 h4 h5 h6 h7 h8)
  have hdata : Work.Drive.FlatteningData
      (fun t : ℝ => Work.Drive.needleFam r D lam δ₁ δ₂ ε (t + period / 4)) :=
    Work.Drive.flatteningData_of_core (Work.Drive.contDiff_shiftedNeedle hr D h4 h6)
      (Work.Drive.periodic_shiftedNeedle hr D h4 h6) hcore
  exact Work.Drive.shifted_needle_family hr D h4 h6 hdata

/-- **The budgeted needle end at a prescribed size, without `havoid`.** -/
theorem needleEndEps_noHav {r : ℝ → Space} (hr : IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t])
    {d : BandArcData} (D : Work.Drive.SweepData d)
    (hang : Work.Drive.NeedleShiftedAngVelDep r D) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ < 1 / 2 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₁ → ∃ Λ : ℝ, 0 < Λ ∧
      ∀ (lam δ₁ δ₂ : ℝ), 0 < lam → lam ≤ Λ → lam < 1 / 2 → 0 < δ₁ → δ₁ ≤ Λ →
        0 < δ₂ → δ₂ ≤ Λ → δ₂ ≤ ε / 2 →
        ∃ (c f1 f2 : Space) (R : ℝ) (F : ℝ → ℝ → Space),
          ContDiff ℝ 1 (fun p : ℝ × ℝ => F p.1 p.2) ∧
          (∀ s t : ℝ, F (t + period) s = F t s) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, IsCInfKnot (fun t : ℝ => F t s)) ∧
          (∀ t : ℝ, F t 0 = Work.Drive.sweepNeedleFam r D lam δ₁ δ₂ ε t) ∧
          (∀ t : ℝ, F t 1 = c + R • (Real.cos t • f1 + Real.sin t • f2)) ∧
          0 < R ∧ ‖f1‖ = 1 ∧ ‖f2‖ = 1 ∧ inner ℝ f1 f2 = 0 := by
  obtain ⟨ε₀, hε₀, hmain⟩ :=
    needleEndDep_of_chartPin_noHav hr D (needleShiftedChartPin_noHav hr hinfl D hang)
  refine ⟨min ε₀ (1 / 4), lt_min hε₀ (by norm_num), by
    have h := min_le_right ε₀ (1 / 4 : ℝ); linarith, ?_⟩
  intro ε hε0 hεε₁
  exact hmain ε hε0 (le_trans hεε₁ (min_le_left _ _))

end Work.Drive

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-- **The endgame glue without `havoid`**: the top end, the (havoid-free) needle end and
`isUnknotted_of_close`, glued exactly as in `Work.Drive.Generic.unknotted_of_needleEndEps` (whose
`havoid` argument is unused). -/
theorem unknotted_of_needleEndEps_noHav {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : Work.Drive.SweepData d)
    (hV : ∀ sg : ℝ, 0 < sg → sg < 1 → r (Work.Drive.taR D sg) ≠ r (Work.Drive.tbR D sg))
    (hntB : ∀ sg : ℝ, 0 < sg → sg < 1 →
      cross3 (r (Work.Drive.tbR D sg) - r (Work.Drive.taR D sg))
        (velocity r (Work.Drive.tbR D sg)) ≠ 0)
    (hntA : ∀ sg : ℝ, 0 < sg → sg < 1 →
      cross3 (r (Work.Drive.tbR D sg) - r (Work.Drive.taR D sg))
        (velocity r (Work.Drive.taR D sg)) ≠ 0)
    (htop : ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∀ Δ : ℝ, 0 < Δ →
      ∃ (lam δ₁ δ₂ : ℝ) (r0 : ℝ → Space) (H : ℝ → ℝ → Space),
        (0 < lam ∧ lam < 1 / 2 ∧ 0 < δ₁ ∧ 0 < δ₂ ∧ δ₂ ≤ ε / 2 ∧
          lam ≤ Δ ∧ δ₁ ≤ Δ ∧ δ₂ ≤ Δ) ∧
        IsSmoothKnot r0 ∧
        (∀ t : ℝ, ‖r0 t - r t‖ < δ ∧ ‖velocity r0 t - velocity r t‖ < δ) ∧
        ContDiff ℝ 1 (fun p : ℝ × ℝ => H p.1 p.2) ∧
        (∀ s t : ℝ, H (t + period) s = H t s) ∧
        (∀ s ∈ Set.Icc (0 : ℝ) 1, Work.Drive.IsCInfKnot (fun t : ℝ => H t s)) ∧
        (∀ t : ℝ, H t 0 = r0 t) ∧
        (∀ t : ℝ, H t 1 = Work.Drive.sweepNeedleFam r D lam δ₁ δ₂ ε t))
    (hneedle : ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ < 1 / 2 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₁ → ∃ Λ : ℝ, 0 < Λ ∧
      ∀ (lam δ₁ δ₂ : ℝ), 0 < lam → lam ≤ Λ → lam < 1 / 2 → 0 < δ₁ → δ₁ ≤ Λ →
        0 < δ₂ → δ₂ ≤ Λ → δ₂ ≤ ε / 2 →
        ∃ (c f1 f2 : Space) (R : ℝ) (F : ℝ → ℝ → Space),
          ContDiff ℝ 1 (fun p : ℝ × ℝ => F p.1 p.2) ∧
          (∀ s t : ℝ, F (t + period) s = F t s) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, Work.Drive.IsCInfKnot (fun t : ℝ => F t s)) ∧
          (∀ t : ℝ, F t 0 = Work.Drive.sweepNeedleFam r D lam δ₁ δ₂ ε t) ∧
          (∀ t : ℝ, F t 1 = c + R • (Real.cos t • f1 + Real.sin t • f2)) ∧
          0 < R ∧ ‖f1‖ = 1 ∧ ‖f2‖ = 1 ∧ inner ℝ f1 f2 = 0) :
    IsUnknotted r := by
  obtain ⟨δ, hδpos, hδcl⟩ := Work.Drive.isUnknotted_of_close hr
  obtain ⟨ε₁, hε₁0, hε₁1, hneedle'⟩ := hneedle
  have hε0 : (0 : ℝ) < ε₁ / 2 := by linarith
  have hε1 : ε₁ / 2 < 1 / 2 := by linarith
  have hε1' : ε₁ / 2 ≤ ε₁ := by linarith
  obtain ⟨Λ, hΛpos, htail⟩ := hneedle' (ε₁ / 2) hε0 hε1'
  obtain ⟨lam, δ₁, δ₂, r0, H, hpar, hr0, hclose, hHsm, hHper, hHsl, hH0, hH1⟩ :=
    htop δ hδpos (ε₁ / 2) hε0 hε1 Λ hΛpos
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hpar
  obtain ⟨c, f1, f2, R, F, hFsm, hFper, hFsl, hF0, hF1, hR, hf1, hf2, hperp⟩ :=
    htail lam δ₁ δ₂ h1 h6 h2 h3 h7 h4 h8 h5
  have hjun : ∀ t : ℝ, H t 1 = F t 0 := fun t => by rw [hH1 t, hF0 t]
  have hglue := Work.Drive.sweepGlue_clauses hHsm hFsm hjun hHsl hFsl hHper hFper
  have hcircU : IsUnknotted (fun t : ℝ => c + R • (Real.cos t • f1 + Real.sin t • f2)) :=
    Work.Drive.framedStarShapedPolarGraph c f1 f2 hf1 hf2 hperp contDiff_const (fun _ => rfl)
      (fun _ => hR) contDiff_id (fun _ => rfl) (fun t => by simpa using deriv_id'' (x := t))
  have hcircS : IsSmoothKnot (fun t : ℝ => c + R • (Real.cos t • f1 + Real.sin t • f2)) :=
    Work.Drive.polarCircle_isSmoothKnot hR hf1 hf2 hperp
  have hU : IsUnknotted r0 :=
    Work.Drive.cInfKnotPath_to_unknotted hr0 hcircS hcircU
      (F := fun t s : ℝ => Work.Drive.sweepGlue H F s t) hglue.1 hglue.2.1
      (fun t => by rw [hglue.2.2.2.1 t, hH0 t])
      (fun t => by rw [hglue.2.2.2.2 t, hF1 t]) hglue.2.2.1
  exact hδcl r0 hr0 hclose hU

end Work.Drive
