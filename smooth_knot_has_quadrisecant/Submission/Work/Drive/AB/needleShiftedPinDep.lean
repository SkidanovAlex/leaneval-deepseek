import Mathlib
import Submission.Work.Drive.AB.shiftedNeedlePinAssembly
import Submission.Work.Drive.AB.flatteningCore_of_chartData
import Submission.Work.Drive.AB.needleShift
import Submission.Work.Drive.AB.needleShiftedNotOnLine

/-!
# The chart pin of the needle, with a per-`ε` width budget and a single centre

`Work.Drive.NeedleShiftedChartPin` (the geometric pin of the needle end of the low end) has two
quantifier defects, both recorded in `NOTES_hnt_topEnd.md` / `ANGVEL_NOTES.md` and in the lead's
`00:10` plan:

1. its `ε₀` and `L` are chosen **before** the box, so the widths `lam, δ₁, δ₂` are only bounded by a
   constant while the needle's own size is `ε`.  The analytic estimate for the angular-velocity
   numerator (the diagonal margin is of size `~ ε³`, the blur mismatch of size
   `~(ε δ₁ + δ₂)²`) needs the widths to be bounded by a function of `ε`, not by a constant.  Hence
   the pin must be stated with a **per-`ε` width budget** `Λ ε`;
2. the angular-velocity clause `Work.Drive.NeedleShiftedAngVel` quantifies over **all** levels
   `y₀ ∈ (0, ‖chartUp‖)`.  Its margin is the vertical distance `‖chartUp‖ - y₀` from the centre to
   the base point, which degenerates as `y₀ → ‖chartUp‖`, while the blur mismatch is independent of
   `y₀`; so the `∀ y₀` form is *not* reachable by the blur estimate.  A single centre
   `y₀ = ‖chartUp‖ / 2` is all that `Work.Drive.ShiftedNeedleChartData` needs.

This module introduces the repaired predicates and proves that the repaired angular-velocity clause
gives the repaired chart pin.  Combined with `needleShiftedNotOnLine_of_infl`, the only geometric
obligation left for the whole generic unknotting target is
`Work.Drive.NeedleShiftedAngVelDep`.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant MeasureTheory
open scoped Real Topology

/-- **The angular-velocity obligation of the chart pin, with the single centre
`y₀ = ‖chartUp‖ / 2` and a per-`ε` width budget `Λ ε`.** -/
def NeedleShiftedAngVelDep (r : ℝ → Space) {d : BandArcData} (D : SweepData d) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
    ∃ Λ : ℝ, 0 < Λ ∧ ∀ (lam δ₁ δ₂ : ℝ), 0 < lam → lam ≤ Λ → lam < 1 / 2 → 0 < δ₁ → δ₁ ≤ Λ →
      0 < δ₂ → δ₂ ≤ Λ → δ₂ ≤ ε / 2 →
      ∀ (v : Space), ‖v‖ = 1 →
        chordEndB r D δ₂ ε - chordEndA r D δ₂ ε
          = ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ • v →
        ∀ t : ℝ,
          0 < (nHeight r D lam δ₁ δ₂ ε ((‖chartUp r D lam δ₁ δ₂ ε v‖)⁻¹ •
                  chartUp r D lam δ₁ δ₂ ε v) t
                - nHeight r D lam δ₁ δ₂ ε ((‖chartUp r D lam δ₁ δ₂ ε v‖)⁻¹ •
                  chartUp r D lam δ₁ δ₂ ε v) 0 + ‖chartUp r D lam δ₁ δ₂ ε v‖ / 2) *
              deriv (nCoord r D lam δ₁ δ₂ ε v) t
            - (nCoord r D lam δ₁ δ₂ ε v t - nCoord r D lam δ₁ δ₂ ε v 0) *
              deriv (nHeight r D lam δ₁ δ₂ ε ((‖chartUp r D lam δ₁ δ₂ ε v‖)⁻¹ •
                chartUp r D lam δ₁ δ₂ ε v)) t

/-- **The chart pin with a per-`ε` width budget.**  The `∃ ε₀` and the `∀ ε ≤ ε₀, ∃ Λ` replace the
single pair `(ε₀, L)` of `Work.Drive.NeedleShiftedChartPin`; the rest is
`Work.Drive.ShiftedNeedleChartData` verbatim. -/
def NeedleShiftedChartPinDep (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    (havoid : ∀ s : Set.Icc (0 : ℝ) 1, ∀ (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1),
      mobiusCover ⟨(d.a s, d.b s), d.offdiag s hs0 hs1⟩ ∉ trisecantSet r) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
    ∃ Λ : ℝ, 0 < Λ ∧ ∀ (lam δ₁ δ₂ : ℝ), 0 < lam → lam ≤ Λ → lam < 1 / 2 → 0 < δ₁ → δ₁ ≤ Λ →
      0 < δ₂ → δ₂ ≤ Λ → δ₂ ≤ ε / 2 → ShiftedNeedleChartData r D lam δ₁ δ₂ ε

/-- **The repaired chart pin from the repaired angular-velocity clause.**  The proof is the assembly
of `Work.Drive.needleShiftedChartPin_of_parts` with the box bounds replaced by the `ε`-dependent
budget `min (min L₁ L₂) (min (Λ₃ ε) L₄)`. -/
theorem needleShiftedChartPinDep_of_angVelDep {r : ℝ → Space} (hr : IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t])
    {d : BandArcData} (D : SweepData d)
    (havoid : ∀ s : Set.Icc (0 : ℝ) 1, ∀ (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1),
      mobiusCover ⟨(d.a s, d.b s), d.offdiag s hs0 hs1⟩ ∉ trisecantSet r)
    (hang : NeedleShiftedAngVelDep r D) : NeedleShiftedChartPinDep r D havoid := by
  obtain ⟨ε₁, L₁, hε₁, hL₁, hframe⟩ := exists_needleChartFrame hr D
  obtain ⟨ε₂, L₂, hε₂, hL₂, hray⟩ := shiftedNeedle_singleRay hr D
  obtain ⟨ε₃, hε₃, hangε⟩ := hang
  obtain ⟨ε₄, L₄, hε₄, hL₄, hnos⟩ := needleShiftedNotOnLine_of_infl hr hinfl D
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
  -- the frame brick supplies the chord direction `v` and `0 < ‖V‖`
  obtain ⟨e₀, v, -, hv, hev₀, hVpos, hVv, hbase₀⟩ :=
    hframe lam δ₁ δ₂ ε h1 hL₁' h3 h4 hδ₁L₁ h6 hδ₂L₁ hε0 hε₁' h8
      (hnos lam δ₁ δ₂ ε h1 hL₄' h3 h4 hδ₁L₄ h6 hδ₂L₄ hε0 hε₄' h8)
  set u : Space := chartUp r D lam δ₁ δ₂ ε v with hu
  have hu_ne : u ≠ 0 := by
    intro h0
    have hc0 : chartUp r D lam δ₁ δ₂ ε v = 0 := by rw [← hu, h0]
    have hz : shiftedNeedle r D lam δ₁ δ₂ ε 0 - chordEndA r D δ₂ ε
        = (nCoord r D lam δ₁ δ₂ ε v 0) • v := by
      have := hc0
      rw [chartUp] at this
      exact sub_eq_zero.mp this
    have hve₀ : inner ℝ v e₀ = 0 := by rw [real_inner_comm]; exact hev₀
    have hzero : inner ℝ (shiftedNeedle r D lam δ₁ δ₂ ε 0 - chordEndA r D δ₂ ε) e₀ = 0 := by
      rw [hz, real_inner_smul_left, hve₀, mul_zero]
    rw [nHeight] at hbase₀
    linarith
  have hu_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
  have he_ne : ‖u‖ ≠ 0 := ne_of_gt hu_pos
  have hnorm_e : ‖(‖u‖)⁻¹ • u‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg u)), inv_mul_cancel₀ he_ne]
  have horth_e : inner ℝ ((‖u‖)⁻¹ • u) v = 0 := by
    rw [real_inner_smul_left, hu, inner_chartUp_v r D lam δ₁ δ₂ ε hv, mul_zero]
  have hu_inner : inner ℝ (shiftedNeedle r D lam δ₁ δ₂ ε 0 - chordEndA r D δ₂ ε) u = ‖u‖ ^ 2 := by
    rw [hu]
    exact inner_shiftedNeedle_chartUp r D lam δ₁ δ₂ ε hv
  have hheight : nHeight r D lam δ₁ δ₂ ε ((‖u‖)⁻¹ • u) 0 = ‖u‖ := by
    rw [nHeight]
    exact inner_smul_unit_of_inner_eq _ _ hu_inner
  refine ⟨(‖u‖)⁻¹ • u, v, ‖u‖ / 2, hnorm_e, hv, horth_e, hVpos, hVv,
    by linarith, by rw [hheight]; linarith, ?_, ?_⟩
  · intro t ht0 htp hcoord
    exact hray lam δ₁ δ₂ ε h1 hL₂' h3 h4 hδ₁L₂ h6 hδ₂L₂ hε0 hε₂' h8 _ v hnorm_e hv horth_e
      hVpos hVv _ (by linarith) (by rw [hheight]; linarith) t ht0 htp hcoord
  · intro t
    exact hang' lam δ₁ δ₂ h1 hL₃' h3 h4 hδ₁L₃ h6 hδ₂L₃ h8 v hv hVv t

/-- **The needle end with the per-`ε` width budget, from the repaired chart pin.**  The whole chain
`ShiftedNeedleChartData → FlatteningCore → FlatteningData → the family to the circle` is pointwise
in the box (`Work.Drive.flatteningCore_of_chartData`, `Work.Drive.flatteningData_of_core`,
`Work.Drive.shifted_needle_family`), so the budget passes through. -/
theorem needleEndDep_of_chartPinDep {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d)
    (havoid : ∀ s : Set.Icc (0 : ℝ) 1, ∀ (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1),
      mobiusCover ⟨(d.a s, d.b s), d.offdiag s hs0 hs1⟩ ∉ trisecantSet r)
    (hpin : NeedleShiftedChartPinDep r D havoid) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ Λ : ℝ, 0 < Λ ∧
      ∀ (lam δ₁ δ₂ : ℝ), 0 < lam → lam ≤ Λ → lam < 1 / 2 → 0 < δ₁ → δ₁ ≤ Λ →
        0 < δ₂ → δ₂ ≤ Λ → δ₂ ≤ ε / 2 →
        ∃ (c f1 f2 : Space) (R : ℝ) (F : ℝ → ℝ → Space),
          ContDiff ℝ 1 (fun p : ℝ × ℝ => F p.1 p.2) ∧
          (∀ s t : ℝ, F (t + period) s = F t s) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, IsCInfKnot (fun t : ℝ => F t s)) ∧
          (∀ t : ℝ, F t 0 = sweepNeedleFam r D lam δ₁ δ₂ ε t) ∧
          (∀ t : ℝ, F t 1 = c + R • (Real.cos t • f1 + Real.sin t • f2)) ∧
          0 < R ∧ ‖f1‖ = 1 ∧ ‖f2‖ = 1 ∧ inner ℝ f1 f2 = 0 := by
  obtain ⟨ε₀, hε₀, hmain⟩ := hpin
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε0 hεε₀
  obtain ⟨Λ, hΛ, hchart⟩ := hmain ε hε0 hεε₀
  refine ⟨Λ, hΛ, ?_⟩
  intro lam δ₁ δ₂ h1 h2 h3 h4 h5 h6 h7 h8
  have hcore : FlatteningCore (shiftedNeedle r D lam δ₁ δ₂ ε) :=
    flatteningCore_of_chartData D (contDiff_shiftedNeedle hr D h4 h6)
      (hchart lam δ₁ δ₂ h1 h2 h3 h4 h5 h6 h7 h8)
  have hdata : FlatteningData (fun t : ℝ => needleFam r D lam δ₁ δ₂ ε (t + period / 4)) :=
    flatteningData_of_core (contDiff_shiftedNeedle hr D h4 h6)
      (periodic_shiftedNeedle hr D h4 h6) hcore
  exact shifted_needle_family hr D h4 h6 hdata

/-- **The budgeted needle end at a prescribed size, from the repaired angular-velocity clause.**  The
threshold form (`∃ ε₁ ∈ (0,1/2), ∀ ε ≤ ε₁, ∃ Λ, …`) is exactly the `hneedle` argument of
`Work.Drive.Generic.unknotted_of_needleEndEps`; it is obtained from the repaired chart pin
(`needleShiftedChartPinDep_of_angVelDep`, using the base-point clause
`needleShiftedNotOnLine_of_infl`) composed with `needleEndDep_of_chartPinDep`. -/
theorem needleEndEps_of_angVelDep {r : ℝ → Space} (hr : IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t])
    {d : BandArcData} (D : SweepData d)
    (havoid : ∀ s : Set.Icc (0 : ℝ) 1, ∀ (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1),
      mobiusCover ⟨(d.a s, d.b s), d.offdiag s hs0 hs1⟩ ∉ trisecantSet r)
    (hang : NeedleShiftedAngVelDep r D) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ < 1 / 2 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₁ → ∃ Λ : ℝ, 0 < Λ ∧
      ∀ (lam δ₁ δ₂ : ℝ), 0 < lam → lam ≤ Λ → lam < 1 / 2 → 0 < δ₁ → δ₁ ≤ Λ →
        0 < δ₂ → δ₂ ≤ Λ → δ₂ ≤ ε / 2 →
        ∃ (c f1 f2 : Space) (R : ℝ) (F : ℝ → ℝ → Space),
          ContDiff ℝ 1 (fun p : ℝ × ℝ => F p.1 p.2) ∧
          (∀ s t : ℝ, F (t + period) s = F t s) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, IsCInfKnot (fun t : ℝ => F t s)) ∧
          (∀ t : ℝ, F t 0 = sweepNeedleFam r D lam δ₁ δ₂ ε t) ∧
          (∀ t : ℝ, F t 1 = c + R • (Real.cos t • f1 + Real.sin t • f2)) ∧
          0 < R ∧ ‖f1‖ = 1 ∧ ‖f2‖ = 1 ∧ inner ℝ f1 f2 = 0 := by
  obtain ⟨ε₀, hε₀, hmain⟩ :=
    needleEndDep_of_chartPinDep hr D havoid
      (needleShiftedChartPinDep_of_angVelDep hr hinfl D havoid hang)
  refine ⟨min ε₀ (1 / 4), lt_min hε₀ (by norm_num), by
    have h := min_le_right ε₀ (1 / 4 : ℝ); linarith, ?_⟩
  intro ε hε0 hεε₁
  exact hmain ε hε0 (le_trans hεε₁ (min_le_left _ _))

end Work.Drive
