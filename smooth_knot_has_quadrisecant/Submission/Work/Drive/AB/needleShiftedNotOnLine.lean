import Mathlib
import Submission.Work.Drive.AB.shiftedNeedlePinAssembly
import Submission.Work.Drive.AB.needleHalfspaceProfile
import Submission.Work.Drive.AB.windowDataSmall
import Submission.Work.Drive.AB.needleHeightSeparation
import Submission.Work.Drive.AB.needleArcZoneMono

/-!
# The base point of the shifted needle is off the chord's line

`Work.Drive.NeedleShiftedNotOnLine r D` is one of the two remaining obligations of the chart pin
`Work.Drive.NeedleShiftedChartPin` (the other being the angular-velocity clause
`Work.Drive.NeedleShiftedAngVel`); see `shiftedNeedlePinAssembly.lean`.

The statement is that the *base point* of the shifted needle — the needle's point at the loop
parameter `period / 4`, i.e. the doubly blurred **middle of the retained arc** — never lies on the
affine line of the needle's chord `[chordEndA, chordEndB]` (note: on the whole line, not just on the
segment, since the chart frame needs the point to be off the line).

The proof is the one recorded for `Work.Drive.needleArcChordSep_generic`, but specialised to the
single parameter `t = period / 4` and with the *strict* half-space input (the direction `e` produced
by `Work.Drive.exists_secondDeriv_halfspace` has `⟪e, r''⟫ < 0` at **every** point of the window,
so `Work.Drive.loopDev_pos_of_halfspace` and `Work.Drive.needleFam_inner_pos_of_pointwise` suffice —
no continuity of the `σ`-average is needed):

* the non-inflection hypothesis `htrans` of `needleArcChordSep_generic` is *automatic* from the
  generic hypothesis `hinfl` (`r'` and `r''` linearly independent everywhere), so this module
  replaces it by `hinfl` — see `exists_secondDerivDir_of_linearIndependent`;
* the two bookkeeping estimates (the retained arcs of the window lie in a `δ`-neighbourhood of the
  collapsed end, and the needle's chord direction is close to the tangent there) are
  `Work.Drive.windowDataSmall`;
* on the window, a point with positive height above the chord's line is off the whole line:
  `Work.Drive.ne_chordSegment_of_height_pos`.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant MeasureTheory
open scoped Real Topology intervalIntegral

/-! ## The half-space direction exists at every non-inflection -/

lemma velocity_eq_deriv_fn (r : ℝ → Space) : velocity r = deriv r := rfl

/-- **Linear independence of `r'` and `r''` gives the half-space datum of a non-inflection**: a unit
vector orthogonal to the velocity with positive pairing against the acceleration.  This is the
`htrans` hypothesis of `Work.Drive.needleArcChordSep_generic`, extracted from `hinfl`. -/
lemma exists_secondDerivDir_of_linearIndependent {r : ℝ → Space} {t : ℝ}
    (hLI : LinearIndependent ℝ ![deriv r t, deriv (deriv r) t]) :
    ∃ e₀ : Space, ‖e₀‖ = 1 ∧ inner ℝ e₀ (deriv r t) = 0 ∧
      0 < inner ℝ e₀ (deriv (deriv r) t) := by
  set x : Space := deriv r t with hx
  set y : Space := deriv (deriv r) t with hy
  obtain ⟨hy0, h2⟩ := linearIndependent_fin2.mp hLI
  have hx0 : x ≠ 0 := by
    have h := h2 0
    rw [zero_smul] at h
    exact fun hx' => h hx'.symm
  have hy_not_smul : ∀ c : ℝ, y ≠ c • x := by
    intro c hc
    have hcne : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      exact hy0 hc
    have hxeq : c⁻¹ • y = x := by
      rw [hc, smul_smul, inv_mul_cancel₀ hcne, one_smul]
    exact h2 c⁻¹ hxeq
  have hxx : inner ℝ x x ≠ 0 := by
    rw [real_inner_self_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hx0)
  set c₀ : ℝ := inner ℝ y x / inner ℝ x x with hc₀
  set w : Space := y - c₀ • x with hw
  have hwx : inner ℝ w x = 0 := by
    rw [hw, inner_sub_left, real_inner_smul_left, hc₀, div_mul_cancel₀ _ hxx, sub_self]
  have hw0 : w ≠ 0 := by
    intro hwz
    have hyl : y = c₀ • x := by
      rw [hw] at hwz
      exact sub_eq_zero.mp hwz
    exact hy_not_smul c₀ hyl
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hwne : ‖w‖ ≠ 0 := ne_of_gt hwn
  have hwy : inner ℝ w y = ‖w‖ ^ 2 := by
    have hydec : y = w + c₀ • x := by rw [hw]; abel
    rw [hydec, inner_add_right, real_inner_smul_right, hwx, mul_zero, add_zero,
      real_inner_self_eq_norm_sq]
  refine ⟨‖w‖⁻¹ • w, ?_, ?_, ?_⟩
  · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg w)), inv_mul_cancel₀ hwne]
  · rw [real_inner_smul_left, hwx, mul_zero]
  · rw [real_inner_smul_left, hwy]
    have hsq : ‖w‖⁻¹ * ‖w‖ ^ 2 = ‖w‖ := by
      rw [sq, ← mul_assoc, inv_mul_cancel₀ hwne, one_mul]
    rw [hsq]
    exact hwn

/-! ## The loop parameter `period / 4` sits on the arc zone -/

/-- `sweepParam` is `z / period` on one period cell. -/
lemma sweepParam_eq_div_of_mem' {z : ℝ} (h0 : 0 ≤ z) (h1 : z < period) :
    sweepParam z = z / period := by
  have hp : (0 : ℝ) < period := period_pos
  have hge : (0 : ℝ) ≤ z / period := div_nonneg h0 hp.le
  have hlt : z / period < 1 := by rw [div_lt_one hp]; exact h1
  have hfloor : ⌊z / period⌋ = 0 := Int.floor_eq_zero_iff.mpr (Set.mem_Ico.mpr ⟨hge, hlt⟩)
  rw [sweepParam, hfloor]
  ring

/-- For `δ₁ ≤ period / 4` the whole `δ₁`-blur of the parameter `period / 4` stays on the arc branch
of the chamfered loop. -/
lemma sweepParam_quarter_sub_le {δ₁ u : ℝ} (hδ₁0 : 0 ≤ δ₁) (hδ₁4 : δ₁ ≤ period / 4)
    (hu : u ∈ Set.Icc (-1 : ℝ) 1) : sweepParam (period / 4 - δ₁ * u) ≤ 1 / 2 := by
  have hp : (0 : ℝ) < period := period_pos
  have h0 : 0 ≤ period / 4 - δ₁ * u := by nlinarith [hδ₁0, hδ₁4, hu.1, hu.2, hp]
  have h1 : period / 4 - δ₁ * u < period := by nlinarith [hδ₁0, hδ₁4, hu.1, hu.2, hp]
  rw [sweepParam_eq_div_of_mem' h0 h1, div_le_iff₀ hp]
  nlinarith [hδ₁0, hδ₁4, hu.1, hu.2, hp]

/-- The arc fraction at the middle of the arc window stays strictly inside `(0,1)`. -/
lemma arcFrac_quarter_mem_Ioo {lam δ₁ u : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1 / 2)
    (hδ₁0 : 0 ≤ δ₁) (hδ₁4 : δ₁ ≤ period / 4) (hu : u ∈ Set.Icc (-1 : ℝ) 1) :
    arcFrac lam δ₁ (period / 4) u ∈ Set.Ioo (0 : ℝ) 1 := by
  have h0 : 0 ≤ sweepParam (period / 4 - δ₁ * u) := (sweepParam_mem _).1
  have h1 : sweepParam (period / 4 - δ₁ * u) ≤ 1 / 2 :=
    sweepParam_quarter_sub_le hδ₁0 hδ₁4 hu
  have hξ : arcFrac lam δ₁ (period / 4) u
      = lam + (1 - 2 * lam) * (2 * sweepParam (period / 4 - δ₁ * u)) := rfl
  constructor
  · rw [hξ]; nlinarith [h0, h1, hlam0, hlam1]
  · rw [hξ]; nlinarith [h0, h1, hlam0, hlam1]

/-! ## The main statement -/

/-- **The base point of the shifted needle is off the chord's line**, for a knot without
inflections.  This discharges the `hnotseg` input of
`Work.Drive.needleShiftedChartPin_of_parts`. -/
theorem needleShiftedNotOnLine_of_infl {r : ℝ → Space} (hr : IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t])
    {d : BandArcData} (D : SweepData d) : NeedleShiftedNotOnLine r D := by
  obtain ⟨e₀, he₀n, he₀orth, he₀pos⟩ :=
    exists_secondDerivDir_of_linearIndependent (hinfl (taR D 0))
  have hTne : deriv r (taR D 0) ≠ 0 := hr.regular (taR D 0)
  obtain ⟨δ, hδ0, hδspec⟩ :=
    exists_secondDeriv_halfspace hr hTne ⟨e₀, he₀n, he₀orth, he₀pos⟩
  obtain ⟨ε₁, hε₁0, -, hwds⟩ := windowDataSmall hr D δ hδ0
  refine ⟨min ε₁ (1 / 2), period / 4, lt_min hε₁0 (by norm_num),
    by have h := period_pos; linarith, ?_⟩
  intro lam δ₁ δ₂ ε hlam0 hlamL hlam1 hδ₁0 hδ₁L hδ₂0 hδ₂L hε0 hεε₀ hδ₂ε
  have hεε₁ : ε ≤ ε₁ := le_trans hεε₀ (min_le_left _ _)
  have hε12 : ε ≤ 1 / 2 := le_trans hεε₀ (min_le_right _ _)
  have hδ₁4 : δ₁ ≤ period / 4 := hδ₁L
  have hδ₁per : δ₁ < period / 2 := by have h := period_pos; linarith
  obtain ⟨hrange, hchordne, hdir⟩ := hwds δ₂ ε hδ₂0 hδ₂ε hε0 hεε₁
  set V : Space := chordEndB r D δ₂ ε - chordEndA r D δ₂ ε with hVdef
  set u : Space := ‖V‖⁻¹ • V with hudef
  have hVne : V ≠ 0 := by rw [hVdef]; exact sub_ne_zero.mpr hchordne
  have hunorm : ‖u‖ = 1 := by rw [hudef]; exact norm_smul_inv_norm hVne
  have hα : |(taR D 0 - δ) - taR D 0| ≤ δ := by
    rw [show (taR D 0 - δ) - taR D 0 = -δ from by ring, abs_neg, abs_of_pos hδ0]
  have hβ : |(taR D 0 + δ) - taR D 0| ≤ δ := by
    rw [show (taR D 0 + δ) - taR D 0 = δ from by ring, abs_of_pos hδ0]
  obtain ⟨e, -, heu, heacc⟩ :=
    hδspec u hunorm hdir (taR D 0 - δ) (taR D 0 + δ) hα hβ
  have hVeq : V = ‖V‖ • u := by
    rw [hudef, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hVne), one_smul]
  have hnV : inner ℝ e (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε) = 0 := by
    rw [← hVdef, hVeq, inner_smul_right, heu, mul_zero]
  have hnVo : inner ℝ (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε) e = 0 := by
    rw [real_inner_comm]; exact hnV
  -- the acceleration is strictly transverse on the whole window
  have haccS : ∀ σ ∈ Set.Icc (ε - δ₂) (ε + δ₂), ∀ u' ∈ Set.Icc (0 : ℝ) 1,
      inner ℝ e (deriv (deriv r) (taR D σ + u' * sweepW' D σ)) < 0 := by
    intro σ hσ u' hu'
    have hx := abs_le.mp (hrange σ hσ.1 hσ.2 u' hu'.1 hu'.2)
    exact heacc _ (by linarith [hx.1]) (by linarith [hx.2])
  have hvon : ∀ σ ∈ Set.Icc (ε - δ₂) (ε + δ₂), 0 < sweepW' D σ := by
    intro σ hσ
    refine wds_sweepW'_pos D ?_ ?_
    · linarith [hσ.1, hδ₂ε, hε0]
    · linarith [hσ.2, hδ₂ε, hε12]
  have hpos : ∀ v ∈ Set.Icc (-1 : ℝ) 1, ∀ u' ∈ Set.Icc (-1 : ℝ) 1,
      0 < inner ℝ (loopDev r D (ε - δ₂ * v) (arcFrac lam δ₁ (period / 4) u')) e := by
    intro v hv u' hu'
    have hσ : ε - δ₂ * v ∈ Set.Icc (ε - δ₂) (ε + δ₂) := by
      constructor
      · have h : δ₂ * v ≤ δ₂ := by nlinarith [hv.2, hδ₂0]
        linarith
      · have h : -δ₂ ≤ δ₂ * v := by nlinarith [hv.1, hδ₂0]
        linarith
    have harc := arcFrac_quarter_mem_Ioo hlam0 hlam1 hδ₁0.le hδ₁4 hu'
    have h := loopDev_pos_of_halfspace hr D (hvon _ hσ)
      (fun u'' hu'' => by
        simpa only [velocity_eq_deriv_fn] using (haccS (ε - δ₂ * v) hσ u'' hu'').le)
      ⟨1 / 2, by norm_num, by
        simpa only [velocity_eq_deriv_fn] using haccS (ε - δ₂ * v) hσ (1 / 2) ⟨by norm_num, by norm_num⟩⟩ harc
    rwa [real_inner_comm] at h
  have hzone : ∀ u' ∈ Set.Icc (-1 : ℝ) 1, sweepParam (period / 4 - δ₁ * u') ≤ 1 / 2 :=
    fun u' hu' => sweepParam_quarter_sub_le hδ₁0.le hδ₁4 hu'
  have hmain := needleFam_inner_pos_of_pointwise (t := period / 4) hr.smooth.continuous D
    hlam1 hδ₁0 hδ₁per hzone hpos hnVo
  intro s
  exact ne_chordSegment_of_height_pos hnV hmain

/-- **The chart pin from the angular-velocity clause alone** (the base-point clause is proved
above). -/
theorem needleShiftedChartPin_of_angVel {r : ℝ → Space} (hr : IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t])
    {d : BandArcData} (D : SweepData d)
    (havoid : ∀ s : Set.Icc (0 : ℝ) 1, ∀ (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1),
      mobiusCover ⟨(d.a s, d.b s), d.offdiag s hs0 hs1⟩ ∉ trisecantSet r)
    (hang : NeedleShiftedAngVel r D) : NeedleShiftedChartPin r D havoid :=
  needleShiftedChartPin_of_parts hr D havoid (needleShiftedNotOnLine_of_infl hr hinfl D) hang

end Work.Drive
