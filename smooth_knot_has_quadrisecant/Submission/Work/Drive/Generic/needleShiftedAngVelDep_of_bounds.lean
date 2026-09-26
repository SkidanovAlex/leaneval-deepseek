import Mathlib
import Submission.Work.Drive.AB.pinBounds
import Submission.Work.Drive.AB.pinInterface
import Submission.Work.Drive.Generic.doubleAverageData_of_jointly_measurable
import Submission.Work.Drive.Generic.const_le_diagIntegral_of_data

namespace Work.Drive.Generic

open LeanEval.KnotTheory.Quadrisecant MeasureTheory
open scoped Real Topology intervalIntegral

/-! ## The chart algebra of the needle's angular-velocity pin

The chart of `Work.Drive.chartC` / `Work.Drive.chartE`: the centre `c'` is the needle's base point
`shiftedNeedle 0` lowered by half its height above the chord's *line*, and `e = chartE` is the unit
"up" direction.  The elementary facts below convert the pin's expression into the coordinates of the
needle about `c'`, which is the form in which `Work.Drive.needle_num_pos_of_diag_osc` is applied. -/

noncomputable section
namespace AngVelDep

variable {r : ℝ → Space} {d : BandArcData} {D : Work.Drive.SweepData d}
variable {lam δ₁ δ₂ ε : ℝ} {v : Space}

/-- `chartE` is a unit vector whenever `chartUp ≠ 0`. -/
lemma norm_chartE (hw : chartUp r D lam δ₁ δ₂ ε v ≠ 0) :
    ‖chartE r D lam δ₁ δ₂ ε v‖ = 1 := by
  rw [chartE, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)]

/-- The chart's "up" direction is perpendicular to the chord direction. -/
lemma inner_v_chartE (hv : ‖v‖ = 1) : inner ℝ v (chartE r D lam δ₁ δ₂ ε v) = 0 := by
  rw [chartE, real_inner_smul_right, real_inner_comm (chartUp r D lam δ₁ δ₂ ε v) v,
    inner_chartUp_v r D lam δ₁ δ₂ ε hv, mul_zero]

/-- `chartE` has unit length, in inner-product form. -/
lemma inner_chartE_self (hw : chartUp r D lam δ₁ δ₂ ε v ≠ 0) :
    inner ℝ (chartE r D lam δ₁ δ₂ ε v) (chartE r D lam δ₁ δ₂ ε v) = 1 := by
  rw [real_inner_self_eq_norm_sq, norm_chartE hw]; norm_num

/-- The base point's height above the chord's line, in the direction `chartE`, is `‖chartUp‖`. -/
lemma nHeight_chartE_zero (hv : ‖v‖ = 1) :
    nHeight r D lam δ₁ δ₂ ε (chartE r D lam δ₁ δ₂ ε v) 0 = ‖chartUp r D lam δ₁ δ₂ ε v‖ := by
  rw [nHeight, chartE]
  exact inner_smul_unit_of_inner_eq _ _ (inner_shiftedNeedle_chartUp r D lam δ₁ δ₂ ε hv)

/-- The `chartE`-coordinate of the needle about the chart centre. -/
lemma inner_chartC_chartE (hv : ‖v‖ = 1) (hw : chartUp r D lam δ₁ δ₂ ε v ≠ 0) (t : ℝ) :
    inner ℝ (shiftedNeedle r D lam δ₁ δ₂ ε t - chartC r D lam δ₁ δ₂ ε v)
        (chartE r D lam δ₁ δ₂ ε v)
      = nHeight r D lam δ₁ δ₂ ε (chartE r D lam δ₁ δ₂ ε v) t
        - ‖chartUp r D lam δ₁ δ₂ ε v‖ / 2 := by
  rw [chartC, nHeight, inner_sub_left, inner_add_left, inner_add_left,
    real_inner_smul_left, real_inner_smul_left, inner_v_chartE hv, inner_chartE_self hw]
  simp only [inner_sub_left]
  ring

/-- The chord coordinate of the needle about the chart centre. -/
lemma inner_chartC_v (hv : ‖v‖ = 1) (t : ℝ) :
    inner ℝ (shiftedNeedle r D lam δ₁ δ₂ ε t - chartC r D lam δ₁ δ₂ ε v) v
      = nCoord r D lam δ₁ δ₂ ε v t - nCoord r D lam δ₁ δ₂ ε v 0 := by
  rw [chartC, nCoord, inner_sub_left, inner_add_left, inner_add_left,
    real_inner_smul_left, real_inner_smul_left, real_inner_self_eq_norm_sq v, hv,
    real_inner_comm v (chartE r D lam δ₁ δ₂ ε v), inner_v_chartE hv]
  simp only [nCoord, inner_sub_left]
  ring

/-- A chart coordinate about `chartC` and the corresponding one about `chordEndA` differ by a
constant, hence have the same derivative. -/
lemma deriv_sub_const_chart (f : ℝ → Space) (c' A e : Space) (t : ℝ) :
    deriv (fun t' : ℝ => inner ℝ (f t' - c') e) t
      = deriv (fun t' : ℝ => inner ℝ (f t' - A) e) t := by
  have h1 : (fun t' : ℝ => inner ℝ (f t' - c') e)
      = fun t' => inner ℝ (f t') e - inner ℝ c' e := by
    funext t'; rw [inner_sub_left]
  have h2 : (fun t' : ℝ => inner ℝ (f t' - A) e)
      = fun t' => inner ℝ (f t') e - inner ℝ A e := by
    funext t'; rw [inner_sub_left]
  rw [h1, h2, deriv_sub_const, deriv_sub_const]

/-- **The `u`-coordinate of the raw chamfered loop over the blur window**, as a function of the two
window parameters `(a, b)`: the loop is evaluated at sweep parameter `ε - δ₂ a` and loop parameter
`t + period/4 - δ₁ b`, and the coordinate is taken about `c'` along `u`.

The first window parameter is the *sweep* parameter (`δ₂`) and the second the *loop* parameter
(`δ₁`): this is the order in which `Work.Drive.inner_shiftedNeedle_eq_doubleAverage` produces the
double average, so that the averaged coordinate is the asserted double integral without a Fubini
exchange. -/
def winCoord (r : ℝ → Space) {d : BandArcData} (D : Work.Drive.SweepData d) (lam δ₁ δ₂ ε : ℝ)
    (c' u : Space) (t : ℝ) : ℝ → ℝ → ℝ :=
  fun a b => inner ℝ (sweepLoopChamfer r D lam (ε - δ₂ * a) (t + period / 4 - δ₁ * b) - c') u

/-- **The `u`-coordinate of the loop velocity over the blur window.** -/
def winVel (r : ℝ → Space) {d : BandArcData} (D : Work.Drive.SweepData d) (lam δ₁ δ₂ ε : ℝ)
    (u : Space) (t : ℝ) : ℝ → ℝ → ℝ :=
  fun a b => inner ℝ (chamferVel r D lam (ε - δ₂ * a) (t + period / 4 - δ₁ * b)) u

end AngVelDep
open AngVelDep

set_option maxHeartbeats 1000000

/-- **The angular-velocity pin of the needle from the two chart bounds.**  The per-loop margin
`Work.Drive.ChartLoopMargin` (the geometric heart) and the oscillation bounds
`Work.Drive.ChartOscBounds` of the loop coordinates over the blur window, together with the
double-average interface of the needle's chart coordinates and their derivatives, give
`Work.Drive.NeedleShiftedAngVelDep` — the assembly `Work.Drive.needle_num_pos_of_diag_osc` applied
at every `t`.

The derivative interface is taken as a hypothesis so that this module does not depend on the module
proving it (`Work.Drive.Generic.shiftedNeedle_deriv_eq_doubleAverage`), which imports this vocabulary
but is proved separately; the *coordinate* interface is the proved
`Work.Drive.inner_shiftedNeedle_eq_doubleAverage` of `Submission/Work/Drive/AB/pinInterface.lean`. -/
theorem needleShiftedAngVelDep_of_bounds {r : ℝ → Space} (hr : IsSmoothKnot r)
    {d : BandArcData} (D : Work.Drive.SweepData d)
    (hderiv : ∀ {lam δ₁ δ₂ ε : ℝ}, 0 < lam → lam < 1 / 2 → δ₁ ≠ 0 → 0 < δ₂ →
      0 < ε - δ₂ → ε + δ₂ < 1 → ∀ (c' u : Space) (t : ℝ),
      deriv (fun t' : ℝ => inner ℝ (Work.Drive.shiftedNeedle r D lam δ₁ δ₂ ε t' - c') u) t
        = ∫ v' in (-1 : ℝ)..1, ∫ s in (-1 : ℝ)..1,
            Work.Drive.sweepBump v' * Work.Drive.sweepBump s *
              inner ℝ (Work.Drive.chamferVel r D lam (ε - δ₂ * v')
                (t + period / 4 - δ₁ * s)) u)
    (hmargin : Work.Drive.ChartLoopMargin r D) (hosc : Work.Drive.ChartOscBounds r D) :
    Work.Drive.NeedleShiftedAngVelDep r D := by
  obtain ⟨εm, hεm, hm⟩ := hmargin
  obtain ⟨εo, hεo, ho⟩ := hosc
  obtain ⟨m, M, C₂, hm0, hM0, hC₂, hmin, hmax, hlip⟩ := exists_knot_c2_bounds hr
  obtain ⟨R, hR0, hR⟩ := wideEnd_knot_bounded hr.continuous hr.periodic
  refine ⟨min (min εm εo) (1 / 2), lt_min (lt_min hεm hεo) (by norm_num), ?_⟩
  intro ε hε0 hεε₀
  have hεm' : ε ≤ εm := le_trans hεε₀ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hεo' : ε ≤ εo := le_trans hεε₀ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hεhalf : ε ≤ 1 / 2 := le_trans hεε₀ (min_le_right _ _)
  obtain ⟨Λm, hΛm, κ, hκ, hmκ⟩ := hm ε hε0 hεm'
  obtain ⟨Λo, hΛo, hoκ⟩ := ho ε hε0 hεo' κ hκ
  refine ⟨min Λm Λo, lt_min hΛm hΛo, ?_⟩
  intro lam δ₁ δ₂ hlam0 hlamΛ hlam12 hδ10 hδ1Λ hδ20 hδ2Λ hδ2ε
  have hlamΛm : lam ≤ Λm := le_trans hlamΛ (min_le_left _ _)
  have hlamΛo : lam ≤ Λo := le_trans hlamΛ (min_le_right _ _)
  have hδ1Λm : δ₁ ≤ Λm := le_trans hδ1Λ (min_le_left _ _)
  have hδ1Λo : δ₁ ≤ Λo := le_trans hδ1Λ (min_le_right _ _)
  have hδ2Λm : δ₂ ≤ Λm := le_trans hδ2Λ (min_le_left _ _)
  have hδ2Λo : δ₂ ≤ Λo := le_trans hδ2Λ (min_le_right _ _)
  have hσlo : 0 < ε - δ₂ := by linarith
  have hσhi : ε + δ₂ < 1 := by linarith
  have hσ1 : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ε - δ₂ ≤ ε - δ₂ * u := fun u hu => by
    have h := mul_le_mul_of_nonneg_left hu.2 hδ20.le
    linarith
  have hσ2 : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ε - δ₂ * u ≤ ε + δ₂ := fun u hu => by
    have h := mul_le_mul_of_nonneg_left hu.1 hδ20.le
    linarith
  -- the retained arc's width is bounded by one period, for every sweep parameter
  have hWglobal : ∀ σ : ℝ, |sweepW' D σ| ≤ period := by
    intro σ
    by_cases h : σ ≤ 0
    · have hc : clampI σ = 0 := by
        apply Subtype.ext
        simp only [clampI, max_eq_left h, min_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
        norm_num
      rw [show sweepW' D σ = sweepW D (clampI σ) from rfl, hc, sweepW_zero, abs_zero]
      exact period_pos.le
    · have hpos : 0 < σ := not_le.mp h
      by_cases h' : 1 ≤ σ
      · have hc : clampI σ = 1 := by
          apply Subtype.ext
          simp only [clampI, max_eq_right hpos.le, min_eq_left h']
          norm_num
        rw [show sweepW' D σ = sweepW D (clampI σ) from rfl, hc, sweepW_one,
          abs_of_pos period_pos]
      · have hlt1 : σ < 1 := not_le.mp h'
        obtain ⟨hp, hlt⟩ :=
          sweepW_pos_lt D (⟨σ, ⟨hpos.le, hlt1.le⟩⟩ : Set.Icc (0 : ℝ) 1) ⟨hpos, hlt1⟩
        have hc : clampI σ = ⟨σ, ⟨hpos.le, hlt1.le⟩⟩ := by
          apply Subtype.ext
          simp only [clampI]
          rw [max_eq_right hpos.le, min_eq_right hlt1.le]
        rw [show sweepW' D σ = sweepW D (clampI σ) from rfl, hc, abs_of_pos hp]
        exact hlt.le
  have hvelglob : ∀ σ s : ℝ, ‖chamferVel r D lam σ s‖ ≤ doubleBlurLam lam M R period :=
    fun σ s => doubleBlur_chamferVel_bound hlam0 hlam12 hmax hR period_pos.le σ (hWglobal σ) s
  intro v hv hV t
  by_cases hw : chartUp r D lam δ₁ δ₂ ε v = 0
  · exfalso
    have he0 : chartE r D lam δ₁ δ₂ ε v = 0 := by
      rw [chartE, hw, norm_zero, inv_zero, zero_smul]
    have h := hmκ lam δ₁ δ₂ hlam0 hlamΛm hlam12 hδ10 hδ1Λm hδ20 hδ2Λm hδ2ε v hv hV ε 0
      (by linarith) (by linarith)
    rw [he0] at h
    simp only [inner_zero_right, mul_zero, zero_mul, sub_zero] at h
    linarith
  have hN0 : nHeight r D lam δ₁ δ₂ ε (chartE r D lam δ₁ δ₂ ε v) 0
      = ‖chartUp r D lam δ₁ δ₂ ε v‖ := nHeight_chartE_zero hv
  obtain ⟨A, B, A', B', hA0, hB0, hA'0, hB'0, hlt, hoscA, hoscB, hoscA', hoscB'⟩ :=
    hoκ lam δ₁ δ₂ hlam0 hlamΛo hlam12 hδ10 hδ1Λo hδ20 hδ2Λo hδ2ε v hv hV
  -- joint measurability of the four window functions
  have hmap : Measurable fun p : ℝ × ℝ => (ε - δ₂ * p.1, t + period / 4 - δ₁ * p.2) := by fun_prop
  have hmes_loop : Measurable fun p : ℝ × ℝ =>
      sweepLoopChamfer r D lam (ε - δ₂ * p.1) (t + period / 4 - δ₁ * p.2) :=
    (sweepLoopChamfer_measurable D hr.continuous lam).comp hmap
  have hmes_vel : Measurable fun p : ℝ × ℝ =>
      chamferVel r D lam (ε - δ₂ * p.1) (t + period / 4 - δ₁ * p.2) :=
    (wideEnd_measurable_chamferVel_joint hr.continuous (hr.smooth.continuous_deriv (by simp)) D lam).comp hmap
  have hfm : Measurable fun p : ℝ × ℝ =>
      winCoord r D lam δ₁ δ₂ ε (chartC r D lam δ₁ δ₂ ε v) (chartE r D lam δ₁ δ₂ ε v) t p.1 p.2 := by
    show Measurable fun p : ℝ × ℝ => inner ℝ
      (sweepLoopChamfer r D lam (ε - δ₂ * p.1) (t + period / 4 - δ₁ * p.2)
        - chartC r D lam δ₁ δ₂ ε v) (chartE r D lam δ₁ δ₂ ε v)
    exact (hmes_loop.sub measurable_const).inner measurable_const
  have hgm : Measurable fun p : ℝ × ℝ => winVel r D lam δ₁ δ₂ ε v t p.1 p.2 := by
    show Measurable fun p : ℝ × ℝ => inner ℝ
      (chamferVel r D lam (ε - δ₂ * p.1) (t + period / 4 - δ₁ * p.2)) v
    exact hmes_vel.inner measurable_const
  have hfm₂ : Measurable fun p : ℝ × ℝ =>
      winCoord r D lam δ₁ δ₂ ε (chartC r D lam δ₁ δ₂ ε v) v t p.1 p.2 := by
    show Measurable fun p : ℝ × ℝ => inner ℝ
      (sweepLoopChamfer r D lam (ε - δ₂ * p.1) (t + period / 4 - δ₁ * p.2)
        - chartC r D lam δ₁ δ₂ ε v) v
    exact (hmes_loop.sub measurable_const).inner measurable_const
  have hgm₂ : Measurable fun p : ℝ × ℝ =>
      winVel r D lam δ₁ δ₂ ε (chartE r D lam δ₁ δ₂ ε v) t p.1 p.2 := by
    show Measurable fun p : ℝ × ℝ => inner ℝ
      (chamferVel r D lam (ε - δ₂ * p.1) (t + period / 4 - δ₁ * p.2))
      (chartE r D lam δ₁ δ₂ ε v)
    exact hmes_vel.inner measurable_const
  -- the bounds on the window
  have hfbd : ∀ u : ℝ, ∀ v' ∈ Set.Icc (-1 : ℝ) 1,
      |winCoord r D lam δ₁ δ₂ ε (chartC r D lam δ₁ δ₂ ε v) (chartE r D lam δ₁ δ₂ ε v) t u v'|
        ≤ (R + ‖chartC r D lam δ₁ δ₂ ε v‖) * ‖chartE r D lam δ₁ δ₂ ε v‖ := by
    intro u v' hv'
    simp only [winCoord]
    have hloop : ‖sweepLoopChamfer r D lam (ε - δ₂ * u) (t + period / 4 - δ₁ * v')‖ ≤ R :=
      sweepLoopChamfer_norm_le hR hlam0 hlam12 _ _
    calc |inner ℝ (sweepLoopChamfer r D lam (ε - δ₂ * u) (t + period / 4 - δ₁ * v')
            - chartC r D lam δ₁ δ₂ ε v) (chartE r D lam δ₁ δ₂ ε v)|
        ≤ ‖sweepLoopChamfer r D lam (ε - δ₂ * u) (t + period / 4 - δ₁ * v')
            - chartC r D lam δ₁ δ₂ ε v‖ * ‖chartE r D lam δ₁ δ₂ ε v‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ (R + ‖chartC r D lam δ₁ δ₂ ε v‖) * ‖chartE r D lam δ₁ δ₂ ε v‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          refine (norm_sub_le _ _).trans ?_
          linarith [hloop]
  have hgbd : ∀ u : ℝ, ∀ v' ∈ Set.Icc (-1 : ℝ) 1,
      |winVel r D lam δ₁ δ₂ ε v t u v'| ≤ doubleBlurLam lam M R period * ‖v‖ := by
    intro u v' hv'
    simp only [winVel]
    calc |inner ℝ (chamferVel r D lam (ε - δ₂ * u) (t + period / 4 - δ₁ * v')) v|
        ≤ ‖chamferVel r D lam (ε - δ₂ * u) (t + period / 4 - δ₁ * v')‖ * ‖v‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ doubleBlurLam lam M R period * ‖v‖ :=
          mul_le_mul_of_nonneg_right (hvelglob (ε - δ₂ * u) _) (norm_nonneg _)
  have hfbd₂ : ∀ u : ℝ, ∀ v' ∈ Set.Icc (-1 : ℝ) 1,
      |winCoord r D lam δ₁ δ₂ ε (chartC r D lam δ₁ δ₂ ε v) v t u v'|
        ≤ (R + ‖chartC r D lam δ₁ δ₂ ε v‖) * ‖v‖ := by
    intro u v' hv'
    simp only [winCoord]
    have hloop : ‖sweepLoopChamfer r D lam (ε - δ₂ * u) (t + period / 4 - δ₁ * v')‖ ≤ R :=
      sweepLoopChamfer_norm_le hR hlam0 hlam12 _ _
    calc |inner ℝ (sweepLoopChamfer r D lam (ε - δ₂ * u) (t + period / 4 - δ₁ * v')
            - chartC r D lam δ₁ δ₂ ε v) v|
        ≤ ‖sweepLoopChamfer r D lam (ε - δ₂ * u) (t + period / 4 - δ₁ * v')
            - chartC r D lam δ₁ δ₂ ε v‖ * ‖v‖ := abs_real_inner_le_norm _ _
      _ ≤ (R + ‖chartC r D lam δ₁ δ₂ ε v‖) * ‖v‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          refine (norm_sub_le _ _).trans ?_
          linarith [hloop]
  have hgbd₂ : ∀ u : ℝ, ∀ v' ∈ Set.Icc (-1 : ℝ) 1,
      |winVel r D lam δ₁ δ₂ ε (chartE r D lam δ₁ δ₂ ε v) t u v'|
        ≤ doubleBlurLam lam M R period * ‖chartE r D lam δ₁ δ₂ ε v‖ := by
    intro u v' hv'
    simp only [winVel]
    calc |inner ℝ (chamferVel r D lam (ε - δ₂ * u) (t + period / 4 - δ₁ * v'))
            (chartE r D lam δ₁ δ₂ ε v)|
        ≤ ‖chamferVel r D lam (ε - δ₂ * u) (t + period / 4 - δ₁ * v')‖
            * ‖chartE r D lam δ₁ δ₂ ε v‖ := abs_real_inner_le_norm _ _
      _ ≤ doubleBlurLam lam M R period * ‖chartE r D lam δ₁ δ₂ ε v‖ :=
          mul_le_mul_of_nonneg_right (hvelglob (ε - δ₂ * u) _) (norm_nonneg _)
  have hd1 : Work.Drive.DoubleAverageData sweepBump
      (winCoord r D lam δ₁ δ₂ ε (chartC r D lam δ₁ δ₂ ε v) (chartE r D lam δ₁ δ₂ ε v) t)
      (winVel r D lam δ₁ δ₂ ε v t) :=
    doubleAverageData_of_jointly_measurable sweepBump_continuous (fun u => abs_sweepBump_le_one_local u)
      hfm hgm hfbd hgbd
  have hd2 : Work.Drive.DoubleAverageData sweepBump
      (winCoord r D lam δ₁ δ₂ ε (chartC r D lam δ₁ δ₂ ε v) v t)
      (winVel r D lam δ₁ δ₂ ε (chartE r D lam δ₁ δ₂ ε v) t) :=
    doubleAverageData_of_jointly_measurable sweepBump_continuous (fun u => abs_sweepBump_le_one_local u)
      hfm₂ hgm₂ hfbd₂ hgbd₂
  -- the diagonal
  have hdiag : κ ≤ ∫ u in (-1 : ℝ)..1, ∫ v' in (-1 : ℝ)..1,
      sweepBump u * sweepBump v' *
        (winCoord r D lam δ₁ δ₂ ε (chartC r D lam δ₁ δ₂ ε v) (chartE r D lam δ₁ δ₂ ε v) t u v'
          * winVel r D lam δ₁ δ₂ ε v t u v'
          - winCoord r D lam δ₁ δ₂ ε (chartC r D lam δ₁ δ₂ ε v) v t u v'
            * winVel r D lam δ₁ δ₂ ε (chartE r D lam δ₁ δ₂ ε v) t u v') :=
    const_le_diagIntegral_of_data sweepBump_continuous sweepBump_nonneg sweepBump_integral hd1 hd2
      (fun u hu v' hv' => by
        simp only [winCoord, winVel]
        exact hmκ lam δ₁ δ₂ hlam0 hlamΛm hlam12 hδ10 hδ1Λm hδ20 hδ2Λm hδ2ε v hv hV
          (ε - δ₂ * u) (t + period / 4 - δ₁ * v') (hσ1 u hu) (hσ2 u hu))
  -- the oscillations
  have hA : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ∀ v' ∈ Set.Icc (-1 : ℝ) 1,
      ∀ u' ∈ Set.Icc (-1 : ℝ) 1, ∀ v₂ ∈ Set.Icc (-1 : ℝ) 1,
      |winCoord r D lam δ₁ δ₂ ε (chartC r D lam δ₁ δ₂ ε v) (chartE r D lam δ₁ δ₂ ε v) t u v'
        - winCoord r D lam δ₁ δ₂ ε (chartC r D lam δ₁ δ₂ ε v) (chartE r D lam δ₁ δ₂ ε v) t u' v₂|
        ≤ A :=
    fun u hu v' hv' u' hu' v₂ hv₂ => by
      simpa only [winCoord] using hoscA t v' hv' u hu v₂ hv₂ u' hu'
  have hB : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ∀ v' ∈ Set.Icc (-1 : ℝ) 1,
      ∀ u' ∈ Set.Icc (-1 : ℝ) 1, ∀ v₂ ∈ Set.Icc (-1 : ℝ) 1,
      |winCoord r D lam δ₁ δ₂ ε (chartC r D lam δ₁ δ₂ ε v) v t u v'
        - winCoord r D lam δ₁ δ₂ ε (chartC r D lam δ₁ δ₂ ε v) v t u' v₂| ≤ B :=
    fun u hu v' hv' u' hu' v₂ hv₂ => by
      simpa only [winCoord] using hoscB t v' hv' u hu v₂ hv₂ u' hu'
  have hA' : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ∀ v' ∈ Set.Icc (-1 : ℝ) 1,
      ∀ u' ∈ Set.Icc (-1 : ℝ) 1, ∀ v₂ ∈ Set.Icc (-1 : ℝ) 1,
      |winVel r D lam δ₁ δ₂ ε (chartE r D lam δ₁ δ₂ ε v) t u v'
        - winVel r D lam δ₁ δ₂ ε (chartE r D lam δ₁ δ₂ ε v) t u' v₂| ≤ A' :=
    fun u hu v' hv' u' hu' v₂ hv₂ => by
      simpa only [winVel] using hoscA' t v' hv' u hu v₂ hv₂ u' hu'
  have hB' : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ∀ v' ∈ Set.Icc (-1 : ℝ) 1,
      ∀ u' ∈ Set.Icc (-1 : ℝ) 1, ∀ v₂ ∈ Set.Icc (-1 : ℝ) 1,
      |winVel r D lam δ₁ δ₂ ε v t u v' - winVel r D lam δ₁ δ₂ ε v t u' v₂| ≤ B' :=
    fun u hu v' hv' u' hu' v₂ hv₂ => by
      simpa only [winVel] using hoscB' t v' hv' u hu v₂ hv₂ u' hu'
  have hnum := needle_num_pos_of_diag_osc (b := sweepBump)
    (α := winCoord r D lam δ₁ δ₂ ε (chartC r D lam δ₁ δ₂ ε v) (chartE r D lam δ₁ δ₂ ε v) t)
    (β := winCoord r D lam δ₁ δ₂ ε (chartC r D lam δ₁ δ₂ ε v) v t)
    (α' := winVel r D lam δ₁ δ₂ ε (chartE r D lam δ₁ δ₂ ε v) t)
    (β' := winVel r D lam δ₁ δ₂ ε v t)
    (A := A) (B := B) (A' := A') (B' := B') (κ := κ)
    sweepBump_continuous sweepBump_nonneg sweepBump_integral hd1 hd2 hA hB hA' hB' hdiag hlt
  -- the four double-average interfaces
  have hP : (∫ u in (-1 : ℝ)..1, sweepBump u * ∫ v' in (-1 : ℝ)..1,
        sweepBump v' * winCoord r D lam δ₁ δ₂ ε (chartC r D lam δ₁ δ₂ ε v)
          (chartE r D lam δ₁ δ₂ ε v) t u v')
      = inner ℝ (shiftedNeedle r D lam δ₁ δ₂ ε t - chartC r D lam δ₁ δ₂ ε v)
          (chartE r D lam δ₁ δ₂ ε v) := by
    have h1 := diag_integral_eq sweepBump
      (winCoord r D lam δ₁ δ₂ ε (chartC r D lam δ₁ δ₂ ε v) (chartE r D lam δ₁ δ₂ ε v) t)
      (fun _ _ => (1 : ℝ))
    simp only [mul_one] at h1
    exact h1.trans (inner_shiftedNeedle_eq_doubleAverage hr D hlam0 hlam12
      (chartC r D lam δ₁ δ₂ ε v) (chartE r D lam δ₁ δ₂ ε v) t).symm
  have hQ : (∫ u in (-1 : ℝ)..1, sweepBump u * ∫ v' in (-1 : ℝ)..1,
        sweepBump v' * winCoord r D lam δ₁ δ₂ ε (chartC r D lam δ₁ δ₂ ε v) v t u v')
      = inner ℝ (shiftedNeedle r D lam δ₁ δ₂ ε t - chartC r D lam δ₁ δ₂ ε v) v := by
    have h1 := diag_integral_eq sweepBump
      (winCoord r D lam δ₁ δ₂ ε (chartC r D lam δ₁ δ₂ ε v) v t) (fun _ _ => (1 : ℝ))
    simp only [mul_one] at h1
    exact h1.trans (inner_shiftedNeedle_eq_doubleAverage hr D hlam0 hlam12
      (chartC r D lam δ₁ δ₂ ε v) v t).symm
  have hPa : (∫ u in (-1 : ℝ)..1, sweepBump u * ∫ v' in (-1 : ℝ)..1,
        sweepBump v' * winVel r D lam δ₁ δ₂ ε (chartE r D lam δ₁ δ₂ ε v) t u v')
      = deriv (fun t' : ℝ => inner ℝ (shiftedNeedle r D lam δ₁ δ₂ ε t'
          - chartC r D lam δ₁ δ₂ ε v) (chartE r D lam δ₁ δ₂ ε v)) t := by
    have h1 := diag_integral_eq sweepBump
      (winVel r D lam δ₁ δ₂ ε (chartE r D lam δ₁ δ₂ ε v) t) (fun _ _ => (1 : ℝ))
    simp only [mul_one] at h1
    exact h1.trans (hderiv hlam0 hlam12 (ne_of_gt hδ10) hδ20 hσlo hσhi
      (chartC r D lam δ₁ δ₂ ε v) (chartE r D lam δ₁ δ₂ ε v) t).symm
  have hQb : (∫ u in (-1 : ℝ)..1, sweepBump u * ∫ v' in (-1 : ℝ)..1,
        sweepBump v' * winVel r D lam δ₁ δ₂ ε v t u v')
      = deriv (fun t' : ℝ => inner ℝ (shiftedNeedle r D lam δ₁ δ₂ ε t'
          - chartC r D lam δ₁ δ₂ ε v) v) t := by
    have h1 := diag_integral_eq sweepBump (winVel r D lam δ₁ δ₂ ε v t) (fun _ _ => (1 : ℝ))
    simp only [mul_one] at h1
    exact h1.trans (hderiv hlam0 hlam12 (ne_of_gt hδ10) hδ20 hσlo hσhi
      (chartC r D lam δ₁ δ₂ ε v) v t).symm
  -- the chart conversion
  have hPe : inner ℝ (shiftedNeedle r D lam δ₁ δ₂ ε t - chartC r D lam δ₁ δ₂ ε v)
        (chartE r D lam δ₁ δ₂ ε v)
      = nHeight r D lam δ₁ δ₂ ε (chartE r D lam δ₁ δ₂ ε v) t
        - nHeight r D lam δ₁ δ₂ ε (chartE r D lam δ₁ δ₂ ε v) 0
        + ‖chartUp r D lam δ₁ δ₂ ε v‖ / 2 := by
    rw [inner_chartC_chartE (t := t) hv hw, hN0]
    ring
  have hQv : inner ℝ (shiftedNeedle r D lam δ₁ δ₂ ε t - chartC r D lam δ₁ δ₂ ε v) v
      = nCoord r D lam δ₁ δ₂ ε v t - nCoord r D lam δ₁ δ₂ ε v 0 := inner_chartC_v hv t
  have hDe : deriv (fun t' : ℝ => inner ℝ (shiftedNeedle r D lam δ₁ δ₂ ε t'
        - chartC r D lam δ₁ δ₂ ε v) (chartE r D lam δ₁ δ₂ ε v)) t
      = deriv (nHeight r D lam δ₁ δ₂ ε (chartE r D lam δ₁ δ₂ ε v)) t :=
    deriv_sub_const_chart _ _ _ _ _
  have hDv : deriv (fun t' : ℝ => inner ℝ (shiftedNeedle r D lam δ₁ δ₂ ε t'
        - chartC r D lam δ₁ δ₂ ε v) v) t
      = deriv (nCoord r D lam δ₁ δ₂ ε v) t := deriv_sub_const_chart _ _ _ _ _
  rw [hP, hQ, hPa, hQb] at hnum
  rw [hPe, hQv, hDe, hDv] at hnum
  exact hnum


end
end Work.Drive.Generic
