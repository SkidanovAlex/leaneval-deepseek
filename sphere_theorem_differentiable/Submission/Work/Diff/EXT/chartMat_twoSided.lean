import Mathlib
import Submission.Work.Diff.EXT.splice_defs
import Submission.Work.Diff.EXT.chartMat_halfspace
import Submission.Work.Diff.EXT.jet_functions_smooth
import Submission.Work.Diff.EXT.contDiffAt_of_hasFTaylorSeries_glue
import Submission.Work.Diff.EXT.borel_jet_uniform
import Submission.Work.Diff.EXT.jet_match_of_time_jets

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Two-sided smoothness of the chart matrix of a jointly smooth family of metrics

`Work.Diff.EXT.chartMat G x₀ t y` is the matrix of the metric `G t` in the coordinate frame of the
chart at `x₀`, evaluated at the chart coordinate `y`.  It is a *total* function of `(t, y)`, and
`chartMat_halfspace` shows that it is `C^∞` on the half-open slab `[0, T) × target`.  Here we prove
the two-sided version: there is an open neighbourhood `B` of `(0, (extChartAt I x₀) x₀)` and a
`C^∞` function `w` on `B` which equals the chart matrix on `B ∩ {t ≥ 0}`.

## Route

Let `Hc p = chartMat H x₀ p.1 p.2` and `S = (Ico 0 τ) ×ˢ (extChartAt I x₀).target`, so that
`Hc` is `C^∞` on the slab `S` (`chartMat_halfspace`) and its one-sided time-jets
`y ↦ iteratedFDerivWithin ℝ k Hc S (0,y) (fun _ => (1,0))` are `C^∞` in `y`
(`jet_functions_smooth`).  Two ingredients are needed:

* **Borel's lemma with parameters**: there is a globally `C^∞` function `F` whose time derivatives
  at `t = 0` reproduce those jets on a neighbourhood `W` of the chart centre
  (`Submission.Work.Diff.EXT.borel_jet_parametric`);
* **time-jets determine all jets**: consequently `Hc` and `F` have the same full iterated
  derivative at every boundary point `(0,y)`, `y ∈ W`
  (`Submission.Work.Diff.EXT.jet_match_of_time_jets`).

Given both, put `w p = F p` for `p.1 ≤ 0` and `w p = Hc p` for `p.1 > 0`.  On a closed ball
`closedBall y₀ r ⊆ W` the two pieces glue along the hyperplane `{t = 0}`:
`contDiffAt_of_hasFTaylorSeries_glue` applies with the two closed sets
`sL = {t ≤ 0} × univ` and `sR = [0,τ/2] × closedBall y₀ r`, whose union is a neighbourhood of
`(0,y₀)` and whose intersection is `{0} × closedBall y₀ r`; there the two Taylor series agree by
the jet-matching property (`pL` is the series of the globally smooth `F`, `pR` the restriction of
the slab series of `Hc`).  This gives `ContDiffOn ℝ ⊤ w (Ioo (-τ) τ ×ˢ ball y₀ r)`, and on the
right half `w` is exactly the chart matrix.

The two named ingredients are used here only through their *conclusions*, which are collected in
the hypothesis `hpieces` of `chartMat_twoSided_of_pieces`; the final theorem applies it.
-/

namespace Work.Diff.EXT

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]

/-- The chart matrix of a family of metrics, as a function on `ℝ × E` (pairing the time variable
and the chart coordinate).  This is definitionally the same function as
`fun p => chartMat H x₀ p.1 p.2`, but shorter to write. -/
noncomputable abbrev chartMatPair (H : ℝ → Submission.Diff.SMet I M) (x₀ : M) :
    ℝ × E → MatE (E := E) :=
  fun p => Work.Diff.EXT.chartMat H x₀ p.1 p.2

/-- The level `∞` is the top of `ℕ∞` coerced into `ℕ∞ω`; the comparison with a natural level is
`le_top` transported along the coercion. -/
private lemma enatCast_le_smooth (k : ℕ) :
    (((k : ℕ) : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) :=
  WithTop.coe_le_coe.mpr le_top

/-- **Assembly.**  Assuming the conclusions of Borel's lemma with parameters and of the
"time-jets determine all jets" theorem (collected in `hpieces`), the chart matrix of a jointly
smooth family of metrics is two-sided smooth near `(0, (extChartAt I x₀) x₀)`. -/
theorem chartMat_twoSided_of_pieces
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (H : ℝ → Submission.Diff.SMet I M) {τ : ℝ} (hτ : 0 < τ)
    (hH : Submission.Diff.JointSmooth H (Set.Ico 0 τ)) (x₀ : M)
    (hpieces : ∃ W : Set E, IsOpen W ∧ (extChartAt I x₀) x₀ ∈ W ∧
      W ⊆ (extChartAt I x₀).target ∧
      ∃ F : ℝ × E → MatE (E := E), ContDiff ℝ (⊤ : ℕ∞) F ∧
        (∀ (k : ℕ) (y : E), y ∈ W →
          iteratedDeriv k (fun t : ℝ => F (t, y)) 0 =
            iteratedFDerivWithin ℝ k (chartMatPair H x₀)
              ((Set.Ico 0 τ) ×ˢ (extChartAt I x₀).target) (0, y) (fun _ => ((1 : ℝ), 0))) ∧
        (∀ (j : ℕ) (y : E), y ∈ W →
          iteratedFDerivWithin ℝ j (chartMatPair H x₀) ((Set.Ico 0 τ) ×ˢ W) (0, y) =
            iteratedFDeriv ℝ j F (0, y))) :
    ∃ B : Set (ℝ × E), IsOpen B ∧ ((0 : ℝ), (extChartAt I x₀) x₀) ∈ B ∧
      ∃ w : ℝ × E → MatE (E := E), ContDiffOn ℝ (⊤ : ℕ∞) w B ∧
        ∀ p ∈ B, 0 ≤ p.1 → w p = Work.Diff.EXT.chartMat H x₀ p.1 p.2 := by
  classical
  obtain ⟨W, hWopen, hy₀W, hWU, F, hFsmooth, hmatch, hjet⟩ := hpieces
  -- ### basic open sets and smoothness of the chart matrix on the slab
  have hUopen : IsOpen (extChartAt I x₀).target := isOpen_extChartAt_target (I := I) x₀
  have hHc_big : ContDiffOn ℝ (⊤ : ℕ∞) (chartMatPair H x₀)
      ((Set.Ico 0 τ) ×ˢ (extChartAt I x₀).target) := chartMat_halfspace hH x₀
  have hHc_small : ContDiffOn ℝ (⊤ : ℕ∞) (chartMatPair H x₀) ((Set.Ico 0 τ) ×ˢ W) :=
    hHc_big.mono (Set.prod_mono Subset.rfl hWU)
  -- a closed ball around the chart centre inside `W`
  obtain ⟨r, hr, hball⟩ : ∃ r : ℝ, 0 < r ∧
      Metric.closedBall ((extChartAt I x₀) x₀) r ⊆ W := by
    obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.mp (hWopen.mem_nhds hy₀W)
    refine ⟨ε / 2, by linarith, fun y hy => hεW ?_⟩
    rw [Metric.mem_closedBall] at hy
    rw [Metric.mem_ball]
    linarith
  -- ### the two closed sets and the function
  set sL : Set (ℝ × E) := Set.Iic 0 ×ˢ (Set.univ : Set E) with hsL
  set sR : Set (ℝ × E) := Set.Icc 0 (τ / 2) ×ˢ Metric.closedBall ((extChartAt I x₀) x₀) r
    with hsR
  set w : ℝ × E → MatE (E := E) :=
    fun p => if p.1 ≤ 0 then F p else chartMatPair H x₀ p with hw
  -- ### the two Taylor series
  have hsL_ud : UniqueDiffOn ℝ sL := by
    rw [hsL]; exact (uniqueDiffOn_Iic 0).prod uniqueDiffOn_univ
  have hsW_ud : UniqueDiffOn ℝ ((Set.Ico 0 τ) ×ˢ W) :=
    (uniqueDiffOn_Ico 0 τ).prod hWopen.uniqueDiffOn
  have hsR_sub : sR ⊆ (Set.Ico 0 τ) ×ˢ W := by
    rw [hsR]
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    exact ⟨⟨(Set.mem_Icc.mp ht).1, by linarith [(Set.mem_Icc.mp ht).2, hr]⟩, hball hy⟩
  have hwL : ContDiffOn ℝ (⊤ : ℕ∞) w sL :=
    hFsmooth.contDiffOn.congr fun z hz => by
      rw [hsL] at hz
      rw [hw]
      exact if_pos (Set.mem_Iic.mp hz.1)
  have hL : HasFTaylorSeriesUpToOn (⊤ : ℕ∞) w (ftaylorSeriesWithin ℝ w sL) sL :=
    hwL.ftaylorSeriesWithin hsL_ud
  have hRmono : HasFTaylorSeriesUpToOn (⊤ : ℕ∞) (chartMatPair H x₀)
      (ftaylorSeriesWithin ℝ (chartMatPair H x₀) ((Set.Ico 0 τ) ×ˢ W)) sR :=
    (hHc_small.ftaylorSeriesWithin hsW_ud).mono hsR_sub
  have hR : HasFTaylorSeriesUpToOn (⊤ : ℕ∞) w
      (ftaylorSeriesWithin ℝ (chartMatPair H x₀) ((Set.Ico 0 τ) ×ˢ W)) sR :=
    { zero_eq := by
        intro z hz
        rw [hsR] at hz
        have h0 : (ftaylorSeriesWithin ℝ (chartMatPair H x₀) ((Set.Ico 0 τ) ×ˢ W) z 0).curry0
            = chartMatPair H x₀ z := by
          simp only [ftaylorSeriesWithin, ContinuousMultilinearMap.curry0_apply,
            iteratedFDerivWithin_zero_apply]
        rw [h0]
        simp only [hw]
        split_ifs with hzle
        · have hz0 : z.1 = 0 := le_antisymm hzle (Set.mem_Icc.mp hz.1).1
          have hz' : z = ((0 : ℝ), z.2) := by ext <;> simp [hz0]
          rw [hz']
          have h1 := hmatch 0 z.2 (hball hz.2)
          rw [iteratedDeriv_zero] at h1
          have h2 : iteratedFDerivWithin ℝ 0 (chartMatPair H x₀)
              ((Set.Ico 0 τ) ×ˢ (extChartAt I x₀).target) ((0 : ℝ), z.2)
              (fun _ => ((1 : ℝ), 0)) = chartMatPair H x₀ ((0 : ℝ), z.2) := by
            simpa using (iteratedFDerivWithin_zero_apply (𝕜 := ℝ) (f := chartMatPair H x₀)
              (s := (Set.Ico 0 τ) ×ˢ (extChartAt I x₀).target) (x := ((0 : ℝ), z.2))
              (fun _ : Fin 0 => ((1 : ℝ), 0)))
          exact h2.symm.trans h1.symm
        · rfl
      fderivWithin := hRmono.fderivWithin
      cont := hRmono.cont }
  -- ### closedness of the two sets
  have hsL_closed : IsClosed sL := by
    rw [hsL]; exact isClosed_Iic.prod isClosed_univ
  have hsR_closed : IsClosed sR := by
    rw [hsR]; exact isClosed_Icc.prod Metric.isClosed_closedBall
  -- ### the union is a neighbourhood of every boundary point of the ball
  have hu_of_mem : ∀ y ∈ Metric.ball ((extChartAt I x₀) x₀) r,
      sL ∪ sR ∈ 𝓝 (((0 : ℝ), y) : ℝ × E) := by
    intro y hy
    have hyr : dist y ((extChartAt I x₀) x₀) < r := Metric.mem_ball.mp hy
    have hρ : 0 < r - dist y ((extChartAt I x₀) x₀) := by linarith
    have hmem : Set.Ioo (-(τ / 4)) (τ / 4)
        ×ˢ Metric.ball y (r - dist y ((extChartAt I x₀) x₀)) ∈ 𝓝 (((0 : ℝ), y) : ℝ × E) :=
      IsOpen.mem_nhds (isOpen_Ioo.prod Metric.isOpen_ball)
        ⟨⟨by linarith, by linarith⟩, Metric.mem_ball_self hρ⟩
    refine mem_of_superset hmem ?_
    · rintro ⟨t, z⟩ ⟨ht, hz⟩
      rw [hsR]
      by_cases ht0 : t ≤ 0
      · exact Or.inl (by rw [hsL]; exact ⟨Set.mem_Iic.mpr ht0, trivial⟩)
      · have ht0' : 0 < t := lt_of_not_ge ht0
        refine Or.inr ⟨⟨le_of_lt ht0', by linarith [ht.2]⟩, ?_⟩
        rw [Metric.mem_closedBall]
        have hz' : dist z y < r - dist y ((extChartAt I x₀) x₀) := Metric.mem_ball.mp hz
        exact le_of_lt (by
          calc dist z ((extChartAt I x₀) x₀) ≤ dist z y + dist y ((extChartAt I x₀) x₀) :=
                dist_triangle _ _ _
            _ < r := by linarith)
  -- ### the agreement of the two series on the intersection `{0} × closedBall`
  have hagree : ∀ z ∈ sL ∩ sR,
      ftaylorSeriesWithin ℝ w sL z
        = ftaylorSeriesWithin ℝ (chartMatPair H x₀) ((Set.Ico 0 τ) ×ˢ W) z := by
    intro z hz
    obtain ⟨hzL, hzR⟩ := hz
    rw [hsL] at hzL
    rw [hsR] at hzR
    have hzW : z.2 ∈ W := hball hzR.2
    have hz0 : z.1 = 0 := le_antisymm (Set.mem_Iic.mp hzL.1) (Set.mem_Icc.mp hzR.1).1
    have hz' : z = ((0 : ℝ), z.2) := by ext <;> simp [hz0]
    rw [hz']
    funext j
    show iteratedFDerivWithin ℝ j w sL ((0 : ℝ), z.2)
      = iteratedFDerivWithin ℝ j (chartMatPair H x₀) ((Set.Ico 0 τ) ×ˢ W) ((0 : ℝ), z.2)
    have h1 : iteratedFDerivWithin ℝ j w sL ((0 : ℝ), z.2)
        = iteratedFDerivWithin ℝ j F sL ((0 : ℝ), z.2) :=
      iteratedFDerivWithin_congr (s := sL) (x := ((0 : ℝ), z.2)) (fun u hu => by
        rw [hsL] at hu
        rw [hw]
        exact if_pos (Set.mem_Iic.mp hu.1)) (by rw [hsL]; exact ⟨by simp, trivial⟩) j
    have h2 : iteratedFDerivWithin ℝ j F sL ((0 : ℝ), z.2)
        = iteratedFDeriv ℝ j F ((0 : ℝ), z.2) :=
      iteratedFDerivWithin_eq_iteratedFDeriv
        (by rw [hsL]; exact (uniqueDiffOn_Iic 0).prod uniqueDiffOn_univ)
        ((hFsmooth.contDiffAt (x := ((0 : ℝ), z.2))).of_le (enatCast_le_smooth j))
        (by rw [hsL]; exact ⟨by simp, trivial⟩)
    have h4 := hjet j z.2 hzW
    rw [h1, h2, h4]
  -- ### the glue at the boundary points
  have hglue : ∀ y ∈ Metric.ball ((extChartAt I x₀) x₀) r,
      ContDiffAt ℝ (⊤ : ℕ∞) w ((0 : ℝ), y) := by
    intro y hy
    rw [contDiffAt_infty]
    intro n
    exact contDiffAt_of_hasFTaylorSeries_glue (hL.of_le (enatCast_le_smooth n))
      (hR.of_le (enatCast_le_smooth n)) hsL_closed hsR_closed (hu_of_mem y hy) hagree
  -- ### conclusion
  refine ⟨Set.Ioo (-τ) τ ×ˢ Metric.ball ((extChartAt I x₀) x₀) r,
    isOpen_Ioo.prod Metric.isOpen_ball, ?_, w, ?_, ?_⟩
  · exact ⟨⟨by linarith, by linarith⟩, Metric.mem_ball_self hr⟩
  · -- `ContDiffOn ℝ ⊤ w B`
    rw [contDiffOn_iff_forall_nat_le]
    intro m _
    intro p hp
    have hp1 : -τ < p.1 ∧ p.1 < τ := hp.1
    by_cases hp0 : p.1 = 0
    · have hp2 : p.2 ∈ Metric.ball ((extChartAt I x₀) x₀) r := hp.2
      have hp' : p = ((0 : ℝ), p.2) := by ext <;> simp [hp0]
      rw [hp']
      exact ((hglue p.2 hp2).of_le (enatCast_le_smooth m)).contDiffWithinAt
    · rcases lt_or_gt_of_ne hp0 with hlt | hgt
      · have hev : w =ᶠ[𝓝 p] F := by
          filter_upwards [IsOpen.mem_nhds (isOpen_lt continuous_fst continuous_const) hlt]
            with z hz
          rw [hw]
          exact if_pos (le_of_lt hz)
        exact (((hFsmooth.contDiffAt (x := p)).congr_of_eventuallyEq hev).of_le
          (enatCast_le_smooth m)).contDiffWithinAt
      · have hev : w =ᶠ[𝓝 p] chartMatPair H x₀ := by
          filter_upwards [IsOpen.mem_nhds (isOpen_lt continuous_const continuous_fst) hgt]
            with z hz
          rw [hw]
          exact if_neg (not_le.mpr hz)
        have hnb : (Set.Ico 0 τ) ×ˢ (extChartAt I x₀).target ∈ 𝓝 p := by
          have hmem : Set.Ioo (p.1 / 2) ((p.1 + τ) / 2) ×ˢ (extChartAt I x₀).target ∈ 𝓝 p :=
            IsOpen.mem_nhds (isOpen_Ioo.prod hUopen)
              ⟨⟨by linarith, by linarith⟩, hWU (hball (Metric.ball_subset_closedBall hp.2))⟩
          refine mem_of_superset hmem ?_
          rintro ⟨t, yv⟩ ⟨ht, hyv⟩
          exact ⟨⟨le_of_lt (by linarith [ht.1] : (0 : ℝ) < t), by linarith [ht.2]⟩, hyv⟩
        exact (((hHc_big.contDiffAt hnb).of_le (enatCast_le_smooth m)).congr_of_eventuallyEq
          hev).contDiffWithinAt
  · -- agreement with the chart matrix on the right half
    intro p hp hple
    have hpW : p.2 ∈ W := hball (Metric.ball_subset_closedBall hp.2)
    by_cases hp0 : p.1 = 0
    · have hif : w p = F p := by
        rw [hw]
        exact if_pos (le_of_eq hp0)
      rw [hif]
      have h1 := hmatch 0 p.2 hpW
      rw [iteratedDeriv_zero] at h1
      have hp' : p = ((0 : ℝ), p.2) := by ext <;> simp [hp0]
      rw [hp'] at h1 ⊢
      rw [h1]
      simpa using (iteratedFDerivWithin_zero_apply (𝕜 := ℝ) (f := chartMatPair H x₀)
        (s := (Set.Ico 0 τ) ×ˢ (extChartAt I x₀).target) (x := ((0 : ℝ), p.2))
        (fun _ : Fin 0 => ((1 : ℝ), 0)))
    · have hpos : 0 < p.1 := lt_of_le_of_ne hple (Ne.symm hp0)
      simp only [hw]
      rw [if_neg (not_le.mpr hpos)]

/-- **The chart matrix of a jointly smooth family of metrics is two-sided smooth at `t = 0`.**

There is an open neighbourhood `B` of `(0, (extChartAt I x₀) x₀)` and a `C^∞` function `w` on `B`
which, on `B ∩ {t ≥ 0}`, coincides with the chart matrix `t ↦ y ↦ chartMat H x₀ t y`. -/
theorem chartMat_twoSided
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (H : ℝ → Submission.Diff.SMet I M) {τ : ℝ} (hτ : 0 < τ)
    (hH : Submission.Diff.JointSmooth H (Set.Ico 0 τ)) (x₀ : M) :
    ∃ B : Set (ℝ × E), IsOpen B ∧ ((0 : ℝ), (extChartAt I x₀) x₀) ∈ B ∧
      ∃ w : ℝ × E → Work.Diff.EXT.MatE (E := E),
        ContDiffOn ℝ (⊤ : ℕ∞) w B ∧ ∀ p ∈ B, 0 ≤ p.1 → w p = Work.Diff.EXT.chartMat H x₀ p.1 p.2 := by
  classical
  have hUopen : IsOpen (extChartAt I x₀).target := isOpen_extChartAt_target (I := I) x₀
  have hy₀U : (extChartAt I x₀) x₀ ∈ (extChartAt I x₀).target :=
    PartialEquiv.map_source (extChartAt I x₀) (mem_extChartAt_source (I := I) x₀)
  have hHc_big : ContDiffOn ℝ (⊤ : ℕ∞) (chartMatPair H x₀)
      ((Set.Ico 0 τ) ×ˢ (extChartAt I x₀).target) := chartMat_halfspace hH x₀
  -- the one-sided time jets of the chart matrix are smooth in `y`
  have hjet_smooth : ∀ k : ℕ, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : E => iteratedFDerivWithin ℝ k (chartMatPair H x₀)
        ((Set.Ico 0 τ) ×ˢ (extChartAt I x₀).target) (0, y) (fun _ => ((1 : ℝ), 0)))
      (extChartAt I x₀).target :=
    fun k => jet_functions_smooth hτ hUopen (chartMatPair H x₀) hHc_big k
  -- Borel's lemma with parameters
  obtain ⟨ε, hε, W, hWopen, hy₀W, hWU, F, hFsmooth, hFmatch⟩ :=
    borel_jet_uniform hUopen
      (fun k y => iteratedFDerivWithin ℝ k (chartMatPair H x₀)
        ((Set.Ico 0 τ) ×ˢ (extChartAt I x₀).target) (0, y) (fun _ => ((1 : ℝ), 0)))
      hjet_smooth hy₀U
  -- the chart matrix is smooth on the slab over `W` as well
  have hHc_small : ContDiffOn ℝ (⊤ : ℕ∞) (chartMatPair H x₀) ((Set.Ico 0 τ) ×ˢ W) :=
    hHc_big.mono (Set.prod_mono Subset.rfl hWU)
  -- the within-jets on the two slabs agree at their common boundary points
  have hud_small : UniqueDiffOn ℝ ((Set.Ico 0 τ) ×ˢ W) :=
    (uniqueDiffOn_Ico 0 τ).prod hWopen.uniqueDiffOn
  have hud_big : UniqueDiffOn ℝ ((Set.Ico 0 τ) ×ˢ (extChartAt I x₀).target) :=
    (uniqueDiffOn_Ico 0 τ).prod hUopen.uniqueDiffOn
  have hsub : (Set.Ico 0 τ) ×ˢ W ⊆ (Set.Ico 0 τ) ×ˢ (extChartAt I x₀).target :=
    Set.prod_mono Subset.rfl hWU
  -- time-jets determine all jets (on the slab over `W`)
  have hjetmatch : ∀ (j : ℕ) (y : E), y ∈ W →
      iteratedFDerivWithin ℝ j (chartMatPair H x₀) ((Set.Ico 0 τ) ×ˢ W) (0, y) =
        iteratedFDeriv ℝ j F (0, y) :=
    jet_match_of_time_jets hτ hWopen (chartMatPair H x₀) F hHc_small hFsmooth
      (fun k y hy => by
        rw [iteratedFDerivWithin_subset hsub hud_small hud_big
          (hHc_big.of_le (enatCast_le_smooth k)) ⟨⟨le_refl 0, hτ⟩, hy⟩]
        exact (hFmatch k y hy).symm)
  -- assemble: the two inputs of `chartMat_twoSided_of_pieces`
  exact chartMat_twoSided_of_pieces H hτ hH x₀
    ⟨W, hWopen, hy₀W, hWU, F, hFsmooth, hFmatch, hjetmatch⟩

end Work.Diff.EXT
