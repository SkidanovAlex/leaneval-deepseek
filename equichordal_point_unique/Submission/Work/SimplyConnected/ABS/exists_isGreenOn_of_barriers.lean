import Mathlib
import Submission.Work.SimplyConnected.ABS.Defs
import Submission.GreenConditional
import Submission.ChartLogClamp
import Submission.SuperharmonicX
import Submission.MaxPrincipleRegion
import Submission.DirichletLim
import Submission.BarrierComparison
import Submission.DirichletX
import Submission.ChartBallDirichlet
import Submission.Work.SimplyConnected.ABS.harmonicOnX_pos_or_eq_zero_of_isPreconnected
import Submission.Work.SimplyConnected.ABS.isPreconnected_diff_singleton_of_isOpen
import Submission.Work.SimplyConnected.ABS.exists_superharmonic_majorant_chartLogClamp

/-!
# The Green function of a barrier-regular relatively compact region

The barrier hypothesis `hbar` of `exists_isGreenOn_of_barriers` is Dirichlet regularity of `Ω`:
at every frontier point there is a continuous function, superharmonic on `Ω` near the point,
strictly positive there and vanishing at the point.  The conclusion is the existence of the Green
function of `Ω` with pole `x₀` in the form `IsGreenOn`.

The proof is the sweep (balayage) construction: with the clamped logarithmic potential
`G = chartLogClamp (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) ρ` of a chart ball around `x₀` contained in
`Ω` (a subharmonic, non-negative function on `X ∖ {x₀}`, which is the chart-disc Green function of
that ball extended by `0`),
* `E := Submission.sweep G (Ω ∖ {x₀})`, the least superharmonic majorant of `G`, is harmonic on
  `Ω ∖ {x₀}` (`Submission.sweep_harmonic`);
* it dominates `G`, which gives both positivity near the pole and, together with the majorant
  supplied by the barrier hypothesis, the logarithmic pole (`Submission.barrier_le_sweep`);
* it is dominated by every member of the sweep family, in particular by the majorant
  `W` of `exists_superharmonic_majorant_chartLogClamp`, whose boundary flatness gives the decay
  `E x < ε` off a compact subset of `Ω` (`Submission.sweep_le_of_mem`);
* strict positivity on all of `Ω ∖ {x₀}` follows from `E ≥ 0`, `E > 0` near the pole and the strong
  minimum principle on the preconnected `Ω ∖ {x₀}`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical
open Submission

namespace Work.SimplyConnected.ABS

/-- A chart ball around `x₀` whose *closed* ball lies in the open set `Ω`. -/
theorem exists_chartClosedBall_subset_of_isOpen {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] {Ω : Set X} (hΩo : IsOpen Ω) {x₀ : X} (hx₀ : x₀ ∈ Ω) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.closedBall ((chartAt ℂ x₀) x₀) ρ ⊆ (chartAt ℂ x₀).target ∧
      Submission.chartClosedBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) ρ ⊆ Ω := by
  have hsrc : x₀ ∈ (chartAt ℂ x₀).source := mem_chart_source ℂ x₀
  have hmap : (chartAt ℂ x₀) x₀ ∈ (chartAt ℂ x₀).target := (chartAt ℂ x₀).map_source hsrc
  obtain ⟨ρ₁, hρ₁, hρ₁sub⟩ := Metric.mem_nhds_iff.mp
    ((chartAt ℂ x₀).open_target.mem_nhds hmap)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp
    (((chartAt ℂ x₀).continuousAt_symm hmap).preimage_mem_nhds
      (hΩo.mem_nhds (by rw [(chartAt ℂ x₀).left_inv hsrc]; exact hx₀)))
  refine ⟨min (ρ₁ / 2) (ε / 2), lt_min (half_pos hρ₁) (half_pos hε), ?_, ?_⟩
  · refine (Metric.closedBall_subset_ball ?_).trans hρ₁sub
    linarith [min_le_left (ρ₁ / 2) (ε / 2)]
  · have hsub : Metric.closedBall ((chartAt ℂ x₀) x₀) (min (ρ₁ / 2) (ε / 2))
        ⊆ (chartAt ℂ x₀).target := by
      refine (Metric.closedBall_subset_ball ?_).trans hρ₁sub
      linarith [min_le_left (ρ₁ / 2) (ε / 2)]
    rw [Submission.chartClosedBall_eq_image hsub]
    rintro z ⟨w, hw, rfl⟩
    exact hεsub (Metric.closedBall_subset_ball (by
      linarith [min_le_right (ρ₁ / 2) (ε / 2)]) hw)

theorem exists_isGreenOn_of_barriers {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {Ω : Set X} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω) (hΩne : Ω ≠ Set.univ)
    (hcomp : IsCompact (closure Ω)) {x₀ : X} (hx₀ : x₀ ∈ Ω)
    (hbar : ∀ p ∈ frontier Ω, ∃ (u : X → ℝ) (V : Set X), IsOpen V ∧ p ∈ V ∧
      Submission.SuperharmonicOnX u (Ω ∩ V) ∧ (∀ x ∈ Ω ∩ V, 0 < u x) ∧
      ContinuousOn u V ∧ u p = 0) :
    ∃ E : X → ℝ, Work.SimplyConnected.ABS.IsGreenOn Ω x₀ E := by
  classical
  obtain ⟨ρ, hρ, hρsub, hρΩ⟩ := exists_chartClosedBall_subset_of_isOpen (X := X) hΩo hx₀
  set U : Set X := Ω \ {x₀} with hU
  have hUo : IsOpen U := hΩo.sdiff isClosed_singleton
  have hUsub : U ⊆ (Set.univ \ {x₀} : Set X) := by
    intro x hx; exact ⟨mem_univ x, hx.2⟩
  -- the barrier to be swept
  set G : X → ℝ := Submission.chartLogClamp (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) ρ with hG
  have hGsub_univ : Submission.SubharmonicOnX G (Set.univ \ {x₀}) :=
    Submission.subharmonicOnX_chartLogClamp hρ hρsub
  have hGsubU : Submission.SubharmonicOnX G U :=
    hGsub_univ.mono hUsub (hGsub_univ.1.mono hUsub)
  have hGnn : ∀ x ∈ U, 0 ≤ G x := fun x _ => Submission.chartLogClamp_nonneg x
  -- a point of `U` at which `G` is positive (any point of the chart ball other than the pole)
  have hGpos : ∃ y ∈ U, 0 < G y := by
    set y : X := (chartAt ℂ x₀).symm ((chartAt ℂ x₀) x₀ + (ρ / 2 : ℝ)) with hy
    have hmem : (chartAt ℂ x₀) x₀ + (ρ / 2 : ℝ) ∈ (chartAt ℂ x₀).target := by
      refine hρsub (Metric.mem_closedBall.mpr ?_)
      rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_of_nonneg (by positivity)]
      linarith
    have hcy : (chartAt ℂ x₀) y = (chartAt ℂ x₀) x₀ + (ρ / 2 : ℝ) := by
      rw [hy]; exact (chartAt ℂ x₀).right_inv hmem
    have hnorm : ‖(chartAt ℂ x₀) y - (chartAt ℂ x₀) x₀‖ = ρ / 2 := by
      rw [hcy, add_sub_cancel_left]
      exact Complex.norm_of_nonneg (by positivity)
    have hyball : y ∈ chartBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) ρ := by
      rw [Submission.mem_chartBall]
      refine ⟨?_, ?_⟩
      · rw [hy]; exact (chartAt ℂ x₀).map_target hmem
      · rw [hcy, Metric.mem_ball, dist_eq_norm, add_sub_cancel_left,
          Complex.norm_of_nonneg (by positivity)]
        linarith
    have hyne : y ≠ x₀ := by
      intro h
      have h1 : (chartAt ℂ x₀).symm ((chartAt ℂ x₀) x₀ + (ρ / 2 : ℝ))
          = (chartAt ℂ x₀).symm ((chartAt ℂ x₀) x₀) := by
        rw [← hy, h, (chartAt ℂ x₀).left_inv (mem_chart_source ℂ x₀)]
      have h2 : (chartAt ℂ x₀) x₀ + (ρ / 2 : ℝ) = (chartAt ℂ x₀) x₀ :=
        (chartAt ℂ x₀).symm.injOn hmem ((chartAt ℂ x₀).map_source (mem_chart_source ℂ x₀)) h1
      have h3 : (ρ / 2 : ℝ) = 0 := by
        have := congrArg (fun z : ℂ => z - (chartAt ℂ x₀) x₀) h2
        simpa using this
      linarith
    refine ⟨y, ⟨hρΩ (Submission.chartBall_subset_chartClosedBall _ _ _ hyball), hyne⟩, ?_⟩
    rw [hG, Submission.chartLogClamp_of_mem hyball, hnorm]
    have : ρ / (ρ / 2) = 2 := by field_simp
    rw [this]
    exact Real.log_pos (by norm_num)
  -- the two inputs
  have hUpc : IsPreconnected (Ω \ {x₀}) :=
    Work.SimplyConnected.ABS.isPreconnected_diff_singleton_of_isOpen hΩo hΩc.isPreconnected hx₀
  -- TEMPORARY: superharmonic majorant (delegated)
  have hD2 : ∃ W : X → ℝ, Submission.SuperharmonicOnX W (Ω \ {x₀}) ∧
      (∀ x ∈ Ω \ {x₀}, Submission.chartLogClamp (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) ρ x ≤ W x) ∧
      (∃ C : ℝ, ∃ V : Set X, V ∈ nhds x₀ ∧ ∀ x ∈ V, x ∈ Ω → x ≠ x₀ →
        W x + Real.log ‖(chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀‖ ≤ C) ∧
      (∀ ε : ℝ, 0 < ε → ∃ K : Set X, IsCompact K ∧ K ⊆ Ω ∧ ∀ x ∈ Ω, x ∉ K → W x < ε) :=
    exists_superharmonic_majorant_chartLogClamp (X := X) hΩo hΩc hΩne hcomp hx₀ hρ hρsub hρΩ hbar
  obtain ⟨W, hWsup, hWG, hWpole, hWdecay⟩ := hD2
  have hWmem : W ∈ Submission.sweepFamily G U := ⟨hWsup, hWG⟩
  have hne : (Submission.sweepFamily G U).Nonempty := ⟨W, hWmem⟩
  have hEharm : Submission.HarmonicOnX (Submission.sweep G U) U :=
    Submission.sweep_harmonic hUo hGsubU hne
  have hEG : ∀ x ∈ U, G x ≤ Submission.sweep G U x := fun x hx =>
    Submission.barrier_le_sweep hne hx
  have hEW : ∀ x ∈ U, Submission.sweep G U x ≤ W x := fun x hx =>
    Submission.sweep_le_of_mem hWmem hx
  refine ⟨Submission.sweep G U, ?_, ?_, ?_, ?_⟩
  · -- strict positivity off the pole
    intro x hxΩ hxne
    have hxU : x ∈ U := ⟨hxΩ, hxne⟩
    have hnn : ∀ z ∈ U, 0 ≤ Submission.sweep G U z := fun z hz =>
      le_trans (hGnn z hz) (hEG z hz)
    rcases Work.SimplyConnected.ABS.harmonicOnX_pos_or_eq_zero_of_isPreconnected
        (X := X) hUo hUpc hEharm hnn with hpos | hzero
    · exact hpos x hxU
    · obtain ⟨y, hyU, hypos⟩ := hGpos
      have h1 : Submission.sweep G U y = 0 := hzero y hyU
      have h2 : 0 < Submission.sweep G U y := lt_of_lt_of_le hypos (hEG y hyU)
      rw [h1] at h2; exact absurd h2 (lt_irrefl 0)
  · -- harmonicity off the pole
    intro x hx; exact hEharm x hx
  · -- decay at the ideal boundary
    intro ε hε
    obtain ⟨K, hKc, hKΩ, hKW⟩ := hWdecay ε hε
    refine ⟨K ∪ {x₀}, hKc.union isCompact_singleton, ?_, ?_⟩
    · rintro x (hx | hx)
      · exact hKΩ hx
      · rw [Set.mem_singleton_iff] at hx; rw [hx]; exact hx₀
    · intro x hxΩ hxK
      have hxne : x ≠ x₀ := fun h => hxK (Or.inr (by simpa [h]))
      have hxU : x ∈ U := ⟨hxΩ, hxne⟩
      have hxKw : x ∉ K := fun h => hxK (Or.inl h)
      exact lt_of_le_of_lt (hEW x hxU) (hKW x hxΩ hxKw)
  · -- the logarithmic pole
    obtain ⟨C_W, V_W, hV_W, hWpole'⟩ := hWpole
    refine ⟨max |Real.log ρ| (max C_W 0),
      chartBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) ρ ∩ V_W, ?_, ?_⟩
    · refine Filter.inter_mem ?_ hV_W
      exact Submission.chartBall_mem_nhds hρ (mem_chart_source ℂ x₀) rfl
    · intro x hxV hxΩ hxne
      obtain ⟨hxball, hxW⟩ := hxV
      have hxU : x ∈ U := ⟨hxΩ, hxne⟩
      have hGx : G x = Real.log (ρ / ‖(chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀‖) :=
        Submission.chartLogClamp_of_mem hxball
      have hsubne : (chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀ ≠ 0 := by
        intro h
        refine hxne ?_
        exact (chartAt ℂ x₀).injOn hxball.1 (mem_chart_source ℂ x₀) (sub_eq_zero.mp h)
      have hpos : 0 < ‖(chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀‖ := norm_pos_iff.mpr hsubne
      have hne0 : ‖(chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀‖ ≠ 0 := ne_of_gt hpos
      have hGlow : G x + Real.log ‖(chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀‖ = Real.log ρ := by
        rw [hGx, Real.log_div hρ.ne' hne0]
        ring
      have hlow : Real.log ρ ≤ Submission.sweep G U x
          + Real.log ‖(chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀‖ := by
        have := hEG x hxU
        linarith [hGlow]
      have hup : Submission.sweep G U x
          + Real.log ‖(chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀‖ ≤ C_W := by
        have h1 := hEW x hxU
        have h2 := hWpole' x hxW hxΩ hxne
        linarith
      have hbdd : |Submission.sweep G U x
          + Real.log ‖(chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀‖| ≤ max |Real.log ρ| (max C_W 0) := by
        rw [abs_le]
        refine ⟨?_, ?_⟩
        · have h1 : -(max |Real.log ρ| (max C_W 0)) ≤ -|Real.log ρ| := by
            linarith [le_max_left |Real.log ρ| (max C_W 0)]
          have h2 : -|Real.log ρ| ≤ Real.log ρ := neg_abs_le _
          linarith
        · exact le_trans hup (le_trans (le_max_left C_W 0) (le_max_right _ _))
      exact hbdd

end Work.SimplyConnected.ABS
