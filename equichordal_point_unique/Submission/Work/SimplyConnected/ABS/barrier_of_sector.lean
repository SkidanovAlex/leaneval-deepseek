import Mathlib
import Submission.Work.SimplyConnected.ABS.RegularPieceDefs
import Submission.Work.SimplyConnected.ABS.plane_sector_barrier_continuous
import Submission.Work.SimplyConnected.Defs
import Submission.ChartBallBarrier

namespace Work.SimplyConnected.ABS

open Set Filter
open scoped Topology Manifold ContDiff

set_option linter.unusedSectionVars false

noncomputable section

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **A translated plane function composed with a chart is superharmonic.**
If `φ : ℂ → ℝ` is harmonic on a ball around `c x - a`, then the function
`y ↦ φ (c y - a)` is superharmonic at `x`, measured in the chart `c`.

(This is the transport step of `barrier_of_sector`: the candidate barrier is
`u = φ ∘ (c · - c p)`, and its superharmonicity is a harmonicity statement about `φ` in the
coordinates of `c`.) -/
theorem superharmonicAtChart_comp_sub {φ : ℂ → ℝ} {a : ℂ} {c : OpenPartialHomeomorph X ℂ}
    {x : X} {δ : ℝ} (hx : x ∈ c.source) (hδ : 0 < δ)
    (hφ : ∀ y ∈ Metric.ball (c x - a) δ, InnerProductSpace.HarmonicAt φ y) :
    Submission.SuperharmonicAtChart (fun y : X => φ (c y - a)) c x := by
  obtain ⟨ε, hε, hεsub⟩ :=
    Metric.mem_nhds_iff.mp (c.open_target.mem_nhds (c.map_source hx))
  have hδ' : ∀ z ∈ Metric.ball (c x) (min ε δ), z - a ∈ Metric.ball (c x - a) δ := by
    intro z hz
    have h1 : dist z (c x) < min ε δ := Metric.mem_ball.mp hz
    rw [Metric.mem_ball, dist_eq_norm]
    have h2 : z - a - (c x - a) = z - c x := by ring
    rw [h2]
    have h3 : dist z (c x) = ‖z - c x‖ := dist_eq_norm _ _
    rw [h3] at h1
    linarith [min_le_right ε δ]
  refine ⟨hx, min ε δ, lt_min hε hδ, (Metric.ball_subset_ball (min_le_left _ _)).trans hεsub,
    ?_, ?_⟩
  · -- continuity of the pullback `w ↦ φ (w - a)`
    have hcont : ContinuousOn (fun w : ℂ => φ (w - a)) (Metric.ball (c x) (min ε δ)) := by
      refine continuousOn_of_forall_continuousAt fun w hw => ?_
      exact ContinuousAt.comp ((hφ (w - a) (hδ' w hw)).1.continuousAt)
        (continuousAt_id.sub continuousAt_const)
    refine hcont.congr ?_
    intro w hw
    have hwT : w ∈ c.target :=
      (Metric.ball_subset_ball (min_le_left ε δ)).trans hεsub hw
    simp only [Function.comp_apply]
    rw [c.right_inv hwT]
  · -- the circle mean value inequality
    intro q hq r hr hqr
    have hball : ∀ z ∈ Metric.closedBall q r, z - a ∈ Metric.ball (c x - a) δ := fun z hz =>
      hδ' z (hqr hz)
    have hharm : InnerProductSpace.HarmonicOnNhd (fun w : ℂ => φ (w - a))
        (Metric.closedBall q |r|) := by
      intro z hz
      have hz' : z ∈ Metric.closedBall q r := by rw [abs_of_pos hr] at hz; exact hz
      exact Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic
        (u := φ) (f := fun w : ℂ => w - a) (x := z)
        (analyticAt_id.sub (analyticAt_const (v := a))) (hφ (z - a) (hball z hz'))
    have hsphere : ∀ z ∈ Metric.sphere q |r|,
        ((fun y : X => φ (c y - a)) ∘ c.symm) z = (fun w : ℂ => φ (w - a)) z := by
      intro z hz
      have hz1 : z ∈ Metric.closedBall q |r| := Metric.sphere_subset_closedBall hz
      have hz2 : z ∈ Metric.closedBall q r := by rw [abs_of_pos hr] at hz1; exact hz1
      have hzT : z ∈ c.target :=
        (Metric.ball_subset_ball (min_le_left ε δ)).trans hεsub (hqr hz2)
      simp only [Function.comp_apply]
      rw [c.right_inv hzT]
    have hpt : ((fun y : X => φ (c y - a)) ∘ c.symm) q = φ (q - a) := by
      have hqT : q ∈ c.target :=
        (Metric.ball_subset_ball (min_le_left ε δ)).trans hεsub hq
      simp only [Function.comp_apply]
      rw [c.right_inv hqT]
    rw [Real.circleAverage_congr_sphere hsphere, hpt,
      InnerProductSpace.HarmonicOnNhd.circleAverage_eq hharm]

/-- **The chart-neighbourhood condition is a closed-sector condition.**
Let `U` be an open set avoiding the open sector `{0 < L₁ (c · - c p) ∧ 0 < L₂ (c · - c p)}`,
`x ∈ U ∩ V` with `V ⊆ c.source` open, and suppose the sector itself is nonempty.  Then
`c x - c p` lies *outside the closed sector* `{0 ≤ L₁ · ∧ 0 ≤ L₂ ·}`: if both functionals were
nonnegative there, the openness of `U ∩ V` would produce points of `U ∩ V` strictly inside the
sector. -/
theorem not_mem_closedSector_of_sector {U V : Set X} {c : OpenPartialHomeomorph X ℂ} {p : X}
    {L₁ L₂ : ℂ →L[ℝ] ℝ} (hUo : IsOpen U) (hVo : IsOpen V) (hVc : V ⊆ c.source)
    (hne : ∃ z₀ : ℂ, 0 < L₁ z₀ ∧ 0 < L₂ z₀)
    (hsect : ∀ x ∈ U ∩ V, ¬ (0 < L₁ (c x - c p) ∧ 0 < L₂ (c x - c p)))
    {x : X} (hx : x ∈ U ∩ V) :
    ¬ (0 ≤ L₁ (c x - c p) ∧ 0 ≤ L₂ (c x - c p)) := by
  rintro ⟨h1, h2⟩
  obtain ⟨z₀, hz₁, hz₂⟩ := hne
  have hxsrc : x ∈ c.source := hVc hx.2
  -- the chart image of `U ∩ V` is a neighbourhood of `c x`
  have hpre : c.symm ⁻¹' (U ∩ V) ∈ 𝓝 (c x) := by
    have hUX : U ∩ V ∈ 𝓝 x :=
      Filter.inter_mem (f := 𝓝 x) (hUo.mem_nhds hx.1) (hVo.mem_nhds hx.2)
    have hUX' : U ∩ V ∈ 𝓝 (c.symm (c x)) := by rw [c.left_inv hxsrc]; exact hUX
    exact (c.continuousAt_symm (c.map_source hxsrc)).preimage_mem_nhds hUX'
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem hpre (c.open_target.mem_nhds (c.map_source hxsrc)))
  -- a point of the chart ball strictly inside the sector
  set t : ℝ := δ / (2 * (‖z₀‖ + 1)) with htdef
  have ht : 0 < t := by rw [htdef]; positivity
  have htδ : ‖(t : ℂ) * z₀‖ < δ := by
    rw [norm_mul]
    have hnorm : ‖(t : ℂ)‖ = t := by simp [abs_of_pos ht]
    rw [hnorm, htdef, div_mul_eq_mul_div, div_lt_iff₀ (by positivity : (0:ℝ) < 2 * (‖z₀‖ + 1))]
    nlinarith [norm_nonneg z₀]
  set w : ℂ := c x + (t : ℂ) * z₀ with hwdef
  have hwball : w ∈ Metric.ball (c x) δ := by
    rw [Metric.mem_ball, dist_eq_norm, hwdef, add_sub_cancel_left]
    exact htδ
  obtain ⟨hwpre, hwT⟩ := hδsub hwball
  have hwsrc : c.symm w ∈ U ∩ V := hwpre
  have hcy : c (c.symm w) = w := c.right_inv hwT
  have hsplit : c x + (t : ℂ) * z₀ - c p = (c x - c p) + (t : ℂ) * z₀ := by ring
  have hmul₁ : L₁ ((t : ℂ) * z₀) = t * L₁ z₀ := by
    rw [← Complex.real_smul, map_smul, smul_eq_mul]
  have hmul₂ : L₂ ((t : ℂ) * z₀) = t * L₂ z₀ := by
    rw [← Complex.real_smul, map_smul, smul_eq_mul]
  refine hsect (c.symm w) hwsrc ⟨?_, ?_⟩
  · rw [hcy, hwdef, hsplit, map_add, hmul₁]; nlinarith
  · rw [hcy, hwdef, hsplit, map_add, hmul₂]; nlinarith

/-- **The sector condition yields a barrier.**  Let `U ⊆ X` be an open set of a complex one-manifold, `p ∉ U`, and suppose `U` satisfies the sector (cone) condition at `p` (`Work.SimplyConnected.ABS.HasSectorBoundary U p`).  Then there is a barrier at `p`: a function `u` and a neighbourhood `V` of `p` with `u` superharmonic on `U ∩ V`, positive on `U ∩ V`, continuous on `V` and `u p = 0`. -/
theorem barrier_of_sector {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {U : Set X} {p : X} (hUo : IsOpen U) (hpU : p ∉ U)
    (h : Work.SimplyConnected.ABS.HasSectorBoundary U p) :
    ∃ (u : X → ℝ) (V : Set X), IsOpen V ∧ p ∈ V ∧
      Submission.SuperharmonicOnX u (U ∩ V) ∧ (∀ x ∈ U ∩ V, 0 < u x) ∧
      ContinuousOn u V ∧ u p = 0 := by
  obtain ⟨c, V, L₁, L₂, hcatlas, hVo, hpV, hVc, hpsrc, hL₁, hL₂, hne, hsect⟩ := h
  obtain ⟨φ, hφcont, hφ0, hφpos, hφharm⟩ :=
    plane_sector_barrier_continuous L₁ L₂ hL₁ hL₂ hne
  have hout : ∀ x ∈ U ∩ V, ¬ (0 ≤ L₁ (c x - c p) ∧ 0 ≤ L₂ (c x - c p)) :=
    fun x hx => not_mem_closedSector_of_sector hUo hVo hVc hne hsect hx
  have hcV : ContinuousOn (fun y : X => c y - c p) V :=
    (c.continuousOn.mono hVc).sub continuousOn_const
  have hcu : ContinuousOn (fun y : X => φ (c y - c p)) V := hφcont.comp_continuousOn hcV
  refine ⟨fun y : X => φ (c y - c p), V, hVo, hpV, ⟨?_, ?_⟩, ?_, hcu, ?_⟩
  · -- continuity on `U ∩ V`
    exact hcu.mono Set.inter_subset_right
  · -- superharmonicity at every point of `U ∩ V`
    intro x hx
    have hxsrc : x ∈ c.source := hVc hx.2
    obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp
      (InnerProductSpace.isOpen_setOfPred_harmonicAt φ) _ (hφharm _ (hout x hx))
    have hchart : Submission.SuperharmonicAtChart (fun y : X => φ (c y - c p)) c x :=
      superharmonicAtChart_comp_sub (a := c p) hxsrc hδ hδsub
    exact Submission.SuperharmonicAtChart.transport hxsrc (mem_chart_source ℂ x)
      (Submission.analyticAt_transition_of_mem_atlas hcatlas (chart_mem_atlas ℂ x))
      (Submission.analyticAt_transition_of_mem_atlas (chart_mem_atlas ℂ x) hcatlas)
      hchart
  · -- positivity on `U ∩ V`
    intro x hx
    exact hφpos _ (hout x hx)
  · -- `u p = 0`
    simp [hφ0]

end

end Work.SimplyConnected.ABS
