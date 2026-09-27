import Mathlib
import Submission.Work.SimplyConnected.ABS.regionSweepBarrier
import Submission.Work.SimplyConnected.ABS.globalizedBarrier_dev

/-!
# The member of the sweep family produced by a local barrier

Let `Ω` be open, `p ∈ frontier Ω`, and `u` a local barrier at `p`: `u` superharmonic and `> 0` on
`Ω ∩ V`, continuous on the open neighbourhood `V ∋ p`, with `u p = 0` (and `V` taken inside a chart
ball at `p`, `chartClosedBall … ρ₂ ⊆ V`).

The *glued* function

`v := lam · min (u ·) 1`  (with `lam := max 1 (ρ₂ - ρ)`)

is superharmonic on `Ω ∩ V` (minimum with a constant, then scaling), and on the region

`R := barrierMemberRegion Ω V p ρ ρ₂ u
      = Ω ∩ V ∩ chartBall (chartAt ℂ p) ((chartAt ℂ p) p) ρ₂
          ∩ (({u > 1} ∩ V) ∪ chartBall (chartAt ℂ p) ((chartAt ℂ p) p) ρ)`

it dominates the chart cone `chartCone … ρ`: on `{u > 1}` we have `min (u ·) 1 = 1`, hence
`v = lam ≥ ρ₂ - ρ ≥ chartCone … ρ`; on `chartBall … ρ` the cone vanishes.  The region is chosen
exactly so that the level set `{u = 1}` — where `u` is continuous, since `u` is continuous on `V` —
is the interface across which `lam u` is glued to the constant `lam`.

Consequently `v` is a member of `Submission.sweepFamily (chartCone … ρ) R` which is `< ε` near `p`
(because `v ≤ lam u` and `u → 0` at `p`) and `> 0` on `R`, and the sweep of the cone over `R` is a
harmonic barrier on `R`: nonnegative, dominating the cone, and vanishing at `p`.  This is the
local/regional part of the globalized-barrier theorem; the remaining gap is the extension of this
regional barrier to all of `Ω`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set Classical

namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- The region on which the local barrier is glued to the constant `lam`: inside the chart ball of
radius `ρ₂` (which sits in `V`), either `u > 1` — where `min (u ·) 1 = 1` — or inside the smaller
chart ball of radius `ρ`, where the cone vanishes. -/
def barrierMemberRegion (Ω V : Set X) (p : X) (ρ ρ₂ : ℝ) (u : X → ℝ) : Set X :=
  Ω ∩ V ∩ Submission.chartBall (chartAt ℂ p) ((chartAt ℂ p) p) ρ₂ ∩
    (({x : X | 1 < u x} ∩ V) ∪ Submission.chartBall (chartAt ℂ p) ((chartAt ℂ p) p) ρ)

theorem barrierMemberRegion_subset_chartBall (Ω V : Set X) (p : X) (ρ ρ₂ : ℝ) (u : X → ℝ) :
    barrierMemberRegion Ω V p ρ ρ₂ u ⊆
      Submission.chartBall (chartAt ℂ p) ((chartAt ℂ p) p) ρ₂ :=
  fun _ hx => hx.1.2

theorem barrierMemberRegion_subset (Ω V : Set X) (p : X) (ρ ρ₂ : ℝ) (u : X → ℝ) :
    barrierMemberRegion Ω V p ρ ρ₂ u ⊆ Ω ∩ V :=
  fun _ hx => ⟨hx.1.1.1, hx.1.1.2⟩

/-- **The gluing region is open.** -/
theorem isOpen_barrierMemberRegion {Ω V : Set X} (hΩo : IsOpen Ω) (hVo : IsOpen V) {p : X}
    {u : X → ℝ} (hcont : ContinuousOn u V) (ρ ρ₂ : ℝ) :
    IsOpen (barrierMemberRegion Ω V p ρ ρ₂ u) := by
  have h1 : IsOpen ({x : X | 1 < u x} ∩ V) := by
    have h : IsOpen (V ∩ u ⁻¹' Set.Ioi (1 : ℝ)) :=
      hcont.isOpen_inter_preimage hVo (isOpen_Ioi (a := (1 : ℝ)))
    have hEq : V ∩ u ⁻¹' Set.Ioi (1 : ℝ) = ({x : X | 1 < u x} ∩ V) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioi, Set.mem_ofPred_eq]
      tauto
    rwa [hEq] at h
  exact ((hΩo.inter hVo).inter (Submission.chartBall_isOpen _ _ _)).inter
    (h1.union (Submission.chartBall_isOpen _ _ _))

/-- **The glued function is superharmonic on `Ω ∩ V`.** -/
theorem superharmonicOnX_glue {Ω V : Set X} (hVo : IsOpen V) {u : X → ℝ} {lam : ℝ} (hlam : 0 ≤ lam)
    (hsup : Submission.SuperharmonicOnX u (Ω ∩ V)) :
    Submission.SuperharmonicOnX (fun x => lam * min (u x) 1) (Ω ∩ V) := by
  have hmin : Submission.SuperharmonicOnX (fun x => min (u x) 1) (Ω ∩ V) :=
    Work.SimplyConnected.ABS.SuperharmonicOnX.inf_const_dev hsup 1
  -- scaling by a nonnegative constant, with the `SuperharmonicOnX.const_mul` step inlined
  refine ⟨hmin.1.const_mul lam, fun x hx => ?_⟩
  obtain ⟨hxsrc, ρh, hρh, htgt, hch, hmvh⟩ := hmin.2 x hx
  have hfun : (fun y => lam * min (u y) 1) ∘ (chartAt ℂ x).symm
      = fun w => lam * ((fun y => min (u y) 1) ∘ (chartAt ℂ x).symm) w := by
    funext w; rfl
  refine ⟨hxsrc, ρh, hρh, htgt, ?_, ?_⟩
  · rw [hfun]
    exact hch.const_mul lam
  · intro p hp r hr hrsub
    have hca : Real.circleAverage
        (fun w => lam * ((fun y => min (u y) 1) ∘ (chartAt ℂ x).symm) w) p r
        = lam * Real.circleAverage ((fun y => min (u y) 1) ∘ (chartAt ℂ x).symm) p r := by
      simpa using Real.circleAverage_fun_smul
        (f := (fun y => min (u y) 1) ∘ (chartAt ℂ x).symm) (a := lam) (c := p) (R := r)
    rw [hfun, hca]
    exact mul_le_mul_of_nonneg_left (hmvh p hp r hr hrsub) hlam

/-- **The member of the sweep family produced by a local barrier.** -/
theorem memberOfLocalBarrier {Ω V : Set X} (hΩo : IsOpen Ω) (hVo : IsOpen V) {p : X}
    (hpV : p ∈ V) {u : X → ℝ} (hsup : Submission.SuperharmonicOnX u (Ω ∩ V))
    (hpos : ∀ x ∈ Ω ∩ V, 0 < u x) (hcont : ContinuousOn u V) (hup : u p = 0)
    {ρ ρ₂ : ℝ} (hρ : 0 < ρ) (hρρ₂ : ρ < ρ₂)
    (htgt : Metric.closedBall ((chartAt ℂ p) p) ρ₂ ⊆ (chartAt ℂ p).target) :
    (fun x => max 1 (ρ₂ - ρ) * min (u x) 1) ∈
        Submission.sweepFamily (chartCone (chartAt ℂ p) ((chartAt ℂ p) p) ρ)
          (barrierMemberRegion Ω V p ρ ρ₂ u) ∧
      (∀ x ∈ barrierMemberRegion Ω V p ρ ρ₂ u, 0 < max 1 (ρ₂ - ρ) * min (u x) 1) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N : Set X, N ∈ 𝓝 p ∧
        ∀ x ∈ barrierMemberRegion Ω V p ρ ρ₂ u ∩ N, max 1 (ρ₂ - ρ) * min (u x) 1 < ε) := by
  refine ⟨?_, ?_, ?_⟩
  · -- membership in the sweep family
    refine ⟨?_, ?_⟩
    · -- superharmonic on the region: inherited from `Ω ∩ V`
      refine (superharmonicOnX_glue hVo (le_of_lt (lt_max_of_lt_left one_pos)) hsup).mono
        (barrierMemberRegion_subset Ω V p ρ ρ₂ u) ?_
      have hcontu : ContinuousOn (fun x : X => min (u x) 1)
          (barrierMemberRegion Ω V p ρ ρ₂ u) :=
        (hcont.mono (Set.Subset.trans (barrierMemberRegion_subset Ω V p ρ ρ₂ u)
          Set.inter_subset_right)).inf (continuousOn_const (c := (1 : ℝ)))
      exact continuousOn_const.mul hcontu
    · -- domination of the cone on the region
      intro x hx
      have hxΩV : x ∈ Ω ∩ V := barrierMemberRegion_subset Ω V p ρ ρ₂ u hx
      have hxball : x ∈ Submission.chartBall (chartAt ℂ p) ((chartAt ℂ p) p) ρ₂ :=
        barrierMemberRegion_subset_chartBall Ω V p ρ ρ₂ u hx
      have hxlt : ‖(chartAt ℂ p) x - (chartAt ℂ p) p‖ < ρ₂ := by
        have h2 := (Submission.mem_chartBall.mp hxball).2
        rwa [Metric.mem_ball, dist_eq_norm] at h2
      have hu_pos : 0 < u x := hpos x hxΩV
      rcases hx.2 with ⟨hu1, -⟩ | hxρ
      · -- `u x > 1`: the glued function equals `lam`
        have hmin1 : min (u x) 1 = 1 := min_eq_right hu1.le
        have hG : chartCone (chartAt ℂ p) ((chartAt ℂ p) p) ρ x ≤ ρ₂ - ρ := by
          show max 0 (‖(chartAt ℂ p) x - (chartAt ℂ p) p‖ - ρ) ≤ ρ₂ - ρ
          exact max_le (by linarith) (by linarith)
        have hlam : ρ₂ - ρ ≤ max 1 (ρ₂ - ρ) := le_max_right _ _
        show chartCone (chartAt ℂ p) ((chartAt ℂ p) p) ρ x
          ≤ max 1 (ρ₂ - ρ) * min (u x) 1
        rw [hmin1, mul_one]
        linarith
      · -- inside the small chart ball: the cone vanishes
        have hG : chartCone (chartAt ℂ p) ((chartAt ℂ p) p) ρ x = 0 := by
          show max 0 (‖(chartAt ℂ p) x - (chartAt ℂ p) p‖ - ρ) = 0
          have h2 := (Submission.mem_chartBall.mp hxρ).2
          rw [Metric.mem_ball, dist_eq_norm] at h2
          exact max_eq_left (by linarith)
        show chartCone (chartAt ℂ p) ((chartAt ℂ p) p) ρ x
          ≤ max 1 (ρ₂ - ρ) * min (u x) 1
        rw [hG]
        exact mul_nonneg (le_of_lt (lt_max_of_lt_left one_pos)) (le_of_lt (lt_min hu_pos one_pos))
  · -- positivity on the region
    intro x hx
    have hxΩV : x ∈ Ω ∩ V := barrierMemberRegion_subset Ω V p ρ ρ₂ u hx
    exact mul_pos (lt_max_of_lt_left one_pos) (lt_min (hpos x hxΩV) one_pos)
  · -- small near `p`
    intro ε hε
    have hlampos : (0 : ℝ) < max 1 (ρ₂ - ρ) := lt_max_of_lt_left one_pos
    have hδ : 0 < ε / max 1 (ρ₂ - ρ) := div_pos hε hlampos
    have hcontp : ContinuousAt u p := hcont.continuousAt (hVo.mem_nhds hpV)
    have hev : ∀ᶠ x in 𝓝 p, u x < ε / max 1 (ρ₂ - ρ) :=
      hcontp.eventually (isOpen_Iio.mem_nhds (by rw [hup]; exact hδ))
    obtain ⟨N, hN, hNsub⟩ := Filter.eventually_iff_exists_mem.mp hev
    refine ⟨N, hN, fun x hx => ?_⟩
    have hxΩV : x ∈ Ω ∩ V := barrierMemberRegion_subset Ω V p ρ ρ₂ u hx.1
    have hvle : max 1 (ρ₂ - ρ) * min (u x) 1 ≤ max 1 (ρ₂ - ρ) * u x :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) hlampos.le
    have hux := hNsub x hx.2
    have : max 1 (ρ₂ - ρ) * u x < max 1 (ρ₂ - ρ) * (ε / max 1 (ρ₂ - ρ)) :=
      mul_lt_mul_of_pos_left hux hlampos
    calc max 1 (ρ₂ - ρ) * min (u x) 1 ≤ max 1 (ρ₂ - ρ) * u x := hvle
      _ < max 1 (ρ₂ - ρ) * (ε / max 1 (ρ₂ - ρ)) := this
      _ = ε := by field_simp

/-- **The region barrier produced by a local barrier.**  On the region `R` of
`barrierMemberRegion`, the sweep of the chart cone is harmonic, nonnegative, dominates the cone
(hence is strictly positive wherever the cone is, in particular outside the closed chart ball of
radius `ρ`), and is `< ε` on a neighbourhood of `p` (inside `R`). -/
theorem regionBarrierOfLocalBarrier {Ω V : Set X} (hΩo : IsOpen Ω) (hVo : IsOpen V) {p : X}
    (hpV : p ∈ V) {u : X → ℝ} (hsup : Submission.SuperharmonicOnX u (Ω ∩ V))
    (hpos : ∀ x ∈ Ω ∩ V, 0 < u x) (hcont : ContinuousOn u V) (hup : u p = 0)
    {ρ ρ₂ : ℝ} (hρ : 0 < ρ) (hρρ₂ : ρ < ρ₂)
    (htgt : Metric.closedBall ((chartAt ℂ p) p) ρ₂ ⊆ (chartAt ℂ p).target) :
    ∃ β : X → ℝ,
      β = Submission.sweep (chartCone (chartAt ℂ p) ((chartAt ℂ p) p) ρ)
        (barrierMemberRegion Ω V p ρ ρ₂ u) ∧
      Submission.HarmonicOnX β (barrierMemberRegion Ω V p ρ ρ₂ u) ∧
      (∀ x ∈ barrierMemberRegion Ω V p ρ ρ₂ u, 0 ≤ β x) ∧
      (∀ x ∈ barrierMemberRegion Ω V p ρ ρ₂ u,
        chartCone (chartAt ℂ p) ((chartAt ℂ p) p) ρ x ≤ β x) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N : Set X, N ∈ 𝓝 p ∧
        ∀ x ∈ barrierMemberRegion Ω V p ρ ρ₂ u ∩ N, β x < ε) := by
  obtain ⟨hmem, -, hvsmall⟩ :=
    memberOfLocalBarrier hΩo hVo hpV hsup hpos hcont hup hρ hρρ₂ htgt
  have hRsub : barrierMemberRegion Ω V p ρ ρ₂ u ⊆
      Submission.chartBall (chartAt ℂ p) ((chartAt ℂ p) p) ρ₂ :=
    barrierMemberRegion_subset_chartBall Ω V p ρ ρ₂ u
  have hsub : Submission.SubharmonicOnX
      (chartCone (chartAt ℂ p) ((chartAt ℂ p) p) ρ)
      (barrierMemberRegion Ω V p ρ ρ₂ u) := by
    have h0 := subharmonicOnX_chartCone_chartBall (p := p) hρ hρρ₂ htgt
    exact h0.mono hRsub (h0.1.mono hRsub)
  have hconst : (fun _ : X => ρ₂ - ρ) ∈ Submission.sweepFamily
      (chartCone (chartAt ℂ p) ((chartAt ℂ p) p) ρ) (barrierMemberRegion Ω V p ρ ρ₂ u) := by
    refine ⟨⟨continuousOn_const, fun x _ => ?_⟩, fun x hx => ?_⟩
    · exact (Submission.harmonicOnXAt_const (ρ₂ - ρ)).superharmonic
    · have hxlt : ‖(chartAt ℂ p) x - (chartAt ℂ p) p‖ < ρ₂ := by
        have h2 := (Submission.mem_chartBall.mp (hRsub hx)).2
        rwa [Metric.mem_ball, dist_eq_norm] at h2
      show chartCone (chartAt ℂ p) ((chartAt ℂ p) p) ρ x ≤ ρ₂ - ρ
      rw [chartCone]
      exact max_le (by linarith) (by linarith)
  have hRopen : IsOpen (barrierMemberRegion Ω V p ρ ρ₂ u) :=
    isOpen_barrierMemberRegion hΩo hVo hcont ρ ρ₂
  have hne : (Submission.sweepFamily (chartCone (chartAt ℂ p) ((chartAt ℂ p) p) ρ)
      (barrierMemberRegion Ω V p ρ ρ₂ u)).Nonempty := ⟨_, hconst⟩
  refine ⟨Submission.sweep (chartCone (chartAt ℂ p) ((chartAt ℂ p) p) ρ)
    (barrierMemberRegion Ω V p ρ ρ₂ u), rfl,
    Submission.sweep_harmonic hRopen hsub hne, ?_, ?_, ?_⟩
  · intro x hx
    exact Submission.sweep_nonneg hne (fun y _ => by
      show 0 ≤ chartCone (chartAt ℂ p) ((chartAt ℂ p) p) ρ y
      rw [chartCone]; exact le_max_left _ _) hx
  · intro x hx
    exact Submission.barrier_le_sweep hne hx
  · intro ε hε
    obtain ⟨N, hN, hNv⟩ := hvsmall ε hε
    exact ⟨N, hN, fun x hx =>
      lt_of_le_of_lt (Submission.sweep_le_of_mem hmem hx.1) (hNv x hx)⟩

/-- **Continuity of the sweep barrier across the interface `∂R` inside `Ω`.**  At a frontier point
`ξ` of the gluing region `R` that lies in `Ω ∩ V` (so that `u` is continuous there), the sweep of
the chart cone over `R` is bounded from inside `R` by the value of the member `λ · min (u ·) 1` at
`ξ`, up to `ε`: the sweep meets the member at the interface.  This is the frontier-limsup datum a
gluing/maximum-principle argument across `∂R` has to consume. -/
theorem regionBarrier_interface {Ω V : Set X} (hΩo : IsOpen Ω) (hVo : IsOpen V) {p : X}
    (hpV : p ∈ V) {u : X → ℝ} (hsup : Submission.SuperharmonicOnX u (Ω ∩ V))
    (hpos : ∀ x ∈ Ω ∩ V, 0 < u x) (hcont : ContinuousOn u V) (hup : u p = 0)
    {ρ ρ₂ : ℝ} (hρ : 0 < ρ) (hρρ₂ : ρ < ρ₂)
    (htgt : Metric.closedBall ((chartAt ℂ p) p) ρ₂ ⊆ (chartAt ℂ p).target) :
    ∀ ξ ∈ frontier (barrierMemberRegion Ω V p ρ ρ₂ u), ξ ∈ Ω ∩ V → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ x in 𝓝[barrierMemberRegion Ω V p ρ ρ₂ u] ξ,
        Submission.sweep (chartCone (chartAt ℂ p) ((chartAt ℂ p) p) ρ)
          (barrierMemberRegion Ω V p ρ ρ₂ u) x
        ≤ max 1 (ρ₂ - ρ) * min (u ξ) 1 + ε := by
  obtain ⟨hmem, -, -⟩ :=
    memberOfLocalBarrier hΩo hVo hpV hsup hpos hcont hup hρ hρρ₂ htgt
  intro ξ _ hξΩV ε hε
  have hcontv : ContinuousAt (fun x : X => max 1 (ρ₂ - ρ) * min (u x) 1) ξ :=
    ((hcont.continuousAt (hVo.mem_nhds hξΩV.2)).min continuousAt_const).const_mul
      (max 1 (ρ₂ - ρ))
  have hev : ∀ᶠ x in 𝓝 ξ,
      max 1 (ρ₂ - ρ) * min (u x) 1 ≤ max 1 (ρ₂ - ρ) * min (u ξ) 1 + ε := by
    have hlt : max 1 (ρ₂ - ρ) * min (u ξ) 1 < max 1 (ρ₂ - ρ) * min (u ξ) 1 + ε := by
      linarith
    have := hcontv.eventually (isOpen_Iio.mem_nhds hlt)
    filter_upwards [this] with y hy
    exact hy.le
  filter_upwards [hev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hxR
  exact le_trans (Submission.sweep_le_of_mem hmem hxR) hx

end Work.SimplyConnected.ABS
