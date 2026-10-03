import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.GreenSetupReg
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.clampedBarrierDefs

/-!
# A global barrier from a clamped collar

Let `Ω` be an open set in a Riemann surface `X`, `p ∈ frontier Ω`, and `u` a *local barrier* at `p`
(superharmonic and strictly positive on `Ω ∩ V`, continuous on the open set `V`, `u p = 0`).  Suppose
in addition that we are given an open set `S ⊆ Ω`, a neighbourhood `N` of `p` with `Ω ∩ N ⊆ S`, and
a *separation constant* `c ∈ (0,1]` such that on the part of the collar `frontier S` that meets `Ω`
the function `u` is bounded below by `c`, *eventually along `Ω`*:

`∀ ξ ∈ frontier S, ξ ∈ Ω → ∀ᶠ z in 𝓝[Ω] ξ, c ≤ u z`.

Then there is a global barrier on `Ω`: a superharmonic `w` on `Ω` with `0 < w ≤ 1` everywhere on `Ω`
and `w → 0` at `p` along `Ω`.

The construction is the clamped collar

`w := clampedBarrier u S c = if x ∈ S then min (u x) c else c`,

i.e. `min (u ·) c` inside the collar and the constant `c` outside it.  The point of the extra
hypothesis `hcollar` is that it makes the glueing *local*: at a point `ξ ∈ Ω ∩ frontier S` we have
`u ≥ c` on `Ω` near `ξ`, so the clamped function is literally equal to the constant `c` on a whole
neighbourhood of `ξ` — hence superharmonic there, with no circle-leaving-`S` issue.  At a point of
`S` the function agrees with `min (u ·) c` on the open set `S`; outside `closure S` it is the
constant `c`.  These three cases cover `Ω` (because `S` is open, `S = interior S`), and each is
handled by the germ-locality of superharmonicity at a point.

Everything is reduced to three elementary local lemmas about `Submission.SuperharmonicOnXAt`:
constants are superharmonic, the minimum with a constant is superharmonic, and superharmonicity at a
point only depends on the germ.
-/

open Filter Set
open scoped Topology

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-! ## Three local lemmas on `Submission.SuperharmonicOnXAt` -/

/-- A constant function is superharmonic at every point. -/
theorem superharmonicOnXAt_const_gbcc (k : ℝ) (x : X) :
    Submission.SuperharmonicOnXAt (fun _ : X => k) x := by
  rw [Submission.SuperharmonicOnXAt, Submission.SuperharmonicAtChart]
  have hxsrc : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp
    ((chartAt ℂ x).open_target.mem_nhds ((chartAt ℂ x).map_source hxsrc))
  refine ⟨hxsrc, ρ, hρ, hρsub, continuousOn_const, ?_⟩
  intro p hp r hr hpr
  have h1 : ((fun _ : X => k) ∘ (chartAt ℂ x).symm) = fun _ : ℂ => k := rfl
  rw [h1, Real.circleAverage_const]

/-- The pointwise minimum of a function superharmonic at `x` with a constant is superharmonic at
`x`. -/
theorem superharmonicOnXAt_inf_const_gbcc {u : X → ℝ} {x : X}
    (h : Submission.SuperharmonicOnXAt u x) (c : ℝ) :
    Submission.SuperharmonicOnXAt (fun y => min (u y) c) x := by
  rw [Submission.SuperharmonicOnXAt, Submission.SuperharmonicAtChart] at h ⊢
  obtain ⟨hxsrc, ρ, hρ, hρsub, hcont, hmvp⟩ := h
  have hfun : (fun y : X => min (u y) c) ∘ (chartAt ℂ x).symm
      = fun z : ℂ => min ((u ∘ (chartAt ℂ x).symm) z) c := rfl
  refine ⟨hxsrc, ρ, hρ, hρsub, ?_, ?_⟩
  · rw [hfun]; exact hcont.inf continuousOn_const
  · intro p hp r hr hpr
    have hclose : Metric.sphere p |r| ⊆ Metric.ball ((chartAt ℂ x) x) ρ := by
      intro z hz
      refine hpr ?_
      have hmem := Metric.sphere_subset_closedBall hz
      rwa [abs_of_pos hr] at hmem
    have hcont_f : ContinuousOn (u ∘ (chartAt ℂ x).symm) (Metric.sphere p |r|) :=
      hcont.mono hclose
    have hcont_g : ContinuousOn (fun z : ℂ => min ((u ∘ (chartAt ℂ x).symm) z) c)
        (Metric.sphere p |r|) := hcont_f.inf continuousOn_const
    have hint_g : CircleIntegrable (fun z : ℂ => min ((u ∘ (chartAt ℂ x).symm) z) c) p r :=
      hcont_g.circleIntegrable'
    have hint_f : CircleIntegrable (u ∘ (chartAt ℂ x).symm) p r := hcont_f.circleIntegrable'
    rw [hfun]
    refine le_min ?_ ?_
    · exact le_trans (Real.circleAverage_mono hint_g hint_f (fun z _ => min_le_left _ _))
        (hmvp p hp r hr hpr)
    · exact Real.circleAverage_mono_on_of_le_circle hint_g (fun z _ => min_le_right _ _)

/-- Superharmonicity at a point is a local condition: it depends only on the germ of the
function. -/
theorem superharmonicOnXAt_congr_gbcc {u v : X → ℝ} {x : X}
    (h : Submission.SuperharmonicOnXAt u x) (huv : u =ᶠ[𝓝 x] v) :
    Submission.SuperharmonicOnXAt v x := by
  rw [Submission.SuperharmonicOnXAt, Submission.SuperharmonicAtChart] at h ⊢
  obtain ⟨hxsrc, ρ, hρ, htarget, hcont, hmvp⟩ := h
  have hpre : ∀ᶠ z in 𝓝 ((chartAt ℂ x) x),
      (chartAt ℂ x).symm z ∈ {y : X | u y = v y} := by
    refine ((chartAt ℂ x).continuousAt_symm ((chartAt ℂ x).map_source hxsrc)).eventually ?_
    rw [(chartAt ℂ x).left_inv hxsrc]
    exact huv
  have htarget' : (chartAt ℂ x).target ∈ 𝓝 ((chartAt ℂ x) x) :=
    (chartAt ℂ x).open_target.mem_nhds ((chartAt ℂ x).map_source hxsrc)
  have hball' : Metric.ball ((chartAt ℂ x) x) ρ ∈ 𝓝 ((chartAt ℂ x) x) :=
    Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρ)
  have hS : ({z : ℂ | (chartAt ℂ x).symm z ∈ {y : X | u y = v y}} ∩
      ((chartAt ℂ x).target ∩ Metric.ball ((chartAt ℂ x) x) ρ)) ∈ 𝓝 ((chartAt ℂ x) x) :=
    Filter.inter_mem hpre (Filter.inter_mem htarget' hball')
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hS
  refine ⟨hxsrc, min δ ρ, lt_min hδ hρ, ?_, ?_, ?_⟩
  · intro z hz
    exact htarget (Metric.ball_subset_ball (min_le_right δ ρ) hz)
  · have heq : ∀ z ∈ Metric.ball ((chartAt ℂ x) x) (min δ ρ),
        (v ∘ (chartAt ℂ x).symm) z = (u ∘ (chartAt ℂ x).symm) z :=
      fun z hz => ((hδsub (Metric.ball_subset_ball (min_le_left δ ρ) hz)).1).symm
    exact (hcont.mono (Metric.ball_subset_ball (min_le_right δ ρ))).congr heq
  · intro p hp r hr hpr
    have hpδ : p ∈ Metric.ball ((chartAt ℂ x) x) δ :=
      Metric.ball_subset_ball (min_le_left δ ρ) hp
    have hp' : p ∈ Metric.ball ((chartAt ℂ x) x) ρ :=
      Metric.ball_subset_ball (min_le_right δ ρ) hp
    have hpr' : Metric.closedBall p r ⊆ Metric.ball ((chartAt ℂ x) x) ρ :=
      hpr.trans (Metric.ball_subset_ball (min_le_right δ ρ))
    have hsphere : Metric.sphere p r ⊆ Metric.ball ((chartAt ℂ x) x) δ :=
      fun z hz => Metric.ball_subset_ball (min_le_left δ ρ)
        (hpr (Metric.sphere_subset_closedBall hz))
    have hpq : (u ∘ (chartAt ℂ x).symm) p = (v ∘ (chartAt ℂ x).symm) p := (hδsub hpδ).1
    have havg : Real.circleAverage (u ∘ (chartAt ℂ x).symm) p r
        = Real.circleAverage (v ∘ (chartAt ℂ x).symm) p r := by
      refine Real.circleAverage_congr_sphere (fun z hz => ?_)
      exact (hδsub (hsphere (by simpa [abs_of_pos hr] using hz))).1
    rw [← hpq, ← havg]
    exact hmvp p hp' r hr hpr'

/-! ## The clamped collar is a global barrier -/

theorem globalBarrierOfClampedCollar {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {Ω V S : Set X} (hΩo : IsOpen Ω) (hSo : IsOpen S) (hVo : IsOpen V) (hSΩ : S ⊆ Ω)
    {p : X} (hp : p ∈ frontier Ω) (hSV : closure S ⊆ V)
    {u : X → ℝ} (hsup : Submission.SuperharmonicOnX u (Ω ∩ V))
    (hpos : ∀ x ∈ Ω ∩ V, 0 < u x) (hcont : ContinuousOn u V) (hup : u p = 0)
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hsep : ∀ ξ ∈ frontier S, ξ ∈ Ω → c ≤ u ξ)
    (hcollar : ∀ ξ ∈ frontier S, ξ ∈ Ω → Filter.Eventually (fun z => c ≤ u z) (nhdsWithin ξ Ω))
    {N : Set X} (hN : N ∈ nhds p) (hNS : Ω ∩ N ⊆ S) :
    ∃ w : X → ℝ, Submission.SuperharmonicOnX w Ω ∧ (∀ x ∈ Ω, 0 < w x) ∧
      (∀ x ∈ Ω, w x ≤ 1) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N' : Set X, N' ∈ nhds p ∧ ∀ x ∈ Ω ∩ N', w x < ε) := by
  -- `p` lies in the closure of `S`: `Ω ∩ N ⊆ S` and `p ∈ closure Ω`.
  have hpclS : p ∈ closure S := by
    refine mem_closure_iff_nhds.mpr ?_
    intro t ht
    obtain ⟨z, ⟨hzt, hzN⟩, hzΩ⟩ :=
      (mem_closure_iff_nhds.mp hp.1) (t ∩ N) (Filter.inter_mem ht hN)
    exact ⟨z, hzt, hNS ⟨hzΩ, hzN⟩⟩
  have hpV : p ∈ V := hSV hpclS
  -- superharmonicity of the clamped collar at every point of `Ω`
  have hAt : ∀ x ∈ Ω, Submission.SuperharmonicOnXAt (clampedBarrier u S c) x := by
    intro x hx
    by_cases hxS : x ∈ S
    · -- inside the collar: locally equal to `min (u ·) c`
      have hxV : x ∈ Ω ∩ V := ⟨hx, hSV (subset_closure hxS)⟩
      refine superharmonicOnXAt_congr_gbcc
        (superharmonicOnXAt_inf_const_gbcc (hsup.2 x hxV) c) ?_
      filter_upwards [hSo.mem_nhds hxS] with z hz
      exact (clampedBarrier_of_mem hz).symm
    · by_cases hxcl : x ∈ closure S
      · -- on the collar: locally the constant `c`, by the eventual separation `hcollar`
        have hxfr : x ∈ frontier S := ⟨hxcl, by rw [hSo.interior_eq]; exact hxS⟩
        obtain ⟨U, hU, t₂, ht₂, heq⟩ := Filter.mem_inf_iff.mp (hcollar x hxfr hx)
        have hUsub : ∀ z ∈ U, z ∈ Ω → c ≤ u z := by
          intro z hzU hzΩ
          have : z ∈ {z : X | c ≤ u z} := by
            rw [heq]; exact ⟨hzU, ht₂ hzΩ⟩
          exact this
        refine superharmonicOnXAt_congr_gbcc (superharmonicOnXAt_const_gbcc c x) ?_
        filter_upwards [hU] with z hz
        by_cases hzS : z ∈ S
        · rw [clampedBarrier_of_mem hzS]
          exact (min_eq_right (hUsub z hz (hSΩ hzS))).symm
        · rw [clampedBarrier_of_not_mem hzS]
      · -- outside the closure of the collar: locally the constant `c`
        refine superharmonicOnXAt_congr_gbcc (superharmonicOnXAt_const_gbcc c x) ?_
        filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxcl] with z hz
        exact (clampedBarrier_of_not_mem (fun hzS => hz (subset_closure hzS))).symm
  refine ⟨clampedBarrier u S c, ⟨?_, hAt⟩, ?_, ?_, ?_⟩
  · -- continuity on `Ω` follows from superharmonicity at every point of `Ω`
    intro x hx
    exact (Submission.SuperharmonicAtChart.continuousAt (hAt x hx)).continuousWithinAt
  · -- strict positivity
    intro x hx
    by_cases hxS : x ∈ S
    · rw [clampedBarrier_of_mem hxS]
      exact lt_min (hpos x ⟨hx, hSV (subset_closure hxS)⟩) hc
    · rw [clampedBarrier_of_not_mem hxS]
      exact hc
  · -- the upper bound `w ≤ 1`
    intro x hx
    by_cases hxS : x ∈ S
    · rw [clampedBarrier_of_mem hxS]
      exact le_trans (min_le_right _ _) hc1
    · rw [clampedBarrier_of_not_mem hxS]
      exact hc1
  · -- the decay at `p`
    intro ε hε
    have huclim : Tendsto u (𝓝 p) (𝓝 0) := by
      have h : Tendsto u (𝓝 p) (𝓝 (u p)) := hcont.continuousAt (hVo.mem_nhds hpV)
      rwa [hup] at h
    have hev : ∀ᶠ z in 𝓝 p, u z < ε := huclim.eventually (isOpen_Iio.mem_nhds hε)
    refine ⟨N ∩ {z : X | u z < ε}, Filter.inter_mem hN hev, ?_⟩
    intro x hx
    obtain ⟨hxΩ, hxN, hxu⟩ := hx
    rw [clampedBarrier_of_mem (hNS ⟨hxΩ, hxN⟩)]
    exact lt_of_le_of_lt (min_le_left _ _) hxu

end Work.SimplyConnected.ABS
