import ChallengeDeps
import Submission.Commons.Geometry.Manifold.chart_transition_analyticOnNhd
import Submission.Commons.Geometry.Manifold.harmonicAt_pullback_iff_chart
import Submission.Commons.Analysis.Complex.Harmonic.harmonicOnNhd_circleAverage_ge
import Submission.Commons.Analysis.Complex.Harmonic.circleMeanValue_ge_sup
import Submission.Commons.Analysis.Complex.Harmonic.circleMeanValue_ge_comp_biholo
import Submission.Commons.Analysis.Complex.Harmonic.circleAverage_ge_of_le_harmonic

/-!
# Harmonic, subharmonic and superharmonic functions on a Riemann surface

Subsystem (A) of the uniformization project: Hubbard, *Teichmüller theory* Vol. 1,
Definitions 1.2.1 and the surrounding calculus, stated on a complex manifold `X`.

* `Submission.HarmonicOnXAt u x` — the pullback of `u` by the preferred chart at `x` is
  harmonic (Mathlib `HarmonicAt`) at the image of `x`.  Chart independence is
  `Submission.HarmonicOnXAt_iff_chart`.
* `Submission.SubharmonicAtChart u c x` — in the coordinates of the chart `c`, the pullback
  `u ∘ c.symm` is continuous on a ball around `c x` and satisfies the circle mean-value
  inequality there (Hubbard's Definition 1.2.1 for subharmonic functions).
* `Submission.SubharmonicOnXAt u x` — the same in the preferred chart at `x`;
  `Submission.SubharmonicOnX u U` — subharmonic at every point of `U`.
* `Submission.SuperharmonicAtChart`, `Submission.SuperharmonicOnXAt`,
  `Submission.SuperharmonicOnX` — the superharmonic (reverse inequality) versions.

The chart-independence of the subharmonic notion is the content of the (commons) transport
lemma `Commons.Analysis.Complex.Harmonic.circleMeanValue_ge_comp_biholo`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Submission

/-- `u` is harmonic at `x` on the complex manifold `X`, measured in the preferred chart at `x`:
the pullback `u ∘ (chartAt ℂ x).symm` is harmonic (Mathlib `HarmonicAt`) at `(chartAt ℂ x) x`. -/
def HarmonicOnXAt {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] (u : X → ℝ) (x : X) : Prop :=
  InnerProductSpace.HarmonicAt (u ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)

/-- `u` is harmonic on the set `s ⊆ X`: harmonic at every point of `s`. -/
def HarmonicOnX {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] (u : X → ℝ) (s : Set X) : Prop :=
  ∀ x ∈ s, HarmonicOnXAt u x

/-- Chart independence of harmonicity at a point: harmonicity measured in the preferred chart
at `x` is equivalent to harmonicity measured in any other preferred chart whose source
contains `x` (commons `harmonicAt_pullback_iff_chart`). -/
theorem HarmonicOnXAt_iff_chart {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {u : X → ℝ} {x y : X}
    (hxy : x ∈ (chartAt ℂ y).source) :
    HarmonicOnXAt u x ↔
      InnerProductSpace.HarmonicAt (u ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x) :=
  Commons.Geometry.Manifold.harmonicAt_pullback_iff_chart hxy

/-- A function harmonic at a point is continuous there. -/
theorem HarmonicOnXAt.continuousAt {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {u : X → ℝ} {x : X} (h : HarmonicOnXAt u x) : ContinuousAt u x := by
  have hc : ContinuousAt (u ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) := h.1.continuousAt
  have hcx : ContinuousAt (chartAt ℂ x) x :=
    (chartAt ℂ x).continuousAt (mem_chart_source ℂ x)
  have hcomp : ContinuousAt (fun w : X => (u ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) w)) x :=
    hc.comp hcx
  refine hcomp.congr ?_
  filter_upwards [(chartAt ℂ x).open_source.eventually_mem (mem_chart_source ℂ x)] with w hw
  simp only [Function.comp_apply]
  rw [(chartAt ℂ x).left_inv hw]

/-- A function harmonic on all of `X` is continuous. -/
theorem HarmonicOnX_continuous {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {u : X → ℝ} (h : HarmonicOnX u univ) : Continuous u :=
  continuous_iff_continuousAt.mpr fun x => (h x (mem_univ x)).continuousAt

section LinearStructure

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] {x : X}

theorem HarmonicOnXAt.add {u v : X → ℝ} (hu : HarmonicOnXAt u x) (hv : HarmonicOnXAt v x) :
    HarmonicOnXAt (u + v) x := by
  have h := InnerProductSpace.HarmonicAt.add hu hv
  rw [HarmonicOnXAt]
  show InnerProductSpace.HarmonicAt
    (fun z => u ((chartAt ℂ x).symm z) + v ((chartAt ℂ x).symm z)) _
  exact h

theorem HarmonicOnXAt.sub {u v : X → ℝ} (hu : HarmonicOnXAt u x) (hv : HarmonicOnXAt v x) :
    HarmonicOnXAt (u - v) x := by
  have h := InnerProductSpace.HarmonicAt.sub hu hv
  rw [HarmonicOnXAt]
  show InnerProductSpace.HarmonicAt
    (fun z => u ((chartAt ℂ x).symm z) - v ((chartAt ℂ x).symm z)) _
  exact h

theorem HarmonicOnXAt.neg {u : X → ℝ} (hu : HarmonicOnXAt u x) : HarmonicOnXAt (-u) x := by
  have h := InnerProductSpace.HarmonicAt.neg hu
  rw [HarmonicOnXAt]
  show InnerProductSpace.HarmonicAt (fun z => -u ((chartAt ℂ x).symm z)) _
  exact h

theorem HarmonicOnXAt.const_smul {u : X → ℝ} (c : ℝ) (hu : HarmonicOnXAt u x) :
    HarmonicOnXAt (c • u) x := by
  have h := InnerProductSpace.HarmonicAt.const_smul (c := c) hu
  rw [HarmonicOnXAt]
  show InnerProductSpace.HarmonicAt (fun z => c * u ((chartAt ℂ x).symm z)) _
  exact h

@[simp]
theorem harmonicOnXAt_const (c : ℝ) : HarmonicOnXAt (fun _ : X => c) x := by
  rw [HarmonicOnXAt]
  show InnerProductSpace.HarmonicAt (fun _ : ℂ => c) _
  exact InnerProductSpace.harmonicAt_const c

end LinearStructure

section SetLevel

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] {s : Set X}

theorem HarmonicOnX.mono {u : X → ℝ} {s t : Set X} (h : HarmonicOnX u t) (hst : s ⊆ t) :
    HarmonicOnX u s := fun x hx => h x (hst hx)

theorem HarmonicOnX.add {u v : X → ℝ} (hu : HarmonicOnX u s) (hv : HarmonicOnX v s) :
    HarmonicOnX (u + v) s := fun x hx => (hu x hx).add (hv x hx)

theorem HarmonicOnX.sub {u v : X → ℝ} (hu : HarmonicOnX u s) (hv : HarmonicOnX v s) :
    HarmonicOnX (u - v) s := fun x hx => (hu x hx).sub (hv x hx)

theorem HarmonicOnX.neg {u : X → ℝ} (hu : HarmonicOnX u s) : HarmonicOnX (-u) s :=
  fun x hx => (hu x hx).neg

theorem HarmonicOnX.const_smul {u : X → ℝ} (c : ℝ) (hu : HarmonicOnX u s) :
    HarmonicOnX (c • u) s := fun x hx => (hu x hx).const_smul c

@[simp]
theorem harmonicOnX_const (c : ℝ) : HarmonicOnX (fun _ : X => c) s :=
  fun _ _ => harmonicOnXAt_const c

end SetLevel

/-! ## Subharmonic and superharmonic functions (Hubbard Definition 1.2.1)

The definition is stated in the coordinates of a single chart: the pullback of `u` is
continuous on a ball around the image of the base point and satisfies the circle mean-value
inequality on that ball.  The chart-independence of this notion is proved later. -/

section Subharmonic

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- A ball contained in a larger ball, with the natural radius: if `b ∈ ball a ρ` then
`ball b (ρ - dist b a) ⊆ ball a ρ`. -/
theorem ball_subset_ball_of_mem {a b : ℂ} {ρ : ℝ} (_hb : b ∈ Metric.ball a ρ) :
    Metric.ball b (ρ - dist b a) ⊆ Metric.ball a ρ := by
  intro z hz
  rw [Metric.mem_ball] at hz ⊢
  have h1 : dist z a ≤ dist z b + dist b a := dist_triangle _ _ _
  linarith [dist_nonneg (x := b) (y := a)]

/-- In the coordinates of the chart `c`, the pullback `u ∘ c.symm` is continuous on a ball
around `c x` and satisfies the circle mean-value inequality on that ball.  This is Hubbard's
Definition 1.2.1 for subharmonic functions, expressed in the coordinates of one chart. -/
def SubharmonicAtChart (u : X → ℝ) (c : OpenPartialHomeomorph X ℂ) (x : X) : Prop :=
  x ∈ c.source ∧ ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball (c x) ρ ⊆ c.target ∧
    ContinuousOn (u ∘ c.symm) (Metric.ball (c x) ρ) ∧
    ∀ p ∈ Metric.ball (c x) ρ, ∀ r : ℝ, 0 < r →
      Metric.closedBall p r ⊆ Metric.ball (c x) ρ →
      (u ∘ c.symm) p ≤ Real.circleAverage (u ∘ c.symm) p r

/-- In the coordinates of the chart `c`, the pullback `u ∘ c.symm` is continuous on a ball
around `c x` and satisfies the reverse circle mean-value inequality on that ball
(superharmonic functions, Hubbard Definition 1.2.1). -/
def SuperharmonicAtChart (u : X → ℝ) (c : OpenPartialHomeomorph X ℂ) (x : X) : Prop :=
  x ∈ c.source ∧ ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball (c x) ρ ⊆ c.target ∧
    ContinuousOn (u ∘ c.symm) (Metric.ball (c x) ρ) ∧
    ∀ p ∈ Metric.ball (c x) ρ, ∀ r : ℝ, 0 < r →
      Metric.closedBall p r ⊆ Metric.ball (c x) ρ →
      Real.circleAverage (u ∘ c.symm) p r ≤ (u ∘ c.symm) p

/-- `u` is subharmonic at `x` (Hubbard's Definition 1.2.1), measured in the preferred
chart at `x`. -/
def SubharmonicOnXAt (u : X → ℝ) (x : X) : Prop := SubharmonicAtChart u (chartAt ℂ x) x

/-- `u` is superharmonic at `x` (Hubbard's Definition 1.2.1), measured in the preferred
chart at `x`. -/
def SuperharmonicOnXAt (u : X → ℝ) (x : X) : Prop := SuperharmonicAtChart u (chartAt ℂ x) x

/-- `u` is subharmonic on the set `U`: it is continuous on `U` and subharmonic at every
point of `U`. -/
def SubharmonicOnX (u : X → ℝ) (U : Set X) : Prop :=
  ContinuousOn u U ∧ ∀ x ∈ U, SubharmonicOnXAt u x

/-- `u` is superharmonic on the set `U`: it is continuous on `U` and superharmonic at every
point of `U`. -/
def SuperharmonicOnX (u : X → ℝ) (U : Set X) : Prop :=
  ContinuousOn u U ∧ ∀ x ∈ U, SuperharmonicOnXAt u x

/-- The circle mean-value inequality for the pullback by `c` is a local condition: it holds at
`y` as soon as it holds at some `x` whose image `c x` is close to `c y`. -/
theorem SubharmonicAtChart.of_mem {u : X → ℝ} {c : OpenPartialHomeomorph X ℂ} {x y : X} {ρ : ℝ}
    (hx : x ∈ c.source) (hy : y ∈ c.source) (hρ : 0 < ρ) (htarget : Metric.ball (c x) ρ ⊆ c.target)
    (hcont : ContinuousOn (u ∘ c.symm) (Metric.ball (c x) ρ))
    (hMVP : ∀ p ∈ Metric.ball (c x) ρ, ∀ r : ℝ, 0 < r →
      Metric.closedBall p r ⊆ Metric.ball (c x) ρ →
      (u ∘ c.symm) p ≤ Real.circleAverage (u ∘ c.symm) p r)
    (hyb : c y ∈ Metric.ball (c x) ρ) : SubharmonicAtChart u c y := by
  have hd : 0 < ρ - dist (c y) (c x) := sub_pos.mpr (Metric.mem_ball.mp hyb)
  have hsub : Metric.ball (c y) (ρ - dist (c y) (c x)) ⊆ Metric.ball (c x) ρ :=
    ball_subset_ball_of_mem hyb
  refine ⟨hy, ρ - dist (c y) (c x), hd, hsub.trans htarget, ?_, ?_⟩
  · exact hcont.mono hsub
  · intro p hp r hr hpr
    exact hMVP p (hsub hp) r hr (hpr.trans hsub)

/-- A function subharmonic at `x` in a chart is continuous at `x` (the chart is a
homeomorphism onto its target). -/
theorem SubharmonicAtChart.continuousAt {u : X → ℝ} {c : OpenPartialHomeomorph X ℂ} {x : X}
    (h : SubharmonicAtChart u c x) : ContinuousAt u x := by
  obtain ⟨hxsrc, ρ, hρ, _, hcont, _⟩ := h
  have hx : c x ∈ Metric.ball (c x) ρ := Metric.mem_ball_self hρ
  have h1 : ContinuousAt (u ∘ c.symm) (c x) :=
    hcont.continuousAt (Metric.isOpen_ball.mem_nhds hx)
  have h2 : ContinuousAt c x := c.continuousAt hxsrc
  have h3 : ContinuousAt (fun y : X => (u ∘ c.symm) (c y)) x := h1.comp h2
  refine h3.congr ?_
  filter_upwards [c.open_source.eventually_mem hxsrc] with y hy
  simp only [Function.comp_apply]
  rw [c.left_inv hy]

/-- A function superharmonic at `x` in a chart is continuous at `x`. -/
theorem SuperharmonicAtChart.continuousAt {u : X → ℝ} {c : OpenPartialHomeomorph X ℂ} {x : X}
    (h : SuperharmonicAtChart u c x) : ContinuousAt u x := by
  obtain ⟨hxsrc, ρ, hρ, _, hcont, _⟩ := h
  have hx : c x ∈ Metric.ball (c x) ρ := Metric.mem_ball_self hρ
  have h1 : ContinuousAt (u ∘ c.symm) (c x) :=
    hcont.continuousAt (Metric.isOpen_ball.mem_nhds hx)
  have h2 : ContinuousAt c x := c.continuousAt hxsrc
  have h3 : ContinuousAt (fun y : X => (u ∘ c.symm) (c y)) x := h1.comp h2
  refine h3.congr ?_
  filter_upwards [c.open_source.eventually_mem hxsrc] with y hy
  simp only [Function.comp_apply]
  rw [c.left_inv hy]

/-- A function subharmonic at a point is continuous there. -/
theorem SubharmonicOnXAt.continuousAt {u : X → ℝ} {x : X} (h : SubharmonicOnXAt u x) :
    ContinuousAt u x :=
  SubharmonicAtChart.continuousAt h

/-- A function superharmonic at a point is continuous there. -/
theorem SuperharmonicOnXAt.continuousAt {u : X → ℝ} {x : X} (h : SuperharmonicOnXAt u x) :
    ContinuousAt u x :=
  SuperharmonicAtChart.continuousAt h

/-- Subharmonicity at a point is a local condition: two functions that agree on a neighbourhood of
`x` are subharmonic there simultaneously. -/
theorem SubharmonicOnXAt.congr {u v : X → ℝ} {x : X} (h : SubharmonicOnXAt u x)
    (huv : u =ᶠ[𝓝 x] v) : SubharmonicOnXAt v x := by
  rw [SubharmonicOnXAt, SubharmonicAtChart] at h ⊢
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
    have hpδ : p ∈ Metric.ball ((chartAt ℂ x) x) δ := Metric.ball_subset_ball (min_le_left δ ρ) hp
    have hp' : p ∈ Metric.ball ((chartAt ℂ x) x) ρ := Metric.ball_subset_ball (min_le_right δ ρ) hp
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

/-- A harmonic function is subharmonic. -/
theorem HarmonicOnXAt.subharmonic {u : X → ℝ} {x : X} (h : HarmonicOnXAt u x) :
    SubharmonicOnXAt u x := by
  have hv_open : IsOpen {z : ℂ |
      InnerProductSpace.HarmonicAt (u ∘ (chartAt ℂ x).symm) z} :=
    InnerProductSpace.isOpen_setOfPred_harmonicAt _
  obtain ⟨ρ₁, hρ₁, hρ₁sub⟩ := Metric.isOpen_iff.mp hv_open ((chartAt ℂ x) x) h
  obtain ⟨ρ₂, hρ₂, hρ₂sub⟩ := Metric.mem_nhds_iff.mp (chart_target_mem_nhds ℂ x)
  refine ⟨mem_chart_source ℂ x, min ρ₁ ρ₂, lt_min hρ₁ hρ₂,
    (Metric.ball_subset_ball (min_le_right ρ₁ ρ₂)).trans hρ₂sub, ?_, ?_⟩
  · refine continuousOn_of_forall_continuousAt fun z hz => ?_
    have hz₁ : z ∈ Metric.ball ((chartAt ℂ x) x) ρ₁ :=
      Metric.ball_subset_ball (min_le_left ρ₁ ρ₂) hz
    exact (hρ₁sub hz₁).1.continuousAt
  · intro p hp r hr hpr
    have hsub₁ : Metric.closedBall p r ⊆ Metric.ball ((chartAt ℂ x) x) ρ₁ :=
      hpr.trans (Metric.ball_subset_ball (min_le_left ρ₁ ρ₂))
    have hharm : InnerProductSpace.HarmonicOnNhd (u ∘ (chartAt ℂ x).symm) (Metric.closedBall p |r|) := by
      rw [abs_of_pos hr]
      intro z hz
      exact hρ₁sub (hsub₁ hz)
    exact (InnerProductSpace.HarmonicOnNhd.circleAverage_eq hharm).ge

/-- A harmonic function is superharmonic. -/
theorem HarmonicOnXAt.superharmonic {u : X → ℝ} {x : X} (h : HarmonicOnXAt u x) :
    SuperharmonicOnXAt u x := by
  have hv_open : IsOpen {z : ℂ |
      InnerProductSpace.HarmonicAt (u ∘ (chartAt ℂ x).symm) z} :=
    InnerProductSpace.isOpen_setOfPred_harmonicAt _
  obtain ⟨ρ₁, hρ₁, hρ₁sub⟩ := Metric.isOpen_iff.mp hv_open ((chartAt ℂ x) x) h
  obtain ⟨ρ₂, hρ₂, hρ₂sub⟩ := Metric.mem_nhds_iff.mp (chart_target_mem_nhds ℂ x)
  refine ⟨mem_chart_source ℂ x, min ρ₁ ρ₂, lt_min hρ₁ hρ₂,
    (Metric.ball_subset_ball (min_le_right ρ₁ ρ₂)).trans hρ₂sub, ?_, ?_⟩
  · refine continuousOn_of_forall_continuousAt fun z hz => ?_
    have hz₁ : z ∈ Metric.ball ((chartAt ℂ x) x) ρ₁ :=
      Metric.ball_subset_ball (min_le_left ρ₁ ρ₂) hz
    exact (hρ₁sub hz₁).1.continuousAt
  · intro p hp r hr hpr
    have hsub₁ : Metric.closedBall p r ⊆ Metric.ball ((chartAt ℂ x) x) ρ₁ :=
      hpr.trans (Metric.ball_subset_ball (min_le_left ρ₁ ρ₂))
    have hharm : InnerProductSpace.HarmonicOnNhd (u ∘ (chartAt ℂ x).symm) (Metric.closedBall p |r|) := by
      rw [abs_of_pos hr]
      intro z hz
      exact hρ₁sub (hsub₁ hz)
    exact le_of_eq (InnerProductSpace.HarmonicOnNhd.circleAverage_eq hharm)

/-- The set-level version: a harmonic function is subharmonic. -/
theorem HarmonicOnX.subharmonic {u : X → ℝ} {U : Set X} (h : HarmonicOnX u U)
    (hu : ContinuousOn u U) : SubharmonicOnX u U :=
  ⟨hu, fun x hx => (h x hx).subharmonic⟩

/-- The set-level version: a harmonic function is superharmonic. -/
theorem HarmonicOnX.superharmonic {u : X → ℝ} {U : Set X} (h : HarmonicOnX u U)
    (hu : ContinuousOn u U) : SuperharmonicOnX u U :=
  ⟨hu, fun x hx => (h x hx).superharmonic⟩

/-- The pointwise maximum of two functions subharmonic at `x` is subharmonic at `x`
(Hubbard: "we can take sups of subharmonic functions"). -/
theorem SubharmonicOnXAt.sup {u v : X → ℝ} {x : X} (hu : SubharmonicOnXAt u x)
    (hv : SubharmonicOnXAt v x) : SubharmonicOnXAt (max u v) x := by
  rw [SubharmonicOnXAt, SubharmonicAtChart] at hu hv ⊢
  obtain ⟨hx, ρ₁, hρ₁, ht₁, hc₁, hm₁⟩ := hu
  obtain ⟨_, ρ₂, hρ₂, ht₂, hc₂, hm₂⟩ := hv
  have hρpos : 0 < min ρ₁ ρ₂ := lt_min hρ₁ hρ₂
  have hsub₁ : Metric.ball ((chartAt ℂ x) x) (min ρ₁ ρ₂) ⊆ Metric.ball ((chartAt ℂ x) x) ρ₁ :=
    Metric.ball_subset_ball (min_le_left _ _)
  have hsub₂ : Metric.ball ((chartAt ℂ x) x) (min ρ₁ ρ₂) ⊆ Metric.ball ((chartAt ℂ x) x) ρ₂ :=
    Metric.ball_subset_ball (min_le_right _ _)
  refine ⟨hx, min ρ₁ ρ₂, hρpos, hsub₁.trans ht₁, ?_, ?_⟩
  · exact (hc₁.mono hsub₁).sup (hc₂.mono hsub₂)
  · intro p hp r hr hpr
    exact (Commons.Analysis.Complex.Harmonic.circleMeanValue_ge_sup Metric.isOpen_ball
      (hc₁.mono hsub₁) (hc₂.mono hsub₂)
      (fun q hq s hs hcs => hm₁ q (hsub₁ hq) s hs (hcs.trans hsub₁))
      (fun q hq s hs hcs => hm₂ q (hsub₂ hq) s hs (hcs.trans hsub₂))).2 p hp r hr hpr

/-- The pointwise maximum of two subharmonic functions on `U` is subharmonic on `U`. -/
theorem SubharmonicOnX.sup {u v : X → ℝ} {U : Set X} (hu : SubharmonicOnX u U)
    (hv : SubharmonicOnX v U) : SubharmonicOnX (max u v) U :=
  ⟨hu.1.sup hv.1, fun x hx => (hu.2 x hx).sup (hv.2 x hx)⟩

theorem SubharmonicOnX.mono {u : X → ℝ} {U V : Set X} (h : SubharmonicOnX u V) (hUV : U ⊆ V)
    (hu : ContinuousOn u U) : SubharmonicOnX u U :=
  ⟨hu, fun x hx => h.2 x (hUV hx)⟩

theorem SuperharmonicOnX.mono {u : X → ℝ} {U V : Set X} (h : SuperharmonicOnX u V) (hUV : U ⊆ V)
    (hu : ContinuousOn u U) : SuperharmonicOnX u U :=
  ⟨hu, fun x hx => h.2 x (hUV hx)⟩

end Subharmonic

/-! ## Harmonic replacement in a chart disc

Hubbard's Definition 1.2.2 (3) refers to the continuous function that agrees with `f` outside a
disc `D` in the image of a chart and is harmonic in `D`.  We set up this construction: `chartBall`
is the disc on `X` cut out by a chart and a Euclidean ball, `replaceOnDisc` is the replacement
itself (a function on `X`), and `gluedBall` is the corresponding glued function on `ℂ` whose
continuity is supplied by the Dirichlet problem on a ball. -/

section Replacement

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- The chart ball: the set of points whose image under the chart lies in the Euclidean ball
`Metric.ball a ρ`. -/
def chartBall (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ : ℝ) : Set X :=
  c.source ∩ c ⁻¹' Metric.ball a ρ

/-- The closed chart disc: the set of points whose image under the chart lies in the closed
Euclidean ball `Metric.closedBall a ρ`. -/
def chartClosedBall (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ : ℝ) : Set X :=
  c.source ∩ c ⁻¹' Metric.closedBall a ρ

theorem mem_chartBall {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ} {x : X} :
    x ∈ chartBall c a ρ ↔ x ∈ c.source ∧ c x ∈ Metric.ball a ρ := Iff.rfl

theorem mem_chartClosedBall {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ} {x : X} :
    x ∈ chartClosedBall c a ρ ↔ x ∈ c.source ∧ c x ∈ Metric.closedBall a ρ := Iff.rfl

theorem chartBall_isOpen (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ : ℝ) :
    IsOpen (chartBall c a ρ) :=
  c.continuousOn.isOpen_inter_preimage c.open_source Metric.isOpen_ball

theorem chartBall_subset_source (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ : ℝ) :
    chartBall c a ρ ⊆ c.source := inter_subset_left

theorem chartClosedBall_subset_source (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ : ℝ) :
    chartClosedBall c a ρ ⊆ c.source := inter_subset_left

theorem chartBall_subset_chartClosedBall (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ : ℝ) :
    chartBall c a ρ ⊆ chartClosedBall c a ρ :=
  fun _ hx => ⟨hx.1, Metric.ball_subset_closedBall hx.2⟩

/-- Inside the chart source, the closed chart disc is the image of the closed Euclidean ball
(no junk values appear, since the closed ball is assumed to lie in the chart target). -/
theorem chartClosedBall_eq_image {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ}
    (hsub : Metric.closedBall a ρ ⊆ c.target) :
    chartClosedBall c a ρ = c.symm '' Metric.closedBall a ρ := by
  ext x
  constructor
  · rintro ⟨hx, hcx⟩
    exact ⟨c x, hcx, c.left_inv hx⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨c.map_target (hsub hz), ?_⟩
    show c (c.symm z) ∈ Metric.closedBall a ρ
    rw [c.right_inv (hsub hz)]
    exact hz

theorem isCompact_chartClosedBall {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ}
    (hsub : Metric.closedBall a ρ ⊆ c.target) : IsCompact (chartClosedBall c a ρ) := by
  rw [chartClosedBall_eq_image hsub]
  exact (isCompact_closedBall a ρ).image_of_continuousOn (c.continuousOn_symm.mono hsub)

theorem isClosed_chartClosedBall [T2Space X] {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ}
    (hsub : Metric.closedBall a ρ ⊆ c.target) : IsClosed (chartClosedBall c a ρ) :=
  (isCompact_chartClosedBall hsub).isClosed

theorem closure_chartBall_subset_chartClosedBall [T2Space X] {c : OpenPartialHomeomorph X ℂ}
    {a : ℂ} {ρ : ℝ} (hsub : Metric.closedBall a ρ ⊆ c.target) :
    closure (chartBall c a ρ) ⊆ chartClosedBall c a ρ :=
  closure_minimal (chartBall_subset_chartClosedBall c a ρ) (isClosed_chartClosedBall hsub)

/-- The function glued from `u` inside the Euclidean ball and `F` outside it. -/
def gluedBall (u F : ℂ → ℝ) (a : ℂ) (ρ : ℝ) : ℂ → ℝ :=
  fun w => if w ∈ Metric.ball a ρ then u w else F w

@[simp]
theorem gluedBall_apply (u F : ℂ → ℝ) (a : ℂ) (ρ : ℝ) (w : ℂ) :
    gluedBall u F a ρ w = if w ∈ Metric.ball a ρ then u w else F w := rfl

theorem gluedBall_of_mem {u F : ℂ → ℝ} {a : ℂ} {ρ : ℝ} {w : ℂ}
    (hw : w ∈ Metric.ball a ρ) : gluedBall u F a ρ w = u w := if_pos hw

theorem gluedBall_of_not_mem {u F : ℂ → ℝ} {a : ℂ} {ρ : ℝ} {w : ℂ}
    (hw : w ∉ Metric.ball a ρ) : gluedBall u F a ρ w = F w := if_neg hw

/-- The glued function is continuous at a point where the inner function has the correct
one-sided limits (supplied in the form of continuity of the glued function on the closed ball,
as delivered by the Dirichlet problem) and the outer function is continuous. -/
theorem continuousAt_gluedBall {u F : ℂ → ℝ} {a : ℂ} {ρ : ℝ} {z : ℂ}
    (hG : ContinuousOn (gluedBall u F a ρ) (Metric.closedBall a ρ))
    (hu : ContinuousOn u (Metric.ball a ρ)) (hF : ContinuousAt F z) :
    ContinuousAt (gluedBall u F a ρ) z := by
  by_cases hzb : z ∈ Metric.ball a ρ
  · have heq : gluedBall u F a ρ =ᶠ[𝓝 z] u := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hzb] with w hw
      exact gluedBall_of_mem hw
    exact (hu.continuousAt (Metric.isOpen_ball.mem_nhds hzb)).congr heq.symm
  · by_cases hzc : z ∈ Metric.closedBall a ρ
    · have hsplit : 𝓝 z = 𝓝[Metric.ball a ρ] z ⊔ 𝓝[(Metric.ball a ρ)ᶜ] z := by
        rw [← nhdsWithin_union, union_compl_self, nhdsWithin_univ]
      have h1 : Tendsto (gluedBall u F a ρ) (𝓝[Metric.ball a ρ] z)
          (𝓝 (gluedBall u F a ρ z)) :=
        (hG.continuousWithinAt hzc).mono Metric.ball_subset_closedBall
      have h2 : Tendsto (gluedBall u F a ρ) (𝓝[(Metric.ball a ρ)ᶜ] z)
          (𝓝 (gluedBall u F a ρ z)) := by
        have hGF : gluedBall u F a ρ =ᶠ[𝓝[(Metric.ball a ρ)ᶜ] z] F := by
          filter_upwards [self_mem_nhdsWithin] with w hw
          exact gluedBall_of_not_mem hw
        have hF' : Tendsto F (𝓝[(Metric.ball a ρ)ᶜ] z) (𝓝 (F z)) :=
          hF.tendsto.mono_left nhdsWithin_le_nhds
        have hz : gluedBall u F a ρ z = F z := gluedBall_of_not_mem hzb
        have h := Filter.Tendsto.congr' hGF.symm hF'
        simpa [hzb] using h
      have hall : Tendsto (gluedBall u F a ρ) (𝓝 z) (𝓝 (gluedBall u F a ρ z)) := by
        rw [hsplit, tendsto_sup]
        exact ⟨h1, h2⟩
      exact hall
    · have heq : gluedBall u F a ρ =ᶠ[𝓝 z] F := by
        filter_upwards [Metric.isClosed_closedBall.isOpen_compl.mem_nhds hzc] with w hw
        exact gluedBall_of_not_mem (fun hwb => hw (Metric.ball_subset_closedBall hwb))
      exact hF.congr heq.symm

/-- The harmonic replacement of `f` in the chart disc `chartBall c a ρ`: it equals `u ∘ c` in
the disc and `f` outside it.  Here `u` is meant to be the harmonic extension of the boundary
values `f ∘ c.symm` on `Metric.sphere a ρ`. -/
def replaceOnDisc (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ : ℝ) (u : ℂ → ℝ)
    (f : X → ℝ) : X → ℝ :=
  fun x => if x ∈ chartBall c a ρ then u (c x) else f x

theorem replaceOnDisc_of_mem_chartBall {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ}
    {u : ℂ → ℝ} {f : X → ℝ} {x : X} (hx : x ∈ chartBall c a ρ) :
    replaceOnDisc c a ρ u f x = u (c x) := if_pos hx

theorem replaceOnDisc_of_not_mem_chartBall {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ}
    {u : ℂ → ℝ} {f : X → ℝ} {x : X} (hx : x ∉ chartBall c a ρ) :
    replaceOnDisc c a ρ u f x = f x := if_neg hx

/-- The pullback of the replacement by the chart `c` is the glued function. -/
theorem replaceOnDisc_eq_glued {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ} {u : ℂ → ℝ}
    {f : X → ℝ} {x : X} (hx : x ∈ c.source) :
    replaceOnDisc c a ρ u f x = gluedBall u (fun w => f (c.symm w)) a ρ (c x) := by
  rw [gluedBall_apply]
  by_cases h : c x ∈ Metric.ball a ρ
  · rw [replaceOnDisc_of_mem_chartBall (show x ∈ chartBall c a ρ from ⟨hx, h⟩), if_pos h]
  · rw [replaceOnDisc_of_not_mem_chartBall (fun hc => h hc.2), if_neg h, c.left_inv hx]

theorem replaceOnDisc_symm {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ} {u : ℂ → ℝ}
    {f : X → ℝ} {z : ℂ} (hz : z ∈ c.target) :
    replaceOnDisc c a ρ u f (c.symm z) = gluedBall u (fun w => f (c.symm w)) a ρ z := by
  rw [replaceOnDisc_eq_glued (c.map_target hz), c.right_inv hz]

/-- Inside the disc, the pullback of the replacement by the chart is the harmonic function `u`. -/
theorem replaceOnDisc_pullback_of_mem {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ}
    {u : ℂ → ℝ} {f : X → ℝ} (hsub : Metric.ball a ρ ⊆ c.target)
    {z : ℂ} (hz : z ∈ Metric.ball a ρ) :
    replaceOnDisc c a ρ u f (c.symm z) = u z := by
  rw [replaceOnDisc_symm (hsub hz), gluedBall_of_mem hz]

/-- The replacement is continuous, provided the glued function on `ℂ` is continuous on the
closed disc (as delivered by the Dirichlet problem on a ball) and `f` is continuous. -/
theorem continuous_replaceOnDisc [T2Space X] {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ}
    {u : ℂ → ℝ} {f : X → ℝ} (hsub : Metric.closedBall a ρ ⊆ c.target) (hf : Continuous f)
    (hu : ContinuousOn u (Metric.ball a ρ))
    (hG : ContinuousOn (gluedBall u (fun w => f (c.symm w)) a ρ) (Metric.closedBall a ρ)) :
    Continuous (replaceOnDisc c a ρ u f) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  by_cases hx₀ : x₀ ∈ c.source
  · have hGeq : gluedBall u (fun w => f (c.symm w)) a ρ ∘ c
        =ᶠ[𝓝 x₀] replaceOnDisc c a ρ u f := by
      filter_upwards [c.open_source.mem_nhds hx₀] with x hx
      exact (replaceOnDisc_eq_glued hx).symm
    have hGA : ContinuousAt (gluedBall u (fun w => f (c.symm w)) a ρ) (c x₀) :=
      continuousAt_gluedBall hG hu
        ((hf.continuousAt).comp (c.continuousAt_symm (c.map_source hx₀)))
    exact (hGA.comp (c.continuousAt hx₀)).congr hGeq
  · have hxcompl : x₀ ∈ (chartClosedBall c a ρ)ᶜ :=
      fun hc => hx₀ (chartClosedBall_subset_source c a ρ hc)
    have hnb : (chartBall c a ρ)ᶜ ∈ 𝓝 x₀ :=
      Filter.mem_of_superset ((isClosed_chartClosedBall hsub).isOpen_compl.mem_nhds hxcompl)
        (compl_subset_compl.mpr (chartBall_subset_chartClosedBall c a ρ))
    have heq : f =ᶠ[𝓝 x₀] replaceOnDisc c a ρ u f := by
      filter_upwards [hnb] with x hx
      exact (replaceOnDisc_of_not_mem_chartBall hx).symm
    exact hf.continuousAt.congr heq

/-- Membership in the source of a transition of partial homeomorphisms, in coordinates: the
transition from `c`-coordinates to `d`-coordinates is defined exactly on those `z` in the target
of `c` whose `c`-preimage lies in the source of `d`. -/
theorem mem_trans_source {X : Type*} [TopologicalSpace X] {c d : OpenPartialHomeomorph X ℂ}
    {z : ℂ} : z ∈ (c.symm.trans d).source ↔ z ∈ c.target ∧ c.symm z ∈ d.source := by
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source, Set.mem_inter_iff,
    Set.mem_preimage]

/-- Membership in the source of the reverse transition. -/
theorem mem_trans_symm_source {X : Type*} [TopologicalSpace X] {c d : OpenPartialHomeomorph X ℂ}
    {z : ℂ} : z ∈ (d.symm.trans c).source ↔ z ∈ d.target ∧ d.symm z ∈ c.source :=
  mem_trans_source (c := d) (d := c)

/-- The two pullbacks of `u` by two charts agree where the transition is defined. -/
theorem pullback_comp_transition {X : Type*} [TopologicalSpace X] {u : X → ℝ}
    {c d : OpenPartialHomeomorph X ℂ} {z : ℂ} (hz : d.symm z ∈ c.source) :
    (u ∘ c.symm) (c (d.symm z)) = (u ∘ d.symm) z := by
  simp only [Function.comp_apply]
  rw [c.left_inv hz]

end Replacement

/-! ## Perron families (Hubbard Definition 1.2.2)

Following Hubbard, a Perron family is a nonempty set `F` of subharmonic functions on `X`, bounded
by `M`, closed under pointwise maxima and closed under harmonic replacement in discs lying in the
image of a chart. -/

section Perron

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- Hubbard's Definition 1.2.2 (in the form needed below): `F` is a Perron family bounded above by
`M` if it is nonempty, consists of subharmonic functions, is bounded above by `M`, is closed under
pointwise maxima and is closed under harmonic replacement in chart discs.  The replacement clause
says: for `f ∈ F`, a chart `c`, a Euclidean ball `Metric.closedBall a ρ ⊆ c.target` and a function
`u` harmonic on `Metric.ball a ρ` whose glued extension of the boundary values `f ∘ c.symm` is
continuous on the closed ball, the replacement `replaceOnDisc c a ρ u f` again lies in `F`.

Only the upper bound is needed for the conclusion of Perron's theorem (and the family used to
construct Green's functions is bounded above but not below). -/
def IsPerronFamily (F : Set (X → ℝ)) (M : ℝ) : Prop :=
  F.Nonempty ∧
  (∀ f ∈ F, SubharmonicOnX f univ) ∧
  (∀ f ∈ F, ∀ x : X, f x ≤ M) ∧
  (∀ f ∈ F, ∀ g ∈ F, max f g ∈ F) ∧
  (∀ f ∈ F, ∀ (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ : ℝ), 0 < ρ →
    Metric.closedBall a ρ ⊆ c.target → ∀ u : ℂ → ℝ,
      (∀ z : ℂ, ‖z - a‖ < ρ → InnerProductSpace.HarmonicAt u z) →
      ContinuousOn (gluedBall u (fun w => f (c.symm w)) a ρ) (Metric.closedBall a ρ) →
      replaceOnDisc c a ρ u f ∈ F)

/-- The upper envelope `F̄ = sup F` of a family of real-valued functions. -/
def upperEnvelope {X : Type*} (F : Set (X → ℝ)) : X → ℝ :=
  fun x => sSup (F.image (fun f => f x))

end Perron

/-! ## Chart independence of subharmonicity -/

section ChartIndependence

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- **Transport of the subharmonic condition between two charts.**
If the pullback of `u` by `c` is continuous and satisfies the circle mean-value inequality on
`Metric.ball (c a) ρ₀` and the transitions between the two charts are complex analytic (as they
are for charts of a complex manifold), then `u` is subharmonic at `a` measured in the chart `d`. -/
theorem transport_subharmonic {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {u : X → ℝ} {c d : OpenPartialHomeomorph X ℂ} {a : X}
    (hca : a ∈ c.source) (hda : a ∈ d.source)
    (hanaT : ∀ z : ℂ, z ∈ d.target → d.symm z ∈ c.source →
      AnalyticAt ℂ (fun z : ℂ => c (d.symm z)) z)
    (hanaS : ∀ w : ℂ, w ∈ c.target → c.symm w ∈ d.source →
      AnalyticAt ℂ (fun w : ℂ => d (c.symm w)) w)
    {ρ₀ ρ : ℝ} (hρ : 0 < ρ) (hρle : ρ ≤ ρ₀)
    (hcont₀ : ContinuousOn (u ∘ c.symm) (Metric.ball (c a) ρ₀))
    (hm₀ : ∀ p ∈ Metric.ball (c a) ρ₀, ∀ r : ℝ, 0 < r →
      Metric.closedBall p r ⊆ Metric.ball (c a) ρ₀ →
      (u ∘ c.symm) p ≤ Real.circleAverage (u ∘ c.symm) p r) :
    SubharmonicAtChart u d a := by
  -- the two open sets
  have htarget : IsOpen (c.source ∩ c ⁻¹' Metric.ball (c a) ρ) :=
    c.continuousOn.isOpen_inter_preimage c.open_source Metric.isOpen_ball
  have hΩopen : IsOpen (Metric.ball (c a) ρ ∩ (c.symm.trans d).source) :=
    Metric.isOpen_ball.inter (c.symm.trans d).open_source
  have hΩ'open : IsOpen (d.target ∩ d.symm ⁻¹' (c.source ∩ c ⁻¹' Metric.ball (c a) ρ)) :=
    d.continuousOn_symm.isOpen_inter_preimage d.open_target htarget
  have hmemΩ : a ∈ c.source ∩ c ⁻¹' Metric.ball (c a) ρ :=
    ⟨hca, Metric.mem_ball_self hρ⟩
  have hmemΩ' : d a ∈ d.target ∩ d.symm ⁻¹' (c.source ∩ c ⁻¹' Metric.ball (c a) ρ) := by
    refine ⟨d.map_source hda, ?_⟩
    show d.symm (d a) ∈ c.source ∩ c ⁻¹' Metric.ball (c a) ρ
    rw [d.left_inv hda]
    exact hmemΩ
  -- the transition and its inverse
  have hTmap : Set.MapsTo (fun z : ℂ => c (d.symm z))
      (d.target ∩ d.symm ⁻¹' (c.source ∩ c ⁻¹' Metric.ball (c a) ρ))
      (Metric.ball (c a) ρ ∩ (c.symm.trans d).source) := by
    rintro z ⟨hzt, hzs⟩
    refine ⟨hzs.2, ?_⟩
    show c (d.symm z) ∈ (c.symm.trans d).source
    rw [mem_trans_source]
    exact ⟨c.map_source hzs.1, by rw [c.left_inv hzs.1]; exact d.map_target hzt⟩
  have hSmap : Set.MapsTo (fun w : ℂ => d (c.symm w))
      (Metric.ball (c a) ρ ∩ (c.symm.trans d).source)
      (d.target ∩ d.symm ⁻¹' (c.source ∩ c ⁻¹' Metric.ball (c a) ρ)) := by
    rintro w ⟨hwb, hws⟩
    obtain ⟨hwct, hwds⟩ := mem_trans_source.mp hws
    refine ⟨d.map_source hwds, ?_⟩
    show d.symm (d (c.symm w)) ∈ c.source ∩ c ⁻¹' Metric.ball (c a) ρ
    rw [d.left_inv hwds]
    exact ⟨c.map_target hwct, by
      show c (c.symm w) ∈ Metric.ball (c a) ρ
      rw [c.right_inv hwct]
      exact hwb⟩
  have hTS : ∀ z ∈ d.target ∩ d.symm ⁻¹' (c.source ∩ c ⁻¹' Metric.ball (c a) ρ),
      d (c.symm (c (d.symm z))) = z := by
    rintro z ⟨hzt, hzs⟩
    rw [c.left_inv hzs.1, d.right_inv hzt]
  have hST : ∀ w ∈ Metric.ball (c a) ρ ∩ (c.symm.trans d).source,
      c (d.symm (d (c.symm w))) = w := by
    rintro w ⟨hwb, hws⟩
    obtain ⟨hwct, hwds⟩ := mem_trans_source.mp hws
    rw [d.left_inv hwds, c.right_inv hwct]
  have hTcont : ContinuousOn (fun z : ℂ => c (d.symm z))
      (d.target ∩ d.symm ⁻¹' (c.source ∩ c ⁻¹' Metric.ball (c a) ρ)) :=
    continuousOn_of_forall_continuousAt fun z hz => (hanaT z hz.1 hz.2.1).continuousAt
  have hScont : ContinuousOn (fun w : ℂ => d (c.symm w))
      (Metric.ball (c a) ρ ∩ (c.symm.trans d).source) :=
    continuousOn_of_forall_continuousAt fun w hw =>
      (hanaS w (mem_trans_source.mp hw.2).1 (mem_trans_source.mp hw.2).2).continuousAt
  have hTana : AnalyticOnNhd ℂ (fun z : ℂ => c (d.symm z))
      (d.target ∩ d.symm ⁻¹' (c.source ∩ c ⁻¹' Metric.ball (c a) ρ)) :=
    fun z hz => hanaT z hz.1 hz.2.1
  have hSana : AnalyticOnNhd ℂ (fun w : ℂ => d (c.symm w))
      (Metric.ball (c a) ρ ∩ (c.symm.trans d).source) :=
    fun w hw => hanaS w (mem_trans_source.mp hw.2).1 (mem_trans_source.mp hw.2).2
  -- the mean-value data on `Ω`
  have hball_le : Metric.ball (c a) ρ ⊆ Metric.ball (c a) ρ₀ := Metric.ball_subset_ball hρle
  have hcont : ContinuousOn (u ∘ c.symm) (Metric.ball (c a) ρ ∩ (c.symm.trans d).source) :=
    hcont₀.mono (fun z hz => hball_le hz.1)
  have hm : ∀ p ∈ Metric.ball (c a) ρ ∩ (c.symm.trans d).source, ∀ r : ℝ, 0 < r →
      Metric.closedBall p r ⊆ Metric.ball (c a) ρ ∩ (c.symm.trans d).source →
      (u ∘ c.symm) p ≤ Real.circleAverage (u ∘ c.symm) p r :=
    fun p hp r hr hpr => hm₀ p (hball_le hp.1) r hr (fun z hz => hball_le (hpr hz).1)
  -- the transported comparison criterion
  have hcrit : ∀ (q : ℂ) (s : ℝ), 0 < s →
      Metric.closedBall q s ⊆ d.target ∩ d.symm ⁻¹' (c.source ∩ c ⁻¹' Metric.ball (c a) ρ) →
      ∀ f : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd f (Metric.ball q s) →
      ContinuousOn f (Metric.closedBall q s) →
      (∀ z ∈ Metric.sphere q s, (u ∘ d.symm) z ≤ f z) →
      ∀ z ∈ Metric.ball q s, (u ∘ d.symm) z ≤ f z := by
    intro q s hs hqs f hf hfc hle
    have hres := Commons.Analysis.Complex.Harmonic.subharmonic_le_harmonic_comp_biholo
      (Ω := Metric.ball (c a) ρ ∩ (c.symm.trans d).source)
      (Ω' := d.target ∩ d.symm ⁻¹' (c.source ∩ c ⁻¹' Metric.ball (c a) ρ))
      hΩopen hcont hm hTmap hSmap hTS hST hTcont hScont hTana hSana hs hqs hf hfc
      (fun z hz => by
        rw [pullback_comp_transition (u := u) (hqs (Metric.sphere_subset_closedBall hz)).2.1]
        exact hle z hz)
    intro z hz
    rw [← pullback_comp_transition (u := u) (hqs (Metric.ball_subset_closedBall hz)).2.1]
    exact hres z hz
  obtain ⟨ρ', hρ', hball'⟩ := Metric.isOpen_iff.mp hΩ'open (d a) hmemΩ'
  have hsub : Metric.ball (d a) ρ' ⊆ d.target := fun z hz => (hball' hz).1
  have hcont' : ContinuousOn (u ∘ d.symm) (Metric.ball (d a) ρ') := by
    have h1 : ContinuousOn (u ∘ d.symm) (d.target ∩ d.symm ⁻¹' (c.source ∩ c ⁻¹' Metric.ball (c a) ρ)) :=
      (ContinuousOn.comp hcont hTcont hTmap).congr
        (fun z hz => (pullback_comp_transition (u := u) hz.2.1).symm)
    exact h1.mono hball'
  have hcrit' : ∀ (p : ℂ) (r : ℝ), 0 < r → Metric.closedBall p r ⊆ Metric.ball (d a) ρ' →
      ∀ h : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd h (Metric.ball p r) →
      ContinuousOn h (Metric.closedBall p r) →
      (∀ z ∈ Metric.sphere p r, (u ∘ d.symm) z ≤ h z) → ∀ z ∈ Metric.ball p r,
      (u ∘ d.symm) z ≤ h z :=
    fun p r hr hpr h hh hhc hle => hcrit p r hr (fun z hz => hball' (hpr hz)) h hh hhc hle
  refine ⟨hda, ρ', hρ', hsub, hcont', ?_⟩
  intro p hp r hr hpr
  exact Commons.Analysis.Complex.Harmonic.circleAverage_ge_of_le_harmonic
    Metric.isOpen_ball hcont' hcrit' hr hpr

/-- **Chart independence of subharmonicity** (Hubbard Definition 1.2.1): the circle mean-value
inequality for the chart pullbacks is the same condition in every preferred chart. -/
theorem SubharmonicAtChart_iff_chartAt {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {u : X → ℝ} {a b : X}
    (hab : a ∈ (chartAt ℂ b).source) :
    SubharmonicAtChart u (chartAt ℂ a) a ↔ SubharmonicAtChart u (chartAt ℂ b) a := by
  have hana : ∀ (x y : X) (z : ℂ),
      z ∈ (chartAt ℂ y).target → (chartAt ℂ y).symm z ∈ (chartAt ℂ x).source →
      AnalyticAt ℂ (fun z : ℂ => (chartAt ℂ x) ((chartAt ℂ y).symm z)) z := by
    intro x y z hzt hzs
    have hsource : z ∈ ((chartAt ℂ y).symm.trans (chartAt ℂ x)).source := by
      rw [mem_trans_source]
      exact ⟨hzt, hzs⟩
    have hana := Commons.Geometry.Manifold.chart_transition_analyticOnNhd (X := X) y x z hsource
    refine hana.congr ?_
    filter_upwards [((chartAt ℂ y).symm.trans (chartAt ℂ x)).open_source.eventually_mem hsource]
      with w hw
    rfl
  constructor
  · intro h
    rw [SubharmonicAtChart] at h
    obtain ⟨-, ρ₀, hρ₀, -, hc₀, hm₀⟩ := h
    exact transport_subharmonic (mem_chart_source ℂ a) hab (hana a b) (hana b a) hρ₀ le_rfl hc₀ hm₀
  · intro h
    rw [SubharmonicAtChart] at h
    obtain ⟨-, ρ₀, hρ₀, -, hc₀, hm₀⟩ := h
    exact transport_subharmonic hab (mem_chart_source ℂ a) (hana b a) (hana a b) hρ₀ le_rfl hc₀ hm₀

/-- `SubharmonicOnXAt` is chart-independent: subharmonicity at `a` may be measured in any
preferred chart whose source contains `a`. -/
theorem SubharmonicOnXAt_iff_chartAt {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {u : X → ℝ} {a b : X}
    (hab : a ∈ (chartAt ℂ b).source) :
    SubharmonicOnXAt u a ↔ SubharmonicAtChart u (chartAt ℂ b) a :=
  SubharmonicAtChart_iff_chartAt hab

/-- A function subharmonic on `U` satisfies the circle mean-value inequality in *any* preferred
chart, on a ball around the chart image of a point of `U`. -/
theorem SubharmonicOnX.subharmonicAtChart {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {u : X → ℝ} {U : Set X} (h : SubharmonicOnX u U)
    {a b : X} (ha : a ∈ U) (hab : a ∈ (chartAt ℂ b).source) :
    SubharmonicAtChart u (chartAt ℂ b) a :=
  (SubharmonicOnXAt_iff_chartAt hab).mp (h.2 a ha)

end ChartIndependence

end Submission
