import Submission.Lib.Unif2.UnifDeps
import Submission.Lib.Unif2.RiemannSurface
import Submission.Lib.Unif2.Commons.Geometry.Manifold.analyticAt_pullback_iff_chart

/-!
# Holomorphic functions on a Riemann surface

A function `f : X → ℂ` is holomorphic at `x` if its pullback by the preferred chart at `x` is
complex analytic there; it is holomorphic on a set if it is holomorphic at every point of the set.
We record the elementary calculus of this notion and the fact that the real part of a holomorphic
function is harmonic (the starting point of the construction of the uniformising map).
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Submission

section Holomorphic

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- `f` is holomorphic at `x`: its pullback by the preferred chart at `x` is complex analytic at
the image of `x`. -/
def HolomorphicOnXAt (f : X → ℂ) (x : X) : Prop :=
  AnalyticAt ℂ (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)

/-- `f` is holomorphic on the set `U`. -/
def HolomorphicOnX (f : X → ℂ) (U : Set X) : Prop := ∀ x ∈ U, HolomorphicOnXAt f x

/-- Chart independence of holomorphy: measuring in the preferred chart at `x` or at `y` gives the
same condition, as the chart transition is complex analytic. -/
theorem HolomorphicOnXAt_iff_chart {f : X → ℂ} {x y : X} (hxy : x ∈ (chartAt ℂ y).source) :
    HolomorphicOnXAt f x ↔ AnalyticAt ℂ (f ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x) :=
  Commons.Geometry.Manifold.analyticAt_pullback_iff_chart hxy

/-- A holomorphic function is continuous. -/
theorem HolomorphicOnXAt.continuousAt {f : X → ℂ} {x : X} (h : HolomorphicOnXAt f x) :
    ContinuousAt f x := by
  have hc : ContinuousAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) :=
    AnalyticAt.continuousAt h
  have hcx : ContinuousAt (chartAt ℂ x) x := (chartAt ℂ x).continuousAt (mem_chart_source ℂ x)
  have hcomp : ContinuousAt (fun w : X => (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) w)) x :=
    hc.comp hcx
  refine hcomp.congr ?_
  filter_upwards [(chartAt ℂ x).open_source.eventually_mem (mem_chart_source ℂ x)] with w hw
  simp only [Function.comp_apply]
  rw [(chartAt ℂ x).left_inv hw]

/-- A function holomorphic on all of `X` is continuous. -/
theorem HolomorphicOnX.continuous {f : X → ℂ} (h : HolomorphicOnX f univ) : Continuous f :=
  continuous_iff_continuousAt.mpr fun x => (h x (mem_univ x)).continuousAt

theorem HolomorphicOnXAt.add {f g : X → ℂ} {x : X} (hf : HolomorphicOnXAt f x)
    (hg : HolomorphicOnXAt g x) : HolomorphicOnXAt (f + g) x := by
  rw [HolomorphicOnXAt] at hf hg ⊢
  have : (f + g) ∘ (chartAt ℂ x).symm
      = (f ∘ (chartAt ℂ x).symm) + (g ∘ (chartAt ℂ x).symm) := rfl
  rw [this]
  exact hf.add hg

theorem HolomorphicOnXAt.sub {f g : X → ℂ} {x : X} (hf : HolomorphicOnXAt f x)
    (hg : HolomorphicOnXAt g x) : HolomorphicOnXAt (f - g) x := by
  rw [HolomorphicOnXAt] at hf hg ⊢
  have : (f - g) ∘ (chartAt ℂ x).symm
      = (f ∘ (chartAt ℂ x).symm) - (g ∘ (chartAt ℂ x).symm) := rfl
  rw [this]
  exact hf.sub hg

theorem HolomorphicOnXAt.mul {f g : X → ℂ} {x : X} (hf : HolomorphicOnXAt f x)
    (hg : HolomorphicOnXAt g x) : HolomorphicOnXAt (f * g) x := by
  rw [HolomorphicOnXAt] at hf hg ⊢
  have : (f * g) ∘ (chartAt ℂ x).symm
      = (f ∘ (chartAt ℂ x).symm) * (g ∘ (chartAt ℂ x).symm) := rfl
  rw [this]
  exact hf.mul hg

theorem HolomorphicOnXAt.neg {f : X → ℂ} {x : X} (hf : HolomorphicOnXAt f x) :
    HolomorphicOnXAt (-f) x := by
  rw [HolomorphicOnXAt] at hf ⊢
  have : (-f) ∘ (chartAt ℂ x).symm = -(f ∘ (chartAt ℂ x).symm) := rfl
  rw [this]
  exact hf.neg

theorem HolomorphicOnXAt.const_mul {f : X → ℂ} {x : X} (c : ℂ) (hf : HolomorphicOnXAt f x) :
    HolomorphicOnXAt (fun y => c * f y) x := by
  rw [HolomorphicOnXAt] at hf ⊢
  have h1 : (fun y : X => c * f y) ∘ (chartAt ℂ x).symm
      = (fun _ : ℂ => c) * (f ∘ (chartAt ℂ x).symm) := rfl
  rw [h1]
  exact analyticAt_const.mul hf

theorem holomorphicOnXAt_const (c : ℂ) (x : X) : HolomorphicOnXAt (fun _ : X => c) x := by
  rw [HolomorphicOnXAt]
  have : (fun _ : X => c) ∘ (chartAt ℂ x).symm = fun _ : ℂ => c := rfl
  rw [this]
  exact analyticAt_const

/-- **The real part of a holomorphic function is harmonic.** -/
theorem HolomorphicOnXAt.re_harmonic {f : X → ℂ} {x : X} (h : HolomorphicOnXAt f x) :
    HarmonicOnXAt (fun y => (f y).re) x := by
  rw [HolomorphicOnXAt] at h
  rw [HarmonicOnXAt]
  have heq : (fun y : X => (f y).re) ∘ (chartAt ℂ x).symm
      = fun w : ℂ => ((f ∘ (chartAt ℂ x).symm) w).re := rfl
  rw [heq]
  exact h.harmonicAt_re

theorem HolomorphicOnX.re_harmonic {f : X → ℂ} {U : Set X} (h : HolomorphicOnX f U) :
    HarmonicOnX (fun y => (f y).re) U := fun x hx => (h x hx).re_harmonic

theorem HolomorphicOnX.mono {f : X → ℂ} {U V : Set X} (h : HolomorphicOnX f U) (hVU : V ⊆ U) :
    HolomorphicOnX f V := fun x hx => h x (hVU hx)

theorem HolomorphicOnX.add {f g : X → ℂ} {U : Set X} (hf : HolomorphicOnX f U)
    (hg : HolomorphicOnX g U) : HolomorphicOnX (f + g) U :=
  fun x hx => (hf x hx).add (hg x hx)

theorem HolomorphicOnX.sub {f g : X → ℂ} {U : Set X} (hf : HolomorphicOnX f U)
    (hg : HolomorphicOnX g U) : HolomorphicOnX (f - g) U :=
  fun x hx => (hf x hx).sub (hg x hx)

theorem HolomorphicOnX.mul {f g : X → ℂ} {U : Set X} (hf : HolomorphicOnX f U)
    (hg : HolomorphicOnX g U) : HolomorphicOnX (f * g) U :=
  fun x hx => (hf x hx).mul (hg x hx)

theorem holomorphicOnX_const (c : ℂ) {U : Set X} : HolomorphicOnX (fun _ : X => c) U :=
  fun x _ => holomorphicOnXAt_const c x

/-- **Locally every harmonic function is the real part of a holomorphic function.** -/
theorem exists_holomorphicOnXAt_re_of_harmonic {u : X → ℝ} {x : X} (h : HarmonicOnXAt u x) :
    ∃ F : X → ℂ, HolomorphicOnXAt F x ∧ (fun y => (F y).re) =ᶠ[𝓝 x] u := by
  have hxsrc : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  obtain ⟨R₁, hR₁, hR₁sub⟩ :=
    Metric.mem_nhds_iff.mp ((InnerProductSpace.isOpen_setOfPred_harmonicAt
      (u ∘ (chartAt ℂ x).symm)).mem_nhds h)
  obtain ⟨R₂, hR₂, hR₂sub⟩ := Metric.mem_nhds_iff.mp
    ((chartAt ℂ x).open_target.mem_nhds ((chartAt ℂ x).map_source hxsrc))
  have hR : 0 < min R₁ R₂ := lt_min hR₁ hR₂
  have hsub : Metric.ball ((chartAt ℂ x) x) (min R₁ R₂) ⊆ (chartAt ℂ x).target :=
    (Metric.ball_subset_ball (min_le_right R₁ R₂)).trans hR₂sub
  have hharm : InnerProductSpace.HarmonicOnNhd (u ∘ (chartAt ℂ x).symm)
      (Metric.ball ((chartAt ℂ x) x) (min R₁ R₂)) :=
    fun w hw => hR₁sub (Metric.ball_subset_ball (min_le_left R₁ R₂) hw)
  obtain ⟨F₀, hF₀ana, hF₀re⟩ :=
    InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq hharm
  have hmem : (chartAt ℂ x) x ∈ Metric.ball ((chartAt ℂ x) x) (min R₁ R₂) := Metric.mem_ball_self hR
  refine ⟨fun y => F₀ ((chartAt ℂ x) y), ?_, ?_⟩
  · rw [HolomorphicOnXAt]
    have heq : (fun y : X => F₀ ((chartAt ℂ x) y)) ∘ (chartAt ℂ x).symm
        =ᶠ[𝓝 ((chartAt ℂ x) x)] F₀ := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hmem] with w hw
      simp only [Function.comp_apply]
      rw [(chartAt ℂ x).right_inv (hsub hw)]
    exact AnalyticAt.congr (hF₀ana ((chartAt ℂ x) x) hmem) heq.symm
  · filter_upwards [(chartBall_isOpen (chartAt ℂ x) ((chartAt ℂ x) x) (min R₁ R₂)).mem_nhds
      ⟨hxsrc, hmem⟩] with y hy
    have h1 : (F₀ ((chartAt ℂ x) y)).re = u ((chartAt ℂ x).symm ((chartAt ℂ x) y)) := hF₀re hy.2
    rw [h1, (chartAt ℂ x).left_inv hy.1]

end Holomorphic

end Submission
