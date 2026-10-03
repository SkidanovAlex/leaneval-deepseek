import Submission.Lib.Unif2.UnifDeps
import Submission.Lib.Unif2.Sweep
import Submission.Lib.Unif2.ChartLogClamp
import Submission.Lib.Unif2.GreenConditional
import Submission.Lib.Unif2.Holomorphic

/-!
# Members of the sweep family from holomorphic functions

The sweep family `sweepFamily ψ U` of the clamped logarithmic potential `ψ` on `U = univ ∖ {z₀}`
(see `Submission/GreenConditional.lean`) is nonempty as soon as `X` carries a holomorphic function
with a single zero at `z₀`: the function `−log ‖f‖` is harmonic on `X ∖ {z₀}` and, after the
addition of a sufficiently large constant, dominates the barrier `ψ`.

This module records the formal statement.  The single analytical input is the **domination**

`∀ x ∈ U, ψ x ≤ −log ‖f x‖ + M`

which holds for a suitable `M` whenever `f` is holomorphic on `X`, bounded by `1` and vanishes only
at `z₀` (the quotient `‖f x‖ / ‖c x − a‖` is bounded near the pole by the Cauchy estimates); it is
taken as a hypothesis here so that the *structural* content — harmonicity of `−log ‖f‖`, membership
in the sweep family, strict positivity of the sweep and the resulting logarithmic pole — is
available independently of it.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Submission

section Superharmonic

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- `x ↦ log ‖f x‖` is harmonic at every point at which `f` is holomorphic and non-zero. -/
theorem harmonicOnXAt_log_norm {f : X → ℂ} {x : X} (hf : HolomorphicOnXAt f x)
    (hne : f x ≠ 0) : HarmonicOnXAt (fun y => Real.log ‖f y‖) x := by
  rw [HarmonicOnXAt]
  have hana : AnalyticAt ℂ (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) := hf
  have hval : (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) = f x := by
    simp only [Function.comp_apply]
    rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
  have hne' : (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) ≠ 0 := by
    rw [hval]; exact hne
  exact hana.harmonicAt_log_norm hne'

/-- `x ↦ −log ‖f x‖` is harmonic at every point at which `f` is holomorphic and non-zero. -/
theorem harmonicOnXAt_neg_log_norm {f : X → ℂ} {x : X} (hf : HolomorphicOnXAt f x)
    (hne : f x ≠ 0) : HarmonicOnXAt (fun y => -Real.log ‖f y‖) x :=
  (harmonicOnXAt_log_norm hf hne).neg

/-- **`−log ‖f‖ + M` is superharmonic on an open set on which `f` is holomorphic and
non-zero.** -/
theorem superharmonicOnX_neg_log_norm_add {U : Set X} {f : X → ℂ}
    (hf : HolomorphicOnX f U) (hne : ∀ x ∈ U, f x ≠ 0) (M : ℝ) :
    SuperharmonicOnX (fun y => -Real.log ‖f y‖ + M) U := by
  refine ⟨?_, fun x hx => ?_⟩
  · refine continuousOn_of_forall_continuousAt (fun x hx => ?_)
    have h1 : ContinuousAt (fun y : X => ‖f y‖) x := (hf x hx).continuousAt.norm
    have h2 : ContinuousAt (fun y : X => Real.log ‖f y‖) x :=
      h1.log (norm_ne_zero_iff.mpr (hne x hx))
    exact h2.neg.add (continuousAt_const : ContinuousAt (fun _ : X => M) x)
  · have h3 : HarmonicOnXAt (fun y : X => -Real.log ‖f y‖) x :=
      harmonicOnXAt_neg_log_norm (hf x hx) (hne x hx)
    have h4 : HarmonicOnXAt (fun y : X => -Real.log ‖f y‖ + M) x :=
      h3.add (harmonicOnXAt_const M)
    exact h4.superharmonic

end Superharmonic

section Member

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **A member of the sweep family from a dominated holomorphic function**: if `−log ‖f‖ + M` is
superharmonic on the punctured surface and dominates the clamped logarithmic potential, then it is
a member of the sweep family. -/
theorem mem_sweepFamily_neg_log_norm {z₀ : X} {ρ M : ℝ} {f : X → ℂ}
    (hv : SuperharmonicOnX (fun y => -Real.log ‖f y‖ + M) (univ \ {z₀}))
    (hdom : ∀ x ∈ (univ \ {z₀} : Set X), greenBarrier z₀ ρ x ≤ -Real.log ‖f x‖ + M) :
    (fun y => -Real.log ‖f y‖ + M) ∈ sweepFamily (greenBarrier z₀ ρ) (univ \ {z₀}) :=
  ⟨hv, hdom⟩

/-- **The sweep family of the clamped logarithmic potential is nonempty** as soon as the surface
carries a holomorphic function with a single zero together with a constant making the domination
hold. -/
theorem sweepFamily_nonempty_of_log_norm {z₀ : X} {ρ M : ℝ} {f : X → ℂ}
    (hf : HolomorphicOnX f univ) (hne : ∀ x ∈ (univ \ {z₀} : Set X), f x ≠ 0)
    (hdom : ∀ x ∈ (univ \ {z₀} : Set X), greenBarrier z₀ ρ x ≤ -Real.log ‖f x‖ + M) :
    (sweepFamily (greenBarrier z₀ ρ) (univ \ {z₀})).Nonempty :=
  ⟨fun y => -Real.log ‖f y‖ + M,
    mem_sweepFamily_neg_log_norm
      (superharmonicOnX_neg_log_norm_add (U := univ \ {z₀})
        (fun x _ => hf x (mem_univ x)) hne M) hdom⟩

/-- **The sweep inherits the bound**: it is dominated by every member of the family. -/
theorem sweep_le_neg_log_norm_add {z₀ : X} {ρ M : ℝ} {f : X → ℂ}
    (hv : (fun y => -Real.log ‖f y‖ + M) ∈ sweepFamily (greenBarrier z₀ ρ) (univ \ {z₀})) :
    ∀ x ∈ (univ \ {z₀} : Set X),
      sweep (greenBarrier z₀ ρ) (univ \ {z₀}) x ≤ -Real.log ‖f x‖ + M :=
  fun x hx => sweep_le_of_mem hv hx

/-- **The sweep family of the clamped logarithmic potential is nonempty for a holomorphic function
with a single zero.**  If `f : X → ℂ` is holomorphic on `X`, bounded by `1` and vanishes exactly at
`z₀`, then `−log ‖f‖ + 1` is a member of the sweep family of a suitable clamped logarithmic
potential; the domination is the Schwarz bound `‖f x‖ ≤ ‖c x − c z₀‖ / r` on the chart ball of
radius `r / 2`, where `r` is a radius of analyticity of the chart pullback of `f`. -/
theorem exists_mem_sweepFamily_neg_log_norm {z₀ : X} {f : X → ℂ}
    (hf : HolomorphicOnX f univ) (hb : ∀ x : X, ‖f x‖ ≤ 1) (hz : f ⁻¹' {0} = {z₀}) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.closedBall ((chartAt ℂ z₀) z₀) ρ ⊆ (chartAt ℂ z₀).target ∧
      (fun x => -Real.log ‖f x‖ + 1) ∈ sweepFamily (greenBarrier z₀ ρ) (univ \ {z₀}) := by
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ z₀ with hc
  set a : ℂ := c z₀ with ha
  have hz₀src : z₀ ∈ c.source := mem_chart_source ℂ z₀
  have haz : a ∈ c.target := ha ▸ c.map_source hz₀src
  have hf0 : f z₀ = 0 := by
    have h : z₀ ∈ f ⁻¹' {0} := by rw [hz]; exact mem_singleton z₀
    simpa using h
  -- a radius of analyticity of the chart pullback
  obtain ⟨r, hr, hran⟩ := (hf z₀ (mem_univ z₀)).exists_ball_analyticOnNhd
  -- a radius inside the chart target
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (c.open_target.mem_nhds haz)
  set ρ : ℝ := min (r / 2) ε / 2 with hρdef
  have hρ : 0 < ρ := by
    rw [hρdef]
    exact half_pos (lt_min (half_pos hr) hε)
  have hρr : ρ ≤ r / 2 := by
    rw [hρdef]
    exact le_trans (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)) (by linarith)
  have hρε : ρ ≤ ε / 2 := by
    rw [hρdef]
    exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have htgt : Metric.closedBall a ρ ⊆ c.target :=
    (Metric.closedBall_subset_ball (by linarith [hρε, hε])).trans hεsub
  refine ⟨ρ, hρ, htgt, ?_⟩
  -- the Schwarz bound
  have hga : (f ∘ c.symm) a = 0 := by
    rw [Function.comp_apply, ha, c.left_inv hz₀src]
    exact hf0
  have hdiff : DifferentiableOn ℂ (f ∘ c.symm) (Metric.ball a r) := hran.differentiableOn
  have hmap : MapsTo (f ∘ c.symm) (Metric.ball a r) (Metric.closedBall ((f ∘ c.symm) a) 1) := by
    intro z _
    rw [Metric.mem_closedBall, dist_eq_norm, hga, sub_zero]
    exact hb (c.symm z)
  have hdom : ∀ x ∈ (univ \ {z₀} : Set X), greenBarrier z₀ ρ x ≤ -Real.log ‖f x‖ + 1 := by
    intro x hx
    by_cases hxB : x ∈ chartBall c a ρ
    · have hxsrc : x ∈ c.source := hxB.1
      have hxne : c x ≠ a := by
        intro h
        exact hx.2 (c.injOn hxsrc hz₀src (by rw [h, ha]))
      have hnorm : 0 < ‖c x - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxne)
      have hlt : ‖c x - a‖ < ρ := by
        have h := Metric.mem_ball.mp hxB.2
        rwa [dist_eq_norm] at h
      have hzmem : c x ∈ Metric.ball a r := by
        rw [Metric.mem_ball, dist_eq_norm]
        linarith [hlt, hρr]
      have hsch := Complex.dist_le_div_mul_dist_of_mapsTo_ball hdiff hmap hzmem
      have hfx : ‖f x‖ ≤ ‖c x - a‖ / r := by
        have h1 : dist ((f ∘ c.symm) (c x)) ((f ∘ c.symm) a) = ‖f x‖ := by
          rw [dist_eq_norm, hga, sub_zero, Function.comp_apply, c.left_inv hxsrc]
        rw [h1, dist_eq_norm] at hsch
        have h2 : (1 : ℝ) / r * ‖c x - a‖ = ‖c x - a‖ / r := by ring
        rwa [h2] at hsch
      have hprod : ρ / ‖c x - a‖ * ‖f x‖ ≤ 1 := by
        have hnn : 0 ≤ ρ / ‖c x - a‖ := by positivity
        calc ρ / ‖c x - a‖ * ‖f x‖ ≤ ρ / ‖c x - a‖ * (‖c x - a‖ / r) :=
              mul_le_mul_of_nonneg_left hfx hnn
          _ = ρ / r := by field_simp
          _ ≤ 1 := by
              rw [div_le_one hr]
              linarith [hρr, hr]
      have hfxne : f x ≠ 0 := fun h0 => hx.2 (by
        have h : x ∈ f ⁻¹' {0} := h0
        rw [hz] at h
        simpa using h)
      have hlog : Real.log (ρ / ‖c x - a‖) + Real.log ‖f x‖ ≤ 1 := by
        rw [← Real.log_mul (div_ne_zero hρ.ne' (ne_of_gt hnorm))
          (norm_ne_zero_iff.mpr hfxne)]
        have h := Real.log_le_log (by positivity) hprod
        rw [Real.log_one] at h
        linarith
      rw [greenBarrier, chartLogClamp_of_mem hxB]
      linarith
    · rw [greenBarrier, chartLogClamp_of_not_mem hxB]
      have h1 : 0 ≤ -Real.log ‖f x‖ :=
        neg_nonneg.mpr (Real.log_nonpos (norm_nonneg _) (hb x))
      linarith
  refine mem_sweepFamily_neg_log_norm (M := 1) ?_ hdom
  refine superharmonicOnX_neg_log_norm_add (U := univ \ {z₀}) (fun x _ => hf x (mem_univ x)) ?_ 1
  intro x hx
  intro h0
  exact hx.2 (by
    have h : x ∈ f ⁻¹' {0} := h0
    rw [hz] at h
    simpa using h)

end Member

section Positivity

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- The complement of `{z₀}` is open. -/
theorem isOpen_univ_diff_singleton (z₀ : X) : IsOpen (univ \ {z₀} : Set X) :=
  isOpen_univ.sdiff isClosed_singleton

/-- **The sweep of the clamped logarithmic potential is strictly positive.** -/
theorem sweep_greenBarrier_pos {z₀ : X} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : Metric.closedBall ((chartAt ℂ z₀) z₀) ρ ⊆ (chartAt ℂ z₀).target)
    (hne : (sweepFamily (greenBarrier z₀ ρ) (univ \ {z₀})).Nonempty) :
    ∀ x ∈ (univ \ {z₀} : Set X), 0 < sweep (greenBarrier z₀ ρ) (univ \ {z₀}) x := by
  refine sweep_pos (isOpen_univ_diff_singleton z₀) (subharmonicOnX_greenBarrier hρ hsub) hne
    (fun x _ => chartLogClamp_nonneg x) ⟨z₀, by simp⟩ ?_
  intro x hx
  rw [show x = z₀ from by simpa using hx]
  refine ⟨chartBall (chartAt ℂ z₀) ((chartAt ℂ z₀) z₀) (ρ / 2),
    chartBall_greenBarrier_mem_nhds (half_pos hρ), ?_⟩
  intro y hy hyU
  have hysrc : y ∈ (chartAt ℂ z₀).source := hy.1
  have hyne : (chartAt ℂ z₀) y ≠ (chartAt ℂ z₀) z₀ := by
    intro h
    exact hyU.2 ((chartAt ℂ z₀).injOn hysrc (mem_chart_source ℂ z₀) h)
  have h1 : Real.log (ρ / (ρ / 2)) ≤ greenBarrier z₀ ρ y :=
    greenBarrier_lower_bound hρ (half_pos hρ) (half_lt_self hρ) hy hyne
  have h2 : 0 < Real.log (ρ / (ρ / 2)) := by
    rw [show ρ / (ρ / 2) = 2 from by field_simp]
    exact Real.log_pos one_lt_two
  linarith

/-- **The Green function exists as soon as `X` carries a holomorphic function with a single
zero.**  With `f` holomorphic on `X`, `‖f‖ ≤ 1`, `f ⁻¹' {0} = {z₀}` and a suitable clamped
logarithmic potential, the sweep `E` of that potential is harmonic on `X ∖ {z₀}`, strictly
positive there, and dominated by `−log ‖f‖ + 1`. -/
theorem exists_sweep_greenBarrier_of_holomorphic_single_zero {z₀ : X} {f : X → ℂ}
    (hf : HolomorphicOnX f univ) (hb : ∀ x : X, ‖f x‖ ≤ 1) (hz : f ⁻¹' {0} = {z₀}) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.closedBall ((chartAt ℂ z₀) z₀) ρ ⊆ (chartAt ℂ z₀).target ∧
      HarmonicOnX (sweep (greenBarrier z₀ ρ) (univ \ {z₀})) (univ \ {z₀}) ∧
      (∀ x ∈ (univ \ {z₀} : Set X), 0 < sweep (greenBarrier z₀ ρ) (univ \ {z₀}) x) ∧
      (∀ x ∈ (univ \ {z₀} : Set X),
        sweep (greenBarrier z₀ ρ) (univ \ {z₀}) x ≤ -Real.log ‖f x‖ + 1) := by
  haveI : T1Space X := inferInstance
  obtain ⟨ρ, hρ, htgt, hmem⟩ := exists_mem_sweepFamily_neg_log_norm hf hb hz
  have hne : (sweepFamily (greenBarrier z₀ ρ) (univ \ {z₀})).Nonempty := ⟨_, hmem⟩
  exact ⟨ρ, hρ, htgt, sweep_harmonic (isOpen_univ_diff_singleton z₀)
      (subharmonicOnX_greenBarrier hρ htgt) hne,
    sweep_greenBarrier_pos hρ htgt hne, fun x hx => sweep_le_of_mem hmem hx⟩

end Positivity

end Submission
