import Mathlib
import Submission.Lib.Unif2.SweepMember
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.ExtremalImports
import Submission.Lib.Unif2.Commons.Analysis.Complex.exists_ball_factorization_of_analyticAt_zero
import Submission.Lib.Unif2.Commons.Analysis.Complex.ChartedSpace.isClopen_setOf_eventuallyConst

/-!
# Auxiliary lemmas for the domination of the extremal family by the sweep of the Green barrier

This module collects the analytic inputs of
`Work.SimplyConnected.ABS.sweep_greenBarrier_dominates`:

* the identity theorem on a connected Riemann surface;
* the isolation of the zero of a holomorphic function at a point (in the preferred chart);
* the Schwarz bound `‖g z‖ ≤ ‖c z - c x₀‖ / ρ` for a member of the extremal family on the chart
  disc of radius `ρ`;
* the clamped potential `z ↦ -log (max ‖g z‖ (exp (-K)))`, its continuity and its
  superharmonicity on the whole surface (the clamp is what repairs the value at the zeros of `g`,
  where `Real.log 0 = 0` would otherwise break upper semicontinuity).
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X] [T2Space X]

/-- `SuperharmonicOnXAt` is a local condition: two functions that agree on a neighbourhood of `x`
are superharmonic there simultaneously.  (The dual of `Submission.SubharmonicOnXAt.congr`.) -/
theorem Submission.SuperharmonicOnXAt.congr [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {u v : X → ℝ} {x : X}
    (h : Submission.SuperharmonicOnXAt u x) (huv : u =ᶠ[nhds x] v) :
    Submission.SuperharmonicOnXAt v x := by
  have h1 : Submission.SubharmonicOnXAt (fun y : X => -u y) x := h.neg
  have h2 : (fun y : X => -u y) =ᶠ[nhds x] (fun y : X => -v y) := huv.neg
  have h3 : Submission.SubharmonicOnXAt (fun y : X => -v y) x :=
    Submission.SubharmonicOnXAt.congr h1 h2
  have h4 : Submission.SuperharmonicOnXAt (fun y : X => -(-v y)) x := h3.neg
  simpa using h4

/-- **Identity theorem** on a connected Riemann surface: a function holomorphic on all of `X` which
vanishes on a neighbourhood of a point vanishes everywhere. -/
theorem holomorphicOnX_eq_zero_of_eventuallyEq_zero [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {f : X → ℂ} (hf : Submission.HolomorphicOnX f Set.univ) {z₀ : X}
    (h : f =ᶠ[nhds z₀] (fun _ : X => (0 : ℂ))) : ∀ x : X, f x = 0 := by
  have hana : ∀ x : X, AnalyticAt ℂ (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) :=
    fun x => hf x (mem_univ x)
  have hS : IsClopen {x : X | ∀ᶠ y in nhds x, f y = f x} :=
    Commons.Analysis.Complex.ChartedSpace.isClopen_setOf_eventuallyConst hana
  have hz₀ : f z₀ = 0 := h.self_of_nhds
  have hz₀S : z₀ ∈ {x : X | ∀ᶠ y in nhds x, f y = f x} := by
    show ∀ᶠ y in nhds z₀, f y = f z₀
    filter_upwards [h] with y hy
    rw [hy, hz₀]
  have huniv : (Set.univ : Set X) ⊆ {x : X | ∀ᶠ y in nhds x, f y = f x} :=
    isPreconnected_univ.subset_isClopen hS ⟨z₀, mem_univ z₀, hz₀S⟩
  have hzero_open : IsOpen {x : X | f x = 0} := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hxn : ∀ᶠ y in nhds x, f y = f x := huniv (mem_univ x)
    have hx' : f x = 0 := hx
    rw [hx'] at hxn
    exact hxn
  have hzero_closed : IsClosed {x : X | f x = 0} := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro x hx
    have hxn : ∀ᶠ y in nhds x, f y = f x := huniv (mem_univ x)
    have hx' : f x ≠ 0 := by simpa using hx
    refine Filter.mem_of_superset hxn ?_
    intro y hy
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
    rw [hy]
    exact hx'
  have hall : (Set.univ : Set X) ⊆ {x : X | f x = 0} :=
    isPreconnected_univ.subset_isClopen ⟨hzero_closed, hzero_open⟩ ⟨z₀, mem_univ z₀, hz₀⟩
  intro x
  exact hall (mem_univ x)

/-- **Isolation of the zero at `x₀`**, in the preferred chart at `x₀`: for a holomorphic function
`g` vanishing at `x₀` and not identically zero, there is a chart radius `ε > 0` such that `x₀` is
the only zero of `g` in the chart disc of radius `ε`. -/
theorem exists_isolated_zero_chart [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {g : X → ℂ} (hg : Submission.HolomorphicOnX g Set.univ) {x₀ : X} (hg0 : g x₀ = 0)
    (hne : ∃ x : X, g x ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z : X, z ∈ (chartAt ℂ x₀).source →
      ‖(chartAt ℂ x₀) z - (chartAt ℂ x₀) x₀‖ < ε → g z = 0 → z = x₀ := by
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ x₀ with hc
  set a : ℂ := c x₀ with ha
  have hsrc : x₀ ∈ c.source := mem_chart_source ℂ x₀
  have hsymm : c.symm a = x₀ := by rw [ha]; exact c.left_inv hsrc
  have hana : AnalyticAt ℂ (g ∘ c.symm) a := hg x₀ (mem_univ x₀)
  have ha0 : (g ∘ c.symm) a = 0 := by
    simp only [Function.comp_apply, hsymm]
    exact hg0
  have hnotzero : ¬ ∀ᶠ w in nhds a, (g ∘ c.symm) w = 0 := by
    intro hz
    have hev : g =ᶠ[nhds x₀] (fun _ : X => (0 : ℂ)) := by
      have h1 : c.source ∈ nhds x₀ := c.open_source.mem_nhds hsrc
      have h2 : ∀ᶠ z in nhds x₀, c z ∈ {w : ℂ | (g ∘ c.symm) w = 0} :=
        (c.continuousAt hsrc).eventually hz
      filter_upwards [h2, h1] with z hz' hzsrc
      simp only [Function.comp_apply, Set.mem_setOf_eq] at hz'
      rwa [c.left_inv hzsrc] at hz'
    obtain ⟨y, hy⟩ := hne
    exact hy (holomorphicOnX_eq_zero_of_eventuallyEq_zero hg hev y)
  obtain ⟨R, k, ψ, hRpos, -, hk1, -, hψne, hψeq⟩ :=
    Commons.Analysis.Complex.exists_ball_factorization_of_analyticAt_zero
      (ρ := 1) one_pos hana ha0 hnotzero
  refine ⟨R, hRpos, ?_⟩
  intro z hzsrc hdist hgz
  have hzmem : c z ∈ Metric.ball a R := by
    rw [Metric.mem_ball, dist_eq_norm]
    exact hdist
  have hval : (g ∘ c.symm) (c z) = 0 := by
    simp only [Function.comp_apply]
    rw [c.left_inv hzsrc]
    exact hgz
  have hfac := hψeq (c z) hzmem
  rw [hval] at hfac
  have hψne' : ψ (c z) ≠ 0 := hψne (c z) hzmem
  have hk0 : k ≠ 0 := Nat.pos_iff_ne_zero.mp hk1
  have hpowzero : (c z - a) ^ k = 0 := by
    rcases mul_eq_zero.mp hfac.symm with h | h
    · exact h
    · exact absurd h hψne'
  have hca : c z = a := sub_eq_zero.mp ((pow_eq_zero_iff hk0).mp hpowzero)
  have hca' : c z = c x₀ := by rw [hca, ha]
  exact c.injOn hzsrc hsrc hca'

/-- **The Schwarz bound** for a member of the extremal family on the chart disc of radius `ρ`. -/
theorem norm_le_chartDist_div_of_mem_extremalFamily [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {x₀ : X} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : Metric.closedBall ((chartAt ℂ x₀) x₀) ρ ⊆ (chartAt ℂ x₀).target)
    {g : X → ℂ} (hg : g ∈ Submission.extremalFamily x₀) {z : X}
    (hz : z ∈ (chartAt ℂ x₀).source)
    (hzρ : ‖(chartAt ℂ x₀) z - (chartAt ℂ x₀) x₀‖ < ρ) :
    ‖g z‖ ≤ ‖(chartAt ℂ x₀) z - (chartAt ℂ x₀) x₀‖ / ρ := by
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ x₀ with hc
  set a : ℂ := c x₀ with ha
  have hhol : Submission.HolomorphicOnX g Set.univ := hg.1
  have hb : ∀ w : X, ‖g w‖ ≤ 1 := hg.2.1
  have hg0 : g x₀ = 0 := hg.2.2
  have hsrc : x₀ ∈ c.source := mem_chart_source ℂ x₀
  have hsymm : c.symm a = x₀ := by rw [ha]; exact c.left_inv hsrc
  have hcomp_a : (g ∘ c.symm) a = 0 := by
    simp only [Function.comp_apply, hsymm]
    exact hg0
  have hdiff : DifferentiableOn ℂ (g ∘ c.symm) (Metric.ball a ρ) := by
    intro w hw
    have hwt : w ∈ c.target := hsub (Metric.ball_subset_closedBall hw)
    have hwsrc : c.symm w ∈ c.source := c.map_target hwt
    have h1 : Submission.HolomorphicOnXAt g (c.symm w) := hhol _ (mem_univ _)
    have h2 := (Submission.HolomorphicOnXAt_iff_chart (f := g) (x := c.symm w) (y := x₀)
      hwsrc).mp h1
    rw [show (chartAt ℂ x₀) (c.symm w) = w from c.right_inv hwt] at h2
    exact h2.differentiableWithinAt
  have hmap : Set.MapsTo (g ∘ c.symm) (Metric.ball a ρ)
      (Metric.closedBall ((g ∘ c.symm) a) 1) := by
    intro w _
    rw [Metric.mem_closedBall, dist_eq_norm, hcomp_a, sub_zero]
    exact hb _
  have hzmem : c z ∈ Metric.ball a ρ := by
    rw [Metric.mem_ball, dist_eq_norm]
    exact hzρ
  have hmain := Complex.dist_le_div_mul_dist_of_mapsTo_ball hdiff hmap hzmem
  have h1 : dist ((g ∘ c.symm) (c z)) ((g ∘ c.symm) a) = ‖g z‖ := by
    rw [Function.comp_apply, c.left_inv hz, hcomp_a, dist_eq_norm, sub_zero]
  rw [h1, dist_eq_norm] at hmain
  have h3 : (1 : ℝ) / ρ * ‖c z - a‖ = ‖c z - a‖ / ρ := by ring
  rwa [h3] at hmain

/-- The clamped potential `z ↦ -log (max ‖g z‖ (exp (-K)))`. -/
noncomputable def clampedLogNorm (g : X → ℂ) (K : ℝ) : X → ℝ :=
  fun z => -Real.log (max ‖g z‖ (Real.exp (-K)))

theorem clampedLogNorm_apply (g : X → ℂ) (K : ℝ) (z : X) :
    clampedLogNorm g K z = -Real.log (max ‖g z‖ (Real.exp (-K))) := rfl

/-- The clamped potential is continuous (its logarithm argument is bounded below by `exp (-K)`). -/
theorem continuous_clampedLogNorm [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {g : X → ℂ} (hg : Submission.HolomorphicOnX g Set.univ) (K : ℝ) :
    Continuous (clampedLogNorm g K) := by
  have h1 : Continuous (fun z : X => max ‖g z‖ (Real.exp (-K))) :=
    hg.continuous.norm.max continuous_const
  have h2 : ∀ z : X, max ‖g z‖ (Real.exp (-K)) ≠ 0 := fun z =>
    ne_of_gt (lt_of_lt_of_le (Real.exp_pos (-K)) (le_max_right _ _))
  exact (h1.log h2).neg

/-- The clamped potential is `K` in a neighbourhood of any zero of `g`, and `-log ‖g‖` in a
neighbourhood of any point where `-log ‖g‖ ≤ K`. -/
theorem clampedLogNorm_of_le {g : X → ℂ} {K : ℝ} {z : X} (hz : g z ≠ 0)
    (h : -Real.log ‖g z‖ ≤ K) : clampedLogNorm g K z = -Real.log ‖g z‖ := by
  rw [clampedLogNorm_apply, max_eq_left]
  have hzpos : 0 < ‖g z‖ := norm_pos_iff.mpr hz
  have h1 : Real.log (Real.exp (-K)) ≤ Real.log ‖g z‖ := by
    rw [Real.log_exp]
    linarith
  exact (Real.log_le_log_iff (Real.exp_pos (-K)) hzpos).mp h1

/-- The clamped potential is superharmonic on the whole surface. -/
theorem superharmonicOnX_clampedLogNorm [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {g : X → ℂ} (hg : Submission.HolomorphicOnX g Set.univ) (K : ℝ) :
    Submission.SuperharmonicOnX (clampedLogNorm g K) Set.univ := by
  refine ⟨(continuous_clampedLogNorm hg K).continuousOn, fun x _ => ?_⟩
  by_cases hx : g x = 0
  · have hev : clampedLogNorm g K =ᶠ[nhds x] (fun _ : X => K) := by
      have hlt0 : ‖g x‖ < Real.exp (-K) := by
        rw [hx, norm_zero]
        exact Real.exp_pos (-K)
      have hcont : ContinuousAt (fun z : X => ‖g z‖) x :=
        (hg x (mem_univ x)).continuousAt.norm
      have hlt : ∀ᶠ z in nhds x, ‖g z‖ < Real.exp (-K) :=
        hcont.eventually (isOpen_Iio.mem_nhds hlt0)
      filter_upwards [hlt] with z hz
      rw [clampedLogNorm_apply, max_eq_right hz.le, Real.log_exp]
      ring
    exact Submission.SuperharmonicOnXAt.congr
      (Submission.harmonicOnXAt_const K).superharmonic hev.symm
  · have hev : clampedLogNorm g K =ᶠ[nhds x] (fun z : X => min (-Real.log ‖g z‖) K) := by
      have hne : ∀ᶠ z in nhds x, g z ≠ 0 :=
        (hg x (mem_univ x)).continuousAt.eventually_ne hx
      filter_upwards [hne] with z hz
      rcases lt_or_ge ‖g z‖ (Real.exp (-K)) with h | h
      · have h1 : K ≤ -Real.log ‖g z‖ := by
          have hzpos : 0 < ‖g z‖ := norm_pos_iff.mpr hz
          have h2 : Real.log ‖g z‖ < Real.log (Real.exp (-K)) := Real.log_lt_log hzpos h
          rw [Real.log_exp] at h2
          linarith
        rw [clampedLogNorm_apply, max_eq_right h.le, Real.log_exp, min_eq_right h1]
        ring
      · have h1 : -Real.log ‖g z‖ ≤ K := by
          have h2 : Real.log (Real.exp (-K)) ≤ Real.log ‖g z‖ :=
            Real.log_le_log (Real.exp_pos (-K)) h
          rw [Real.log_exp] at h2
          linarith
        rw [clampedLogNorm_apply, max_eq_left h, min_eq_left h1]
    refine Submission.SuperharmonicOnXAt.congr ?_ hev.symm
    exact Submission.SuperharmonicOnXAt.min
      (Submission.harmonicOnXAt_neg_log_norm (hg x (mem_univ x)) hx).superharmonic
      (Submission.harmonicOnXAt_const K).superharmonic

/-- Away from the zeros of `g` the clamped potential is the minimum of `-log ‖g‖` and `K`. -/
theorem clampedLogNorm_eq_min {g : X → ℂ} {K : ℝ} {z : X} (hz : g z ≠ 0) :
    clampedLogNorm g K z = min (-Real.log ‖g z‖) K := by
  rcases lt_or_ge ‖g z‖ (Real.exp (-K)) with h | h
  · have h1 : K ≤ -Real.log ‖g z‖ := by
      have hzpos : 0 < ‖g z‖ := norm_pos_iff.mpr hz
      have h2 : Real.log ‖g z‖ < Real.log (Real.exp (-K)) := Real.log_lt_log hzpos h
      rw [Real.log_exp] at h2
      linarith
    rw [clampedLogNorm_apply, max_eq_right h.le, Real.log_exp, min_eq_right h1]
    ring
  · have h1 : -Real.log ‖g z‖ ≤ K := by
      have h2 : Real.log (Real.exp (-K)) ≤ Real.log ‖g z‖ :=
        Real.log_le_log (Real.exp_pos (-K)) h
      rw [Real.log_exp] at h2
      linarith
    rw [clampedLogNorm_apply, max_eq_left h, min_eq_left h1]

/-- The clamped potential equals `K` at the zeros of `g`. -/
theorem clampedLogNorm_of_eq_zero {g : X → ℂ} {K : ℝ} {z : X} (hz : g z = 0) :
    clampedLogNorm g K z = K := by
  rw [clampedLogNorm_apply, hz, norm_zero, max_eq_right (Real.exp_pos (-K)).le, Real.log_exp]
  ring

/-- The clamped potential is below `-log ‖g‖` where `g ≠ 0`. -/
theorem clampedLogNorm_le_neg_log {g : X → ℂ} {K : ℝ} {z : X} (hz : g z ≠ 0) :
    clampedLogNorm g K z ≤ -Real.log ‖g z‖ := by
  rw [clampedLogNorm_apply, neg_le_neg_iff]
  exact Real.log_le_log (norm_pos_iff.mpr hz) (le_max_left _ _)

/-- The clamped potential is non-negative when `K ≥ 0` and `‖g‖ ≤ 1`. -/
theorem clampedLogNorm_nonneg {g : X → ℂ} {K : ℝ} (hK : 0 ≤ K) (hb : ∀ z : X, ‖g z‖ ≤ 1)
    (z : X) : 0 ≤ clampedLogNorm g K z := by
  have h1 : max ‖g z‖ (Real.exp (-K)) ≤ 1 := by
    refine max_le (hb z) ?_
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  rw [clampedLogNorm_apply, neg_nonneg]
  exact Real.log_nonpos (le_trans (le_of_lt (Real.exp_pos (-K))) (le_max_right _ _)) h1

end Work.SimplyConnected.ABS
