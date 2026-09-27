import Mathlib
import Submission.Work.Noncompact.CompressionTube.exists_straightened_chart_twoSided
import Submission.Work.Routing.spreadAxisFix
import Submission.Work.Routing.spreadNormalize
import Submission.Work.Routing.pasteCharts
import Submission.Work.Routing.injectiveOn_nhds_of_injective_arc
import Submission.Work.Routing.injOn_nhds_of_compact_of_locallyInjOn
import Submission.Work.Noncompact.CompressionTube.exists_collar_of_local_slabs
import Submission.Work.Noncompact.Routing.arc_height_on_Icc
import Submission.Work.Noncompact.Routing.arc_local_section
import Submission.Work.Noncompact.Routing.arc_transverse_local
import Submission.Work.Compat.MFDerivCongrV433

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


/-!
# Stretching a straightened chart along an arc

`Work.Routing.straightenedChartStretch`: if `α : ℝ → M` is a smooth curve in an `n`-manifold whose
derivative is injective at every `t ∈ [0,1]` and which is injective on `[0,1]`, then for every
`s ∈ (0,1]` there is a chart `c` of the maximal atlas with `α 1 ∈ c.source` and
`c (α t) = c (α 1) + (t - 1) • w` for all `t ∈ [1-s,1]`.

This file builds the straightening along the whole arc `[1-s,1]`, not just near `t = 1`.

## The route

The hypothesis `himm` is available only on `[0,1]`, so the first step is to propagate it to a
*window* around `[0,1]`:

* `mfderiv_injective_iff_fderiv_chart`: in a chart, `γ` is an immersion at `t` iff the coordinate
  expression has injective derivative at `t`;
* `injOn_Ioo_of_injective_mfderiv`: the inverse function theorem in one parameter gives injectivity
  of `γ` near a point of immersion;
* `injective_mfderiv_on_window`: the set of immersion parameters is open (a nonzero derivative in a
  chart stays nonzero nearby), hence contains a window `(-δ, 1+δ)`;
* `injOn_window_of_immersion`: an immersed arc injective on `[0,1]` is injective on a window (the
  boundary is handled by the local injectivity at `0` and `1` plus a height function).

With a window in hand, the existing tube chapter is applied without any global immersion
hypothesis: `arc_height_on_Icc'` and `exists_local_left_inverse_on_Icc'` are the interval-restricted
forms of the height construction (the only place where `himm` was used globally), the transverse
coordinate comes from `Work.Noncompact.Routing.arc_transverse_local`, the slab sections from
`arc_local_section`, and `exists_tubeChart_with_axis` is `arc_tube_chart_assembly` with the extra
conclusion that the chart sends `γ t` to `(0, t)` on `[0,1]`.

Composing that chart with a linear equivalence `ℝ^{n-1} × ℝ ≃ ℝⁿ` sends `(0, t)` to `t • w`, and the
resulting chart of the maximal atlas straightens the arc on `[0,1] ⊇ [1-s,1]`.
-/

namespace Work.Routing

open Set Topology Filter
open scoped Manifold ContDiff
open Work.Noncompact.CompressionTube

set_option linter.unusedVariables false

variable {n : ℕ}

set_option backward.isDefEq.respectTransparency false in
/-- **Local straightening at a parameter.**  If the derivative of a smooth curve `γ : ℝ → M` is
injective at `s`, then there are a chart `c` of the maximal atlas, a direction `u ≠ 0` and an
extent `e > 0` with `c (γ t) = c (γ s) + (t - s) • u` for `|t - s| ≤ e`. -/
theorem localStraighteningAt {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M]
    {γ : ℝ → M} (hγ : ContMDiff Work.Noncompact.CompressionTube.MCreal
      (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder γ)
    (s : ℝ)
    (himm : Function.Injective (mfderiv Work.Noncompact.CompressionTube.MCreal
      (Work.Noncompact.CompressionTube.MC n) γ s)) :
    ∃ (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (u : EuclideanSpace ℝ (Fin n)) (e : ℝ),
      0 < e ∧ u ≠ 0 ∧
      c ∈ IsManifold.maximalAtlas (Work.Noncompact.CompressionTube.MC n)
        Work.Noncompact.CompressionTube.smoothOrder M ∧
      γ s ∈ c.source ∧
      ∀ t : ℝ, |t - s| ≤ e → γ t ∈ c.source ∧ c (γ t) = c (γ s) + (t - s) • u := by
  classical
  have hn0 : Work.Noncompact.CompressionTube.smoothOrder ≠ (0 : WithTop ℕ∞) := by
    simp [Work.Noncompact.CompressionTube.smoothOrder]
  have hshift_md : MDifferentiableAt Work.Noncompact.CompressionTube.MCreal
      Work.Noncompact.CompressionTube.MCreal (fun t : ℝ => t + (s - 1)) 1 := by
    have heq : (fun t : ℝ => t + (s - 1))
        = (id : ℝ → ℝ) + (fun _ : ℝ => (s - 1)) := by
      funext t; rfl
    rw [heq]; exact mdifferentiableAt_id.add mdifferentiableAt_const
  have hshift : mfderiv Work.Noncompact.CompressionTube.MCreal
      Work.Noncompact.CompressionTube.MCreal (fun t : ℝ => t + (s - 1)) 1
      = ContinuousLinearMap.id ℝ (TangentSpace Work.Noncompact.CompressionTube.MCreal (1 : ℝ)) := by
    have heq : (fun t : ℝ => t + (s - 1))
        = (id : ℝ → ℝ) + (fun _ : ℝ => (s - 1)) := by
      funext t; rfl
    rw [heq, mfderiv_add mdifferentiableAt_id mdifferentiableAt_const,
      mfderiv_id, mfderiv_const]
    exact add_zero _
  have hα : ContMDiff Work.Noncompact.CompressionTube.MCreal
      (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder (fun t : ℝ => γ (t + (s - 1))) := by
    have hshift_sm : ContMDiff Work.Noncompact.CompressionTube.MCreal
        Work.Noncompact.CompressionTube.MCreal Work.Noncompact.CompressionTube.smoothOrder
        (fun t : ℝ => t + (s - 1)) := by
      have heq : (fun t : ℝ => t + (s - 1))
          = (id : ℝ → ℝ) + (fun _ : ℝ => (s - 1)) := by
        funext t; rfl
      rw [heq]; exact contMDiff_id.add contMDiff_const
    exact hγ.comp hshift_sm
  have hchain : mfderiv Work.Noncompact.CompressionTube.MCreal
      (Work.Noncompact.CompressionTube.MC n) (fun t : ℝ => γ (t + (s - 1))) 1
      = mfderiv Work.Noncompact.CompressionTube.MCreal
        (Work.Noncompact.CompressionTube.MC n) γ s := by
    have hγmd : MDifferentiableAt Work.Noncompact.CompressionTube.MCreal
        (Work.Noncompact.CompressionTube.MC n) γ (1 + (s - 1)) :=
      hγ.contMDiffAt.mdifferentiableAt hn0
    rw [show (fun t : ℝ => γ (t + (s - 1)))
        = γ ∘ (fun t : ℝ => t + (s - 1)) from rfl,
      mfderiv_comp (I := Work.Noncompact.CompressionTube.MCreal)
        (I' := Work.Noncompact.CompressionTube.MCreal)
        (I'' := Work.Noncompact.CompressionTube.MC n) 1 hγmd hshift_md,
      hshift, show (1 : ℝ) + (s - 1) = s from by ring_nf]
    simp
  have hαimm : Function.Injective (mfderiv Work.Noncompact.CompressionTube.MCreal
      (Work.Noncompact.CompressionTube.MC n) (fun t : ℝ => γ (t + (s - 1))) 1) := by
    rw [hchain]; exact himm
  obtain ⟨c, w, e, he, hw, hc, hsrc, hgerm⟩ :=
    Work.Noncompact.CompressionTube.exists_straightened_chart_twoSided (n := n) (M := M)
      (α := fun t : ℝ => γ (t + (s - 1))) hα hαimm
  have hsrc' : γ s ∈ c.source := by
    have h : (fun t : ℝ => γ (t + (s - 1))) 1 ∈ c.source := hsrc
    simpa [show (1 : ℝ) + (s - 1) = s from by ring_nf] using h
  refine ⟨c, w, e, he, hw, hc, hsrc', fun t ht => ?_⟩
  have harg : |(t - s + 1) - 1| ≤ e := by
    rw [show t - s + 1 - 1 = t - s from by ring_nf]; exact ht
  obtain ⟨h1, h2⟩ := hgerm (t - s + 1) harg
  refine ⟨?_, ?_⟩
  · simpa [show (t - s + 1) + (s - 1) = t from by ring_nf] using h1
  · have h3 : c (γ t) = c (γ (1 + (s - 1))) + ((t - s + 1) - 1) • w := by
      simpa [show (t - s + 1) + (s - 1) = t from by ring_nf] using h2
    rw [show (1 : ℝ) + (s - 1) = s from by ring_nf,
      show t - s + 1 - 1 = t - s from by ring_nf] at h3
    exact h3


/-- **Smooth totalisation at a base point.**  A function that is smooth on a neighbourhood of a ball
can be modified outside a smaller ball so that it is smooth everywhere, without changing its values
or its derivatives on the smaller ball. -/
theorem totaliseSmooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {U : Set E} (hU : IsOpen U) {x₀ : E} {ρ : ℝ} (hρ : 0 < ρ)
    (hball : Metric.ball x₀ ρ ⊆ U)
    {f : E → E} (hf : ∀ y ∈ U, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f y) :
    ∃ f' : E → E,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f' ∧
      (∀ y, ‖y - x₀‖ < ρ / 2 → f' y = f y) ∧
      (∀ y, ‖y - x₀‖ < ρ / 2 → fderiv ℝ f' y = fderiv ℝ f y) := by
  classical
  haveI : HasContDiffBump E := inferInstance
  let b : ContDiffBump x₀ := ⟨ρ / 2, ρ * 3 / 4, by positivity, by linarith⟩
  have hbsupp : Function.support (fun y : E => (b : E → ℝ) y) = Metric.ball x₀ b.rOut :=
    ContDiffBump.support_eq b
  have hbclos : closure (Function.support (fun y : E => (b : E → ℝ) y))
      = Metric.closedBall x₀ b.rOut := by
    rw [hbsupp, closure_ball _ b.rOut_pos.ne']
  have hsub : Metric.closedBall x₀ b.rOut ⊆ U := by
    refine Subset.trans (Metric.closedBall_subset_ball ?_) hball
    show b.rOut < ρ
    have h1 : b.rOut = ρ * 3 / 4 := rfl
    rw [h1]; linarith
  have hcont : ∀ z : E, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : E => b y • f y) z := by
    intro z
    by_cases hz : z ∈ closure (Function.support (fun y : E => (b : E → ℝ) y))
    · have hzU : z ∈ U := hsub (by rw [hbclos] at hz; exact hz)
      exact (ContDiffBump.contDiff b).contDiffAt.smul (hf z hzU)
    · have hz' : b.rOut < dist z x₀ := by
        by_contra hcon
        push Not at hcon
        exact hz (by rw [hbclos]; rwa [Metric.mem_closedBall])
      have hball0 : Metric.ball z (dist z x₀ - b.rOut) ⊆ (Function.support
          (fun y : E => (b : E → ℝ) y))ᶜ := by
        intro w hw
        rw [Set.mem_compl_iff, Function.mem_support, not_not]
        apply ContDiffBump.zero_of_le_dist b
        have h2 : dist z x₀ ≤ dist z w + dist w x₀ := dist_triangle _ _ _
        rw [Metric.mem_ball, dist_comm] at hw
        linarith
      have hb0 : (fun y : E => b y • f y) =ᶠ[𝓝 z] (fun _ => (0 : E)) := by
        refine Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds
          (Metric.mem_ball_self (sub_pos.mpr hz'))) ?_
        intro w hw
        have hw0 : b w = 0 := by simpa [Function.mem_support, not_not] using hball0 hw
        show b w • f w = (0 : E)
        rw [hw0, zero_smul]
      exact (ContDiffAt.congr_of_eventuallyEq (contDiffAt_const :
        ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : E => (0 : E)) z) hb0)
  refine ⟨fun y : E => b y • f y, ?_, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]; exact hcont
  · intro y hy
    have hy1 : y ∈ Metric.closedBall x₀ b.rIn := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      show ‖y - x₀‖ ≤ b.rIn
      have h1 : b.rIn = ρ / 2 := rfl
      rw [h1]; exact le_of_lt hy
    show b y • f y = f y
    rw [ContDiffBump.one_of_mem_closedBall b hy1, one_smul]
  · intro y hy
    have hopen : Metric.ball x₀ b.rIn ∈ 𝓝 y := by
      apply Metric.isOpen_ball.mem_nhds
      rw [Metric.mem_ball, dist_eq_norm]
      show ‖y - x₀‖ < b.rIn
      have h1 : b.rIn = ρ / 2 := rfl
      rw [h1]; exact hy
    have hev : (fun z : E => b z • f z) =ᶠ[𝓝 y] f := by
      refine Filter.eventually_of_mem hopen ?_
      intro z hz
      show b z • f z = f z
      rw [ContDiffBump.one_of_mem_closedBall b (Metric.ball_subset_closedBall hz), one_smul]
    rw [hev.fderiv_eq]


/-- **A bump function in `ℝⁿ` with an explicit derivative bound.** -/
theorem bumpFderivBound {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r) :
    ∃ (χ : EuclideanSpace ℝ (Fin n) → ℝ) (K : ℝ), 0 < K ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧
      (∀ z, ‖z‖ ≤ r → χ z = 1) ∧
      (∀ z, 2 * r ≤ ‖z‖ → χ z = 0) ∧
      (∀ z, 0 ≤ χ z) ∧ (∀ z, χ z ≤ 1) ∧
      (∀ z, ‖fderiv ℝ χ z‖ ≤ K / r) := by
  classical
  haveI : HasContDiffBump (EuclideanSpace ℝ (Fin n)) := inferInstance
  let φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) := ⟨1, 2, one_pos, one_lt_two⟩
  have hφsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin n) => φ z) := ContDiffBump.contDiff φ
  have hφ0 : φ.rIn = 1 := rfl
  have hφ1 : φ.rOut = 2 := rfl
  have hφfd : Continuous (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin n) => φ z)) :=
    hφsm.continuous_fderiv (by simp)
  obtain ⟨C, hC⟩ := HasCompactSupport.exists_bound_of_continuous
    ((ContDiffBump.hasCompactSupport φ).fderiv ℝ) hφfd
  have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  refine ⟨fun z => φ (r⁻¹ • z), max C 1 * 2, by positivity, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- smoothness
    have : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : EuclideanSpace ℝ (Fin n) => r⁻¹ • z) := by
      fun_prop
    exact hφsm.comp this
  · -- equals one on the closed ball of radius `r`
    intro z hz
    refine ContDiffBump.one_of_mem_closedBall φ ?_
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, hφ0]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ r⁻¹),
      inv_mul_eq_div, div_le_one hr]
    exact hz
  · -- vanishes outside the ball of radius `2r`
    intro z hz
    refine ContDiffBump.zero_of_le_dist φ ?_
    rw [hφ1, dist_eq_norm, sub_zero]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ r⁻¹),
      inv_mul_eq_div, le_div_iff₀ hr]
    linarith
  · intro z; exact ContDiffBump.nonneg φ
  · intro z; exact ContDiffBump.le_one φ
  · -- the derivative bound
    intro z
    have hderiv : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => φ (r⁻¹ • y)) z
        = (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => φ y) (r⁻¹ • z)).comp
            (r⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) := by
      have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => r⁻¹ • y)
          (r⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) z :=
        (hasFDerivAt_id z).const_smul (r⁻¹)
      have h2 : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => φ y)
          (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => φ y) (r⁻¹ • z)) (r⁻¹ • z) :=
        (hφsm.differentiable (by simp)).differentiableAt.hasFDerivAt
      exact (h2.comp z h1).fderiv
    have hnorm : ‖(fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => φ y) (r⁻¹ • z)).comp
        (r⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))‖ ≤ C * r⁻¹ := by
      have h2 : ‖r⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ ≤ r⁻¹ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ r⁻¹)]
        calc r⁻¹ * ‖ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ ≤ r⁻¹ * 1 :=
              mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (by positivity)
          _ = r⁻¹ := by ring
      calc ‖(fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => φ y) (r⁻¹ • z)).comp
              (r⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))‖
            ≤ ‖fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => φ y) (r⁻¹ • z)‖
              * ‖r⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ :=
              ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ C * r⁻¹ := mul_le_mul (hC (r⁻¹ • z)) h2 (by positivity) hCnn
    rw [hderiv]
    calc ‖fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => φ y) (r⁻¹ • z) ∘SL
            (r⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))‖
          ≤ C * r⁻¹ := hnorm
      _ ≤ max C 1 * 2 / r := by
          have h1 : C ≤ max C 1 * 2 := by
            nlinarith [le_max_left C 1, le_max_right C 1, hCnn]
          calc C * r⁻¹ ≤ (max C 1 * 2) * r⁻¹ :=
                mul_le_mul_of_nonneg_right h1 (by positivity)
            _ = (max C 1 * 2) / r := by rw [div_eq_mul_inv]



set_option backward.isDefEq.respectTransparency false in
/-- **Product rule for a scalar function times a vector function.**  (Mathlib has this for
`fderiv`/`HasFDerivWithinAt` but not for `HasMFDerivAt`; the proof is the coordinate-wise product
rule `HasFDerivWithinAt.smul`.) -/
theorem hasMFDerivAt_smul {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M]
    {f : M → ℝ} {g : M → EuclideanSpace ℝ (Fin n)} {x : M}
    {f' : TangentSpace (Work.Noncompact.CompressionTube.MC n) x →L[ℝ] ℝ}
    {g' : TangentSpace (Work.Noncompact.CompressionTube.MC n) x →L[ℝ]
      EuclideanSpace ℝ (Fin n)}
    (hf : HasMFDerivAt (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.MCreal f x f')
    (hg : HasMFDerivAt (Work.Noncompact.CompressionTube.MC n)
      (Work.Noncompact.CompressionTube.MC n) g x g') :
    HasMFDerivAt (Work.Noncompact.CompressionTube.MC n)
      (Work.Noncompact.CompressionTube.MC n)
      (fun y => f y • g y) x (f x • g' + f'.smulRight (g x)) := by
  refine ⟨hf.1.smul hg.1, ?_⟩
  simpa using! hf.2.smul hg.2

section WindowLemmas

set_option backward.isDefEq.respectTransparency false in
/-- The chart expression of `γ` has injective derivative at `t` exactly when `γ` does. -/
theorem mfderiv_injective_iff_fderiv_chart {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (MC n) smoothOrder M]
    {γ : ℝ → M} (hγ : ContMDiff MCreal (MC n) smoothOrder γ)
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hc : c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M)
    {t : ℝ} (ht : γ t ∈ c.source) :
    Function.Injective (fderiv ℝ (fun s => c (γ s)) t) ↔
      Function.Injective (mfderiv MCreal (MC n) γ t) := by
  have hn : smoothOrder ≠ (0 : WithTop ℕ∞) := by simp [smoothOrder]
  have hcm : MDifferentiableAt (MC n) (MC n) (c : M → EuclideanSpace ℝ (Fin n)) (γ t) :=
    (contMDiffAt_of_mem_maximalAtlas hc ht).mdifferentiableAt hn
  have hγm : MDifferentiableAt MCreal (MC n) γ t := hγ.mdifferentiableAt (x := t) hn
  have hFA : HasFDerivAt (fun s => c (γ s))
      ((mfderiv (MC n) (MC n) (c : M → EuclideanSpace ℝ (Fin n)) (γ t)).comp
        (mfderiv MCreal (MC n) γ t)) t :=
    (hcm.hasMFDerivAt.comp t hγm.hasMFDerivAt).hasFDerivAt
  constructor
  · intro hΦ v w hvw
    have hcomp : Function.Injective (⇑((mfderiv (MC n) (MC n)
        (c : M → EuclideanSpace ℝ (Fin n)) (γ t)).comp (mfderiv MCreal (MC n) γ t))) := by
      rw [← hFA.fderiv]
      exact hΦ
    have h1 : (mfderiv (MC n) (MC n) (c : M → EuclideanSpace ℝ (Fin n)) (γ t))
        ((mfderiv MCreal (MC n) γ t) v)
        = (mfderiv (MC n) (MC n) (c : M → EuclideanSpace ℝ (Fin n)) (γ t))
        ((mfderiv MCreal (MC n) γ t) w) := by
      rw [hvw]
    exact hcomp h1
  · intro himm
    have hcomp : Function.Injective
        ((⇑(mfderiv (MC n) (MC n) (c : M → EuclideanSpace ℝ (Fin n)) (γ t))) ∘
         (⇑(mfderiv MCreal (MC n) γ t))) :=
      (isLocalDiffeomorphAt_chart_mfderiv_injective hc ht).comp himm
    rw [hFA.fderiv]
    exact hcomp

set_option backward.isDefEq.respectTransparency false in
/-- **An immersed curve is injective in the parameter near a point of immersion.** -/
theorem injOn_Ioo_of_injective_mfderiv {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (MC n) smoothOrder M]
    {γ : ℝ → M} (hγ : ContMDiff MCreal (MC n) smoothOrder γ) (t : ℝ)
    (himm : Function.Injective (mfderiv MCreal (MC n) γ t)) :
    ∃ ρ : ℝ, 0 < ρ ∧ Set.InjOn γ (Set.Ioo (t - ρ) (t + ρ)) := by
  classical
  have hn : smoothOrder ≠ (0 : WithTop ℕ∞) := by simp [smoothOrder]
  set c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    chartAt (EuclideanSpace ℝ (Fin n)) (γ t) with hcdef
  have hc : c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M :=
    IsManifold.chart_mem_maximalAtlas (γ t)
  have hmem : γ t ∈ c.source := mem_chart_source _ (γ t)
  have hI : IsOpen (γ ⁻¹' c.source) := c.open_source.preimage hγ.continuous
  have htI : t ∈ γ ⁻¹' c.source := hmem
  set h : ℝ → EuclideanSpace ℝ (Fin n) := fun s => c (γ s) with hhdef
  have hsm : ContDiffOn ℝ smoothOrder h (γ ⁻¹' c.source) :=
    contMDiffOn_iff_contDiffOn.mp
      ((contMDiffOn_of_mem_maximalAtlas hc).comp hγ.contMDiffOn (fun s hs => hs))
  have hcd : ContDiffAt ℝ smoothOrder h t := hsm.contDiffAt (hI.mem_nhds htI)
  have hinj : Function.Injective (fderiv ℝ h t) :=
    (mfderiv_injective_iff_fderiv_chart hγ hc hmem).mpr himm
  have hhat : HasFDerivAt h (fderiv ℝ h t) t := (hcd.differentiableAt hn).hasFDerivAt
  have hne : fderiv ℝ h t 1 ≠ 0 := fun h0 => one_ne_zero (hinj (by rw [h0, map_zero]))
  obtain ⟨j, hj⟩ : ∃ j : Fin n, (fderiv ℝ h t 1) j ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact hne (PiLp.ext hcon)
  set v : ℝ → ℝ := fun s => (c (γ s)) j with hvdef
  have hv_sm : ContDiffOn ℝ smoothOrder v (γ ⁻¹' c.source) := by
    have h1 : ContDiffOn ℝ smoothOrder
        (fun s : ℝ => (EuclideanSpace.proj (𝕜 := ℝ) j) (c (γ s))) (γ ⁻¹' c.source) :=
      (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp_contDiffOn hsm
    refine h1.congr (fun s _ => ?_)
    simp only [hvdef, PiLp.proj_apply]
  have hv_cd : ContDiffAt ℝ smoothOrder v t := hv_sm.contDiffAt (hI.mem_nhds htI)
  have hv_fderiv : fderiv ℝ v t = (EuclideanSpace.proj (𝕜 := ℝ) j) ∘L fderiv ℝ h t := by
    have h1 : HasFDerivAt (fun s : ℝ => (EuclideanSpace.proj (𝕜 := ℝ) j) (c (γ s)))
        ((EuclideanSpace.proj (𝕜 := ℝ) j) ∘L fderiv ℝ h t) t :=
      (EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt.comp t hhat
    have hveq : v = fun s : ℝ => (EuclideanSpace.proj (𝕜 := ℝ) j) (c (γ s)) := by
      funext s
      rw [hvdef, PiLp.proj_apply]
    rw [hveq]
    exact h1.fderiv
  have hv_one : fderiv ℝ v t 1 ≠ 0 := by
    rw [hv_fderiv, ContinuousLinearMap.comp_apply]
    simpa [PiLp.proj_apply] using hj
  have hv_inj : Function.Injective (fderiv ℝ v t) := by
    intro x y hxy
    have h2 : (fderiv ℝ v t) (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have h1 : (x - y) • (fderiv ℝ v t 1) = 0 := by
      calc (x - y) • (fderiv ℝ v t 1)
          = (fderiv ℝ v t) ((x - y) • (1 : ℝ)) :=
            (ContinuousLinearMap.map_smul _ _ _).symm
        _ = (fderiv ℝ v t) (x - y) := by rw [smul_eq_mul, mul_one]
        _ = 0 := h2
    rcases smul_eq_zero.mp h1 with hh | hh
    · exact sub_eq_zero.mp hh
    · exact absurd hh hv_one
  obtain ⟨L, hL⟩ := Work.Noncompact.CompressionTube.exists_continuousLinearEquiv_of_injective
    (E := ℝ) (E' := ℝ) rfl (fderiv ℝ v t) hv_inj
  have hvL : HasFDerivAt v (L : ℝ →L[ℝ] ℝ) t :=
    HasFDerivAt.congr_fderiv (hv_cd.differentiableAt hn).hasFDerivAt hL.symm
  set φ : OpenPartialHomeomorph ℝ ℝ := hv_cd.toOpenPartialHomeomorph v hvL hn with hφdef
  have hφcoe : (φ : ℝ → ℝ) = v := ContDiffAt.toOpenPartialHomeomorph_coe hv_cd hvL hn
  have htφ : t ∈ φ.source := ContDiffAt.mem_toOpenPartialHomeomorph_source hv_cd hvL hn
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.mp (φ.open_source.mem_nhds htφ)
  refine ⟨ρ, hρpos, ?_⟩
  intro a ha b hb hab
  rw [Set.mem_Ioo] at ha hb
  have ha' : a ∈ φ.source := hρsub (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [ha.1], by linarith [ha.2]⟩)
  have hb' : b ∈ φ.source := hρsub (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [hb.1], by linarith [hb.2]⟩)
  have hva : v a = v b := by
    have h2 := congrArg (fun z : EuclideanSpace ℝ (Fin n) => z j) (congrArg c hab)
    simpa only [hvdef] using h2
  exact φ.injOn ha' hb' (by rw [hφcoe]; exact hva)

end WindowLemmas

set_option backward.isDefEq.respectTransparency false in
/-- **The set of immersion parameters is open, hence `[0,1]` lies in a window of immersion.** -/
theorem injective_mfderiv_on_window {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (MC n) smoothOrder M]
    {γ : ℝ → M} (hγ : ContMDiff MCreal (MC n) smoothOrder γ)
    (himm : ∀ t ∈ Set.Icc (0:ℝ) 1, Function.Injective (mfderiv MCreal (MC n) γ t)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Set.Icc (-δ) (1 + δ),
      Function.Injective (mfderiv MCreal (MC n) γ t) := by
  classical
  have hn : smoothOrder ≠ (0 : WithTop ℕ∞) := by simp [smoothOrder]
  have hopen : IsOpen {t : ℝ | Function.Injective (mfderiv MCreal (MC n) γ t)} := by
    rw [isOpen_iff_mem_nhds]
    intro t₀ ht₀
    set c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
      chartAt (EuclideanSpace ℝ (Fin n)) (γ t₀) with hcdef
    have hc : c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M :=
      IsManifold.chart_mem_maximalAtlas (γ t₀)
    have hmem : γ t₀ ∈ c.source := mem_chart_source _ (γ t₀)
    have hI : IsOpen (γ ⁻¹' c.source) := c.open_source.preimage hγ.continuous
    have ht₀I : t₀ ∈ γ ⁻¹' c.source := hmem
    have hsm : ContDiffOn ℝ smoothOrder (fun s => c (γ s)) (γ ⁻¹' c.source) :=
      contMDiffOn_iff_contDiffOn.mp
        ((contMDiffOn_of_mem_maximalAtlas hc).comp hγ.contMDiffOn (fun s hs => hs))
    have hcd : ContDiffAt ℝ smoothOrder (fun s => c (γ s)) t₀ := hsm.contDiffAt (hI.mem_nhds ht₀I)
    have hcont : ContinuousAt (fun u : ℝ => fderiv ℝ (fun s => c (γ s)) u) t₀ :=
      hcd.continuousAt_fderiv hn
    have hcont1 : ContinuousAt (fun u : ℝ => (fderiv ℝ (fun s => c (γ s)) u) 1) t₀ :=
      (((ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin n))) 1).continuous.continuousAt).comp hcont
    have hfj : Function.Injective (fderiv ℝ (fun s => c (γ s)) t₀) :=
      (mfderiv_injective_iff_fderiv_chart hγ hc hmem).mpr ht₀
    have hne0 : (fderiv ℝ (fun s => c (γ s)) t₀) 1 ≠ 0 :=
      fun h0 => one_ne_zero (hfj (by rw [h0, map_zero]))
    have hA : {u : ℝ | (fderiv ℝ (fun s => c (γ s)) u) 1 ≠ 0} ∈ 𝓝 t₀ :=
      hcont1.preimage_mem_nhds (isOpen_ne.mem_nhds hne0)
    refine Filter.mem_of_superset (Filter.inter_mem (hI.mem_nhds ht₀I) hA) ?_
    rintro u ⟨hu1, hu2⟩
    refine (mfderiv_injective_iff_fderiv_chart hγ hc hu1).mp (fun v w hvw => ?_)
    have h1 : (fderiv ℝ (fun s => c (γ s)) u) (v - w) = 0 := by rw [map_sub, hvw, sub_self]
    have h2 : (v - w) • (fderiv ℝ (fun s => c (γ s)) u) 1 = 0 := by
      calc (v - w) • (fderiv ℝ (fun s => c (γ s)) u) 1
          = (fderiv ℝ (fun s => c (γ s)) u) ((v - w) • (1 : ℝ)) :=
            (ContinuousLinearMap.map_smul _ _ _).symm
        _ = (fderiv ℝ (fun s => c (γ s)) u) (v - w) := by rw [smul_eq_mul, mul_one]
        _ = 0 := h1
    rcases smul_eq_zero.mp h2 with hh | hh
    · exact sub_eq_zero.mp hh
    · exact absurd hh hu2
  obtain ⟨δ, hδpos, hδsub⟩ :=
    IsCompact.exists_cthickening_subset_open isCompact_Icc hopen (fun t ht => himm t ht)
  refine ⟨δ, hδpos, fun t ht => hδsub ?_⟩
  rw [Metric.mem_cthickening_iff]
  have hy : min 1 (max 0 t) ∈ Set.Icc (0:ℝ) 1 :=
    ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩
  have hdist : dist t (min 1 (max 0 t)) ≤ δ := by
    rw [Real.dist_eq]
    rcases le_total t 0 with h | h
    · rw [max_eq_left h, min_eq_right (by norm_num : (0:ℝ) ≤ 1), sub_zero, abs_of_nonpos h]
      linarith [ht.1]
    · rcases le_total t 1 with h1 | h1
      · rw [max_eq_right h, min_eq_right h1, sub_self, abs_zero]
        exact le_of_lt hδpos
      · rw [max_eq_right h, min_eq_left h1, abs_of_nonneg (by linarith)]
        linarith [ht.2]
  calc Metric.infEDist t (Set.Icc (0:ℝ) 1)
      ≤ edist t (min 1 (max 0 t)) := Metric.infEDist_le_edist_of_mem hy
    _ = ENNReal.ofReal (dist t (min 1 (max 0 t))) := edist_dist _ _
    _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal hdist

section HeightOnInterval

set_option maxHeartbeats 800000 in
/-- **Local smooth left inverse of an immersed curve** (hypothesis restricted to the interval). -/
theorem exists_local_left_inverse_on_Icc' {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (MC n) smoothOrder M] [T2Space M]
    {γ : ℝ → M} (hγ : ContMDiff MCreal (MC n) smoothOrder γ) {a b : ℝ}
    (himm : ∀ t : ℝ, t ∈ Set.Icc a b → Function.Injective (mfderiv MCreal (MC n) γ t))
    {s : ℝ} (hγinj : Set.InjOn γ (Set.Icc a b)) (hs : s ∈ Set.Icc a b) :
    ∃ (U : Set M) (F : M → ℝ), IsOpen U ∧ γ s ∈ U ∧
      ContMDiffOn (MC n) MCreal smoothOrder F U ∧
      ∀ t : ℝ, t ∈ Set.Icc a b → γ t ∈ U → F (γ t) = t := by
  classical
  set c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    chartAt (EuclideanSpace ℝ (Fin n)) (γ s) with hc_def
  have hc : c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M :=
    IsManifold.chart_mem_maximalAtlas (γ s)
  have hmem : γ s ∈ c.source := mem_chart_source (EuclideanSpace ℝ (Fin n)) (γ s)
  have hI : IsOpen (γ ⁻¹' c.source) := c.open_source.preimage hγ.continuous
  have hsI : s ∈ γ ⁻¹' c.source := hmem
  have hh_smooth : ContDiffOn ℝ smoothOrder (fun t => c (γ t)) (γ ⁻¹' c.source) :=
    contMDiffOn_iff_contDiffOn.mp
      ((contMDiffOn_of_mem_maximalAtlas hc).comp hγ.contMDiffOn (fun t ht => ht))
  have hh_inj : Function.Injective (fderiv ℝ (fun t => c (γ t)) s) :=
    (mfderiv_injective_iff_fderiv_chart hγ hc hmem).mpr (himm s hs)
  have hne : fderiv ℝ (fun t => c (γ t)) s 1 ≠ 0 := fun h0 =>
    one_ne_zero (hh_inj (by rw [h0, map_zero]))
  obtain ⟨j, hj⟩ : ∃ j : Fin n, (fderiv ℝ (fun t => c (γ t)) s 1) j ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact hne (PiLp.ext hcon)
  let u : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := EuclideanSpace.proj (𝕜 := ℝ) j
  have hu_apply : ∀ y : EuclideanSpace ℝ (Fin n), u y = y j := fun y => by
    simp [u, PiLp.proj_apply]
  have hG_smooth : ContDiffOn ℝ smoothOrder (fun t => u (c (γ t))) (γ ⁻¹' c.source) :=
    u.contDiff.comp_contDiffOn hh_smooth
  have hG_fderiv : fderiv ℝ (fun t => u (c (γ t))) s =
      u ∘L fderiv ℝ (fun t => c (γ t)) s := by
    have hhat : HasFDerivAt (fun t => c (γ t)) (fderiv ℝ (fun t => c (γ t)) s) s :=
      (hh_smooth.contDiffAt (hI.mem_nhds hsI)).differentiableAt (by simp) |>.hasFDerivAt
    exact (u.hasFDerivAt.comp s hhat).fderiv
  have hG_inj : Function.Injective (fderiv ℝ (fun t => u (c (γ t))) s) := by
    rw [hG_fderiv]
    have hU1 : (u ∘L fderiv ℝ (fun t => c (γ t)) s) 1 ≠ 0 := by
      simpa [hu_apply] using hj
    intro x y hxy
    have h2 : (u ∘L fderiv ℝ (fun t => c (γ t)) s) (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have h1 : (x - y) • ((u ∘L fderiv ℝ (fun t => c (γ t)) s) 1) = 0 := by
      calc (x - y) • ((u ∘L fderiv ℝ (fun t => c (γ t)) s) 1)
          = (u ∘L fderiv ℝ (fun t => c (γ t)) s) ((x - y) • (1 : ℝ)) :=
            (ContinuousLinearMap.map_smul _ _ _).symm
        _ = (u ∘L fderiv ℝ (fun t => c (γ t)) s) (x - y) := by rw [smul_eq_mul, mul_one]
        _ = 0 := h2
    rcases smul_eq_zero.mp h1 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hU1
  obtain ⟨L, O, W, hOo, hOs, hWo, hsW, hWV, hLGs, hLsmooth, hLO, hLG, huniq⟩ :=
    Work.Whitney.exists_localInverse_smooth_on (fun t => u (c (γ t))) (γ ⁻¹' c.source) hI s
      hsI hG_smooth hG_inj
  have hGcont : ContinuousAt (fun t => u (c (γ t))) s :=
    (hG_smooth.contDiffAt (hI.mem_nhds hsI)).continuousAt
  obtain ⟨J₁, hJ₁sub, hJ₁open, hsJ₁⟩ :=
    mem_nhds_iff.mp (hGcont.preimage_mem_nhds (hOo.mem_nhds hOs))
  set J : Set ℝ := W ∩ J₁ with hJ_def
  have hJopen : IsOpen J := hWo.inter hJ₁open
  have hsJ : s ∈ J := ⟨hsW, hsJ₁⟩
  have hKc : IsCompact (Set.Icc a b \ J) := isCompact_Icc.inter_right hJopen.isClosed_compl
  have hγs : γ s ∉ γ '' (Set.Icc a b \ J) := by
    rintro ⟨t, ht, hts⟩
    have ht_eq : t = s := hγinj ht.1 hs hts
    exact ht.2 (ht_eq ▸ hsJ)
  let U : Set M := (γ '' (Set.Icc a b \ J))ᶜ ∩ (c.source ∩ (fun x => u (c x)) ⁻¹' O)
  have hUo : IsOpen U := by
    refine ((hKc.image hγ.continuous).isClosed.isOpen_compl).inter ?_
    exact (u.continuous.comp_continuousOn c.continuousOn).isOpen_inter_preimage c.open_source hOo
  have hγsU : γ s ∈ U := ⟨hγs, hmem, hOs⟩
  refine ⟨U, fun x => L (u (c x)), hUo, hγsU, ?_, ?_⟩
  · have hcU : ContMDiffOn (MC n) (MC n) smoothOrder (c : M → EuclideanSpace ℝ (Fin n)) U :=
      (contMDiffOn_of_mem_maximalAtlas hc).mono (fun x hx => hx.2.1)
    have hucU : ContMDiffOn (MC n) MCreal smoothOrder (fun x => u (c x)) U :=
      u.contMDiff.comp_contMDiffOn hcU
    exact hLsmooth.contMDiffOn.comp hucU (fun x hx => hx.2.2)
  · intro t ht htU
    have htJ : t ∈ J := by
      by_contra htJ'
      exact htU.1 ⟨t, ⟨ht, htJ'⟩, rfl⟩
    have hGtO : u (c (γ t)) ∈ O := hJ₁sub htJ.2
    have hz : t = L (u (c (γ t))) := huniq (u (c (γ t))) hGtO t htJ.1 rfl
    exact hz.symm

set_option maxHeartbeats 800000 in
/-- **A height function on an interval** (hypothesis restricted to the interval). -/
theorem arc_height_on_Icc' {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (MC n) smoothOrder M] [T2Space M]
    {γ : ℝ → M} (hγ : ContMDiff MCreal (MC n) smoothOrder γ) {a b : ℝ}
    (himm : ∀ t : ℝ, t ∈ Set.Icc a b → Function.Injective (mfderiv MCreal (MC n) γ t))
    (hab : a ≤ b) (hγinj : Set.InjOn γ (Set.Icc a b)) :
    ∃ g : M → ℝ, ContMDiff (MC n) MCreal smoothOrder g ∧
      ∀ t : ℝ, t ∈ Set.Icc a b → g (γ t) = t := by
  classical
  have _hab := hab
  have hexA : ∀ y : M, y ∈ (γ '' Set.Icc a b) → ∃ s : ℝ, s ∈ Set.Icc a b ∧ γ s = y := by
    rintro y ⟨s, hs, rfl⟩
    exact ⟨s, hs, rfl⟩
  let p : M → ℝ := fun y => if h : ∃ s : ℝ, s ∈ Set.Icc a b ∧ γ s = y then h.choose else 0
  have hp_mem : ∀ y (h : ∃ s : ℝ, s ∈ Set.Icc a b ∧ γ s = y), p y ∈ Set.Icc a b := by
    intro y h
    have hp : p y = h.choose := dif_pos h
    rw [hp]
    exact h.choose_spec.1
  have hp_val : ∀ y (h : ∃ s : ℝ, s ∈ Set.Icc a b ∧ γ s = y), γ (p y) = y := by
    intro y h
    have hp : p y = h.choose := dif_pos h
    rw [hp]
    exact h.choose_spec.2
  have hpA : ∀ y ∈ (γ '' Set.Icc a b), p y ∈ Set.Icc a b ∧ γ (p y) = y :=
    fun y hy => ⟨hp_mem y (hexA y hy), hp_val y (hexA y hy)⟩
  have hφ : ∀ s : ℝ, s ∈ Set.Icc a b → p (γ s) = s := by
    intro s hs
    have hex : ∃ s' : ℝ, s' ∈ Set.Icc a b ∧ γ s' = γ s := ⟨s, hs, rfl⟩
    exact hγinj (hp_mem (γ s) hex) hs (hp_val (γ s) hex)
  have hloc : ∀ x : γ '' Set.Icc a b,
      ∃ (U : Set M) (F : M → ℝ), IsOpen U ∧ (x : M) ∈ U ∧
        ContMDiffOn (MC n) MCreal smoothOrder F U ∧
        ∀ y : M, y ∈ (γ '' Set.Icc a b) → y ∈ U → F y = p y := by
    intro x
    obtain ⟨hxK, hxv⟩ := hpA (x : M) x.2
    obtain ⟨U, F, hUo, hxU, hFs, hUF⟩ := exists_local_left_inverse_on_Icc' hγ himm hγinj hxK
    refine ⟨U, F, hUo, ?_, hFs, ?_⟩
    · rw [← hxv]
      exact hxU
    · intro y hyA hyU
      obtain ⟨hyK, hyv⟩ := hpA y hyA
      have h1 : F (γ (p y)) = p y := hUF (p y) hyK (by rw [hyv]; exact hyU)
      rwa [hyv] at h1
  choose Uloc Floc hUloc_o hUloc_x hUloc_sm hUloc_prop using hloc
  let U' : M → Set M := fun x => if h : x ∈ (γ '' Set.Icc a b) then Uloc ⟨x, h⟩ else Set.univ
  let F' : M → M → ℝ := fun x => if h : x ∈ (γ '' Set.Icc a b) then Floc ⟨x, h⟩ else 0
  have hU'o : ∀ x, IsOpen (U' x) := by
    intro x
    by_cases h : x ∈ (γ '' Set.Icc a b)
    · have hx : U' x = Uloc ⟨x, h⟩ := dif_pos h
      rw [hx]
      exact hUloc_o ⟨x, h⟩
    · have hx : U' x = Set.univ := dif_neg h
      rw [hx]
      exact isOpen_univ
  have hU'A : ∀ x ∈ (γ '' Set.Icc a b), x ∈ U' x := by
    intro x hx
    have h : U' x = Uloc ⟨x, hx⟩ := dif_pos hx
    rw [h]
    exact hUloc_x ⟨x, hx⟩
  have hF'md : ∀ x, ContMDiffOn (MC n) MCreal smoothOrder (F' x) (U' x) := by
    intro x
    by_cases h : x ∈ (γ '' Set.Icc a b)
    · have h1 : F' x = Floc ⟨x, h⟩ := dif_pos h
      have h2 : U' x = Uloc ⟨x, h⟩ := dif_pos h
      rw [h1, h2]
      exact hUloc_sm ⟨x, h⟩
    · have h1 : F' x = 0 := dif_neg h
      have h2 : U' x = Set.univ := dif_neg h
      rw [h1, h2]
      exact contMDiffOn_const
  have hUF' : ∀ x y, x ∈ (γ '' Set.Icc a b) → y ∈ (γ '' Set.Icc a b) → y ∈ U' x →
      F' x y = p y := by
    intro x y hxA hyA hyU
    have h1 : F' x = Floc ⟨x, hxA⟩ := dif_pos hxA
    have h2 : U' x = Uloc ⟨x, hxA⟩ := dif_pos hxA
    rw [h1]
    exact hUloc_prop ⟨x, hxA⟩ y hyA (by rwa [h2] at hyU)
  obtain ⟨g, hg_sm, hg_val⟩ :=
    Work.Noncompact.Routing.exists_contMDiff_eqOn_of_isCompact_of_local (isCompact_Icc.image hγ.continuous) U' hU'o
      hU'A F' hF'md hUF'
  exact ⟨g, hg_sm, fun t ht => by
    have h1 : g (γ t) = p (γ t) := hg_val (γ t) ⟨t, ht, rfl⟩
    rwa [hφ t ht] at h1⟩

end HeightOnInterval

set_option maxHeartbeats 800000 in
/-- **An immersed arc injective on `[0,1]` is injective on a window around `[0,1]`.** -/
theorem injOn_window_of_immersion {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (MC n) smoothOrder M] [T2Space M]
    {γ : ℝ → M} (hγ : ContMDiff MCreal (MC n) smoothOrder γ)
    (himm : ∀ t ∈ Set.Icc (0:ℝ) 1, Function.Injective (mfderiv MCreal (MC n) γ t))
    (hinj : Set.InjOn γ (Set.Icc (0:ℝ) 1)) :
    ∃ δ : ℝ, 0 < δ ∧ Set.InjOn γ (Set.Icc (-δ) (1 + δ)) := by
  classical
  obtain ⟨g, hgsm, hg0⟩ :=
    arc_height_on_Icc' (n := n) (a := 0) (b := 1) (γ := γ) hγ himm (by norm_num) hinj
  obtain ⟨ρ₀, hρ₀pos, hρ₀⟩ :=
    injOn_Ioo_of_injective_mfderiv hγ 0 (himm 0 ⟨le_refl 0, by norm_num⟩)
  obtain ⟨ρ₁, hρ₁pos, hρ₁⟩ :=
    injOn_Ioo_of_injective_mfderiv hγ 1 (himm 1 ⟨by norm_num, le_refl 1⟩)
  have hφc : Continuous (fun t : ℝ => g (γ t)) := hgsm.continuous.comp hγ.continuous
  have hg00 : g (γ 0) = 0 := hg0 0 ⟨le_refl 0, by norm_num⟩
  have hg11 : g (γ 1) = 1 := hg0 1 ⟨by norm_num, le_refl 1⟩
  set η : ℝ := min (min ρ₀ ρ₁) (1 / 2) / 2 with hηdef
  have hηpos : 0 < η := by
    rw [hηdef]; exact half_pos (lt_min (lt_min hρ₀pos hρ₁pos) (by norm_num))
  have hηρ₀ : η < ρ₀ := by
    rw [hηdef]
    have h1 : min (min ρ₀ ρ₁) (1 / 2) ≤ min ρ₀ ρ₁ := min_le_left _ _
    have h2 : min ρ₀ ρ₁ ≤ ρ₀ := min_le_left _ _
    linarith
  have hηρ₁ : η < ρ₁ := by
    rw [hηdef]
    have h1 : min (min ρ₀ ρ₁) (1 / 2) ≤ min ρ₀ ρ₁ := min_le_left _ _
    have h2 : min ρ₀ ρ₁ ≤ ρ₁ := min_le_right _ _
    linarith
  have hηquarter : η ≤ 1 / 4 := by
    rw [hηdef]
    have h1 : min (min ρ₀ ρ₁) (1 / 2) ≤ 1 / 2 := min_le_right _ _
    linarith
  obtain ⟨c₀, hc₀pos, hc₀⟩ := Metric.mem_nhds_iff.mp
    (hφc.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds (g (γ 0)) hηpos))
  obtain ⟨c₁, hc₁pos, hc₁⟩ := Metric.mem_nhds_iff.mp
    (hφc.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds (g (γ 1)) hηpos))
  have hcb₀ : ∀ s : ℝ, |s| < c₀ → |g (γ s)| < η := by
    intro s hs
    have h1 : dist (g (γ s)) (g (γ 0)) < η :=
      hc₀ (by rw [Metric.mem_ball, Real.dist_eq, sub_zero]; exact hs)
    rwa [Real.dist_eq, hg00, sub_zero] at h1
  have hcb₁ : ∀ s : ℝ, |s - 1| < c₁ → |g (γ s) - 1| < η := by
    intro s hs
    have h1 : dist (g (γ s)) (g (γ 1)) < η :=
      hc₁ (by rw [Metric.mem_ball, Real.dist_eq]; exact hs)
    rwa [Real.dist_eq, hg11] at h1
  set δ : ℝ := min (min c₀ c₁) (min ρ₀ ρ₁) / 2 with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]; exact half_pos (lt_min (lt_min hc₀pos hc₁pos) (lt_min hρ₀pos hρ₁pos))
  have hδc₀ : δ < c₀ := by
    rw [hδdef]
    have h1 : min (min c₀ c₁) (min ρ₀ ρ₁) ≤ min c₀ c₁ := min_le_left _ _
    have h2 : min c₀ c₁ ≤ c₀ := min_le_left _ _
    linarith
  have hδc₁ : δ < c₁ := by
    rw [hδdef]
    have h1 : min (min c₀ c₁) (min ρ₀ ρ₁) ≤ min c₀ c₁ := min_le_left _ _
    have h2 : min c₀ c₁ ≤ c₁ := min_le_right _ _
    linarith
  have hδρ₀ : δ < ρ₀ := by
    rw [hδdef]
    have h1 : min (min c₀ c₁) (min ρ₀ ρ₁) ≤ min ρ₀ ρ₁ := min_le_right _ _
    have h2 : min ρ₀ ρ₁ ≤ ρ₀ := min_le_left _ _
    linarith
  have hδρ₁ : δ < ρ₁ := by
    rw [hδdef]
    have h1 : min (min c₀ c₁) (min ρ₀ ρ₁) ≤ min ρ₀ ρ₁ := min_le_right _ _
    have h2 : min ρ₀ ρ₁ ≤ ρ₁ := min_le_right _ _
    linarith
  refine ⟨δ, hδpos, ?_⟩
  have key : ∀ a b : ℝ, a ≤ b → a ∈ Set.Icc (-δ) (1 + δ) → b ∈ Set.Icc (-δ) (1 + δ) →
      γ a = γ b → a = b := by
    intro a b hab ha hb hab'
    rw [Set.mem_Icc] at ha hb
    have hgt : g (γ a) = g (γ b) := by rw [hab']
    rcases lt_or_ge a 0 with ha0 | ha0
    · rcases lt_or_ge b 0 with hb0 | hb0
      · exact hρ₀ ⟨by linarith [ha.1, hδρ₀], by linarith [ha0, hρ₀pos]⟩
          ⟨by linarith [hb.1, hδρ₀], by linarith [hb0, hρ₀pos]⟩ hab'
      · rcases le_or_gt b 1 with hb1 | hb1
        · have hgb : g (γ b) = b := hg0 b ⟨hb0, hb1⟩
          have haη : |g (γ a)| < η :=
            hcb₀ a (by rw [abs_lt]; constructor <;> linarith [ha.1, ha.2, hδc₀])
          have hbη : |b| < η := by rw [← hgb, ← hgt]; exact haη
          exact hρ₀ ⟨by linarith [ha.1, hδρ₀], by linarith [ha0, hρ₀pos]⟩
            ⟨by linarith [(abs_lt.mp hbη).1, hηρ₀], by linarith [(abs_lt.mp hbη).2, hηρ₀]⟩ hab'
        · have haη : |g (γ a)| < η :=
            hcb₀ a (by rw [abs_lt]; constructor <;> linarith [ha.1, ha.2, hδc₀])
          have hbη : |g (γ b) - 1| < η :=
            hcb₁ b (by rw [abs_lt]; constructor <;> linarith [hb1, hb.2, hδc₁])
          have h1 : |g (γ a)| ≤ 1 / 4 := le_of_lt (lt_of_lt_of_le haη hηquarter)
          have h2 : 3 / 4 ≤ |g (γ b)| := by
            have h3 : 1 - η < g (γ b) := by linarith [(abs_lt.mp hbη).1]
            have h4 : 0 < g (γ b) := by linarith [h3, hηquarter]
            rw [abs_of_pos h4]
            linarith [h3, hηquarter]
          rw [hgt] at h1
          linarith
    · rcases le_or_gt b 1 with hb1 | hb1
      · exact hinj ⟨ha0, by linarith⟩ ⟨by linarith, hb1⟩ hab'
      · rcases le_or_gt a 1 with ha1 | ha1
        · have hga : g (γ a) = a := hg0 a ⟨ha0, ha1⟩
          have hbη : |g (γ b) - 1| < η :=
            hcb₁ b (by rw [abs_lt]; constructor <;> linarith [hb1, hb.2, hδc₁])
          have haη : |a - 1| < η := by rw [← hga, hgt]; exact hbη
          exact hρ₁ ⟨by linarith [(abs_lt.mp haη).1, hηρ₁], by linarith [(abs_lt.mp haη).2, hηρ₁]⟩
            ⟨by linarith [hb1], by linarith [hb.2, hδρ₁]⟩ hab'
        · exact hρ₁ ⟨by linarith [ha1], by linarith [ha.2, hδρ₁]⟩
            ⟨by linarith [hb1], by linarith [hb.2, hδρ₁]⟩ hab'
  intro a ha b hb hab'
  rw [Set.mem_Icc] at ha hb
  rcases le_total a b with hle | hle
  · exact key a b hle ha hb hab'
  · exact (key b a hle hb ha hab'.symm).symm


set_option maxHeartbeats 1600000 in
/-- **The tube chart along an arc, with the coordinates on the arc.**  Same construction as
`Work.Noncompact.Routing.arc_tube_chart_assembly`, but recording that the chart sends `γ t` to
`(0, t)` on `[0,1]`. -/
theorem exists_tubeChart_with_axis {n : ℕ} (hn : 1 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (MC n) smoothOrder M] [T2Space M]
    {γ : ℝ → M} (hγ : ContMDiff MCreal (MC n) smoothOrder γ)
    {g : M → ℝ} {P : M → EuclideanSpace ℝ (Fin (n - 1))}
    (hg : ContMDiff (MC n) MCreal smoothOrder g)
    (hP : ContMDiff (MC n) (MC (n - 1)) smoothOrder P)
    {a b : ℝ} (ha : a < 0) (hb : 1 < b)
    (hcore : ∀ t ∈ Set.Icc (0 : ℝ) 1, P (γ t) = 0 ∧ g (γ t) = t)
    {U : Set M} (hU : IsOpen U)
    (hloc : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ∃ (r ε : ℝ) (σ : CollarParam n → M),
        0 < r ∧ 0 < ε ∧ ε ≤ s - a ∧ ε ≤ b - s ∧
        ContMDiffOn (MCprod n) (MC n) smoothOrder σ
          {p : CollarParam n | ‖p.1‖ < r ∧ |p.2 - s| < ε} ∧
        (∀ t : ℝ, |t - s| < ε → σ ((0 : EuclideanSpace ℝ (Fin (n - 1))), t) = γ t) ∧
        (∀ p : CollarParam n, ‖p.1‖ < r → |p.2 - s| < ε → (P (σ p), g (σ p)) = p) ∧
        (∀ p : CollarParam n, ‖p.1‖ < r → |p.2 - s| < ε → σ p ∈ U)) :
    ∃ e : OpenPartialHomeomorph M (CollarParam n),
      ContMDiffOn (MC n) (MCprod n) smoothOrder (e : M → CollarParam n) e.source ∧
      ContMDiffOn (MCprod n) (MC n) smoothOrder (e.symm : CollarParam n → M) e.target ∧
      γ '' Set.Icc (0 : ℝ) 1 ⊆ e.source ∧ e.source ⊆ U ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, e (γ t) = ((0 : EuclideanSpace ℝ (Fin (n - 1))), t)) := by
  classical
  have hn0 : smoothOrder ≠ (0 : WithTop ℕ∞) := by simp [smoothOrder]
  -- the pair map
  set F : M → CollarParam n := fun x => (P x, g x) with hFdef
  have hFsm : ContMDiff (MC n) (MCprod n) smoothOrder F := by
    rw [hFdef, prodModel_eq_self (n := n)]
    exact (contMDiff_prod_module_iff (I := MC n) F).2 ⟨hP, hg⟩
  -- the local slab data
  have hdata : ∀ s : {s : ℝ // s ∈ Set.Icc (0 : ℝ) 1},
      ∃ (r ε : ℝ) (σ : CollarParam n → M),
        0 < r ∧ 0 < ε ∧ ε ≤ s.1 - a ∧ ε ≤ b - s.1 ∧
        ContMDiffOn (MCprod n) (MC n) smoothOrder σ
          {p : CollarParam n | ‖p.1‖ < r ∧ |p.2 - s.1| < ε} ∧
        (∀ t : ℝ, |t - s.1| < ε → σ ((0 : EuclideanSpace ℝ (Fin (n - 1))), t) = γ t) ∧
        (∀ p : CollarParam n, ‖p.1‖ < r → |p.2 - s.1| < ε → F (σ p) = p) ∧
        (∀ p : CollarParam n, ‖p.1‖ < r → |p.2 - s.1| < ε → σ p ∈ U) := by
    intro s
    obtain ⟨r, ε, σ, hr, hε, hεa, hεb, hsm, hcore', hsect, hU'⟩ := hloc s.1 s.2
    exact ⟨r, ε, σ, hr, hε, hεa, hεb, hsm, hcore', fun p hp1 hp2 => by
      simpa only [hFdef] using hsect p hp1 hp2, hU'⟩
  choose r ε σ hr hε hεa hεb hσsm hσcore hσsect hσU using hdata
  -- the slabs
  let slab : {s : ℝ // s ∈ Set.Icc (0 : ℝ) 1} → Set (CollarParam n) :=
    fun s => {p : CollarParam n | ‖p.1‖ < r s ∧ |p.2 - s.1| < ε s}
  have hslab_open : ∀ s : {s : ℝ // s ∈ Set.Icc (0 : ℝ) 1}, IsOpen (slab s) := by
    intro s
    exact isOpen_lt continuous_fst.norm continuous_const |>.inter
      (isOpen_lt (continuous_snd.sub continuous_const).abs continuous_const)
  -- the union of the slabs
  let U₀ : Set (CollarParam n) := ⋃ s, slab s
  have hU₀open : IsOpen U₀ := isOpen_iUnion hslab_open
  -- the glued section
  let sIdx : CollarParam n → {s : ℝ // s ∈ Set.Icc (0 : ℝ) 1} :=
    fun p => if hp : p ∈ U₀ then Classical.choose (Set.mem_iUnion.mp hp) else ⟨0, by norm_num⟩
  let Ψ₀ : CollarParam n → M :=
    fun p => if hp : p ∈ U₀ then σ (Classical.choose (Set.mem_iUnion.mp hp)) p else γ 0
  have hsIdx : ∀ (p : CollarParam n) (hp : p ∈ U₀), p ∈ slab (sIdx p) := by
    intro p hp
    have h1 : sIdx p = Classical.choose (Set.mem_iUnion.mp hp) := by
      simp only [sIdx]
      rw [dif_pos hp]
    rw [h1]
    exact Classical.choose_spec (Set.mem_iUnion.mp hp)
  have hagree : ∀ (s s' : {s : ℝ // s ∈ Set.Icc (0 : ℝ) 1}) (p : CollarParam n),
      p ∈ slab s → p ∈ slab s' → σ s p = σ s' p := by
    intro s s' p hp hp'
    by_cases hne : (slab s ∩ slab s').Nonempty
    · obtain ⟨q, hq⟩ := hne
      have hconv : Convex ℝ (slab s ∩ slab s') := by
        show Convex ℝ ({p : CollarParam n | ‖p.1‖ < r s ∧ |p.2 - s.1| < ε s} ∩
          {p : CollarParam n | ‖p.1‖ < r s' ∧ |p.2 - s'.1| < ε s'})
        exact convex_slab_inter
      have haxis : ((0 : EuclideanSpace ℝ (Fin (n - 1))), q.2) ∈ slab s ∩ slab s' := by
        refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
        · simpa using hr s
        · simpa using hq.1.2
        · simpa using hr s'
        · simpa using hq.2.2
      have heq : σ s ((0 : EuclideanSpace ℝ (Fin (n - 1))), q.2)
          = σ s' ((0 : EuclideanSpace ℝ (Fin (n - 1))), q.2) := by
        rw [hσcore s q.2 (by simpa using hq.1.2), hσcore s' q.2 (by simpa using hq.2.2)]
      exact sections_eqOn_of_convex hn hFsm (hslab_open s) (hslab_open s')
        (hσsm s) (hσsm s') (fun q hq => hσsect s q hq.1 hq.2) (fun q hq => hσsect s' q hq.1 hq.2)
        hconv haxis heq p ⟨hp, hp'⟩
    · exact absurd ⟨p, hp, hp'⟩ hne
  have hΨ₀val : ∀ (s : {s : ℝ // s ∈ Set.Icc (0 : ℝ) 1}) (p : CollarParam n),
      p ∈ slab s → Ψ₀ p = σ s p := by
    intro s p hp
    simp only [Ψ₀]
    rw [dif_pos (Set.mem_iUnion.mpr ⟨s, hp⟩)]
    exact (hagree s (Classical.choose (Set.mem_iUnion.mp (Set.mem_iUnion.mpr ⟨s, hp⟩))) p hp
      (Classical.choose_spec (Set.mem_iUnion.mp (Set.mem_iUnion.mpr ⟨s, hp⟩)))).symm
  -- placeholder for the agreement of two sections
  -- smoothness of the glued section on the union
  have hΨ₀sm : ContMDiffOn (MCprod n) (MC n) smoothOrder Ψ₀ U₀ := by
    intro p hp
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hp
    have hcongr : ContMDiffOn (MCprod n) (MC n) smoothOrder Ψ₀ (U₀ ∩ slab s) :=
      ((hσsm s).mono inter_subset_right).congr (fun q hq => hΨ₀val s q hq.2)
    exact (hcongr.contMDiffAt ((hU₀open.inter (hslab_open s)).mem_nhds ⟨hp, hs⟩)).contMDiffWithinAt
  have hΨ₀sect : ∀ p ∈ U₀, F (Ψ₀ p) = p := by
    intro p hp
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hp
    rw [hΨ₀val s p hs]
    exact hσsect s p hs.1 hs.2
  have hΨ₀core : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Ψ₀ ((0 : EuclideanSpace ℝ (Fin (n - 1))), t) = γ t := by
    intro t ht
    have hmem : ((0 : EuclideanSpace ℝ (Fin (n - 1))), t) ∈ slab ⟨t, ht⟩ := by
      refine ⟨?_, ?_⟩
      · simpa using hr ⟨t, ht⟩
      · simpa using hε ⟨t, ht⟩
    rw [hΨ₀val ⟨t, ht⟩ _ hmem]
    exact hσcore ⟨t, ht⟩ t (by simpa using hε ⟨t, ht⟩)
  -- the compact core segment
  have hKsub : ((fun t : ℝ => ((0 : EuclideanSpace ℝ (Fin (n - 1))), t)) '' Set.Icc (0 : ℝ) 1)
      ⊆ U₀ := by
    rintro p ⟨t, ht, rfl⟩
    exact Set.mem_iUnion.mpr ⟨⟨t, ht⟩, by
      refine ⟨?_, ?_⟩
      · simpa using hr ⟨t, ht⟩
      · simpa using hε ⟨t, ht⟩⟩
  have hKcompact : IsCompact ((fun t : ℝ => ((0 : EuclideanSpace ℝ (Fin (n - 1))), t)) ''
      Set.Icc (0 : ℝ) 1) := isCompact_Icc.image (by fun_prop)
  obtain ⟨δ, hδpos, hδ⟩ :=
    IsCompact.exists_cthickening_subset_open hKcompact hU₀open hKsub
  -- the product slab inside the union
  set ρ : ℝ := δ / 3 with hρdef
  set a' : ℝ := -δ / 3 with ha'def
  set b' : ℝ := 1 + δ / 3 with hb'def
  have hρpos : 0 < ρ := by rw [hρdef]; linarith
  have ha'neg : a' < 0 := by rw [ha'def]; linarith
  have hb'one : 1 < b' := by rw [hb'def]; linarith
  set V : Set (CollarParam n) := {p : CollarParam n | ‖p.1‖ < ρ ∧ p.2 ∈ Set.Ioo a' b'} with hVdef
  have hVopen : IsOpen V := by
    rw [hVdef]
    exact isOpen_lt continuous_fst.norm continuous_const |>.inter
      (isOpen_Ioo.preimage continuous_snd)
  have hVsub : V ⊆ U₀ := by
    intro p hp
    rw [hVdef] at hp
    have h1 : ‖p.1‖ < δ / 3 := by
      rw [hρdef] at hp
      exact hp.1
    have h2 : p.2 ∈ Set.Ioo (-δ / 3) (1 + δ / 3) := by
      rw [ha'def, hb'def] at hp
      exact hp.2
    rw [Set.mem_Ioo] at h2
    have hKmem : ((0 : EuclideanSpace ℝ (Fin (n - 1))), max 0 (min p.2 1)) ∈
        ((fun t : ℝ => ((0 : EuclideanSpace ℝ (Fin (n - 1))), t)) '' Set.Icc (0 : ℝ) 1) :=
      ⟨max 0 (min p.2 1), ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩, rfl⟩
    have hle : |p.2 - max 0 (min p.2 1)| ≤ δ / 3 := by
      rcases le_total p.2 0 with h | h
      · rw [min_eq_left (by linarith), max_eq_left h, sub_zero, abs_of_nonpos h]
        linarith
      · rcases le_total p.2 1 with h1' | h1'
        · rw [min_eq_left h1', max_eq_right h, sub_self, abs_zero]
          linarith
        · rw [min_eq_right h1', max_eq_right (by norm_num), sub_eq_add_neg,
            abs_of_nonneg (by linarith)]
          linarith
    have hdist : dist p ((0 : EuclideanSpace ℝ (Fin (n - 1))), max 0 (min p.2 1)) ≤ δ := by
      rw [Prod.dist_eq, dist_zero_right, Real.dist_eq]
      calc max ‖p.1‖ |p.2 - max 0 (min p.2 1)| ≤ max (δ / 3) (δ / 3) :=
            max_le_max (le_of_lt h1) hle
        _ = δ / 3 := max_self _
        _ ≤ δ := by linarith
    refine hδ ?_
    rw [Metric.mem_cthickening_iff]
    calc Metric.infEDist p ((fun t : ℝ => ((0 : EuclideanSpace ℝ (Fin (n - 1))), t)) ''
          Set.Icc (0 : ℝ) 1)
        ≤ edist p ((0 : EuclideanSpace ℝ (Fin (n - 1))), max 0 (min p.2 1)) :=
          Metric.infEDist_le_edist_of_mem hKmem
      _ = ENNReal.ofReal (dist p ((0 : EuclideanSpace ℝ (Fin (n - 1))), max 0 (min p.2 1))) :=
          edist_dist _ _
      _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal hdist
  -- the image of `V` is open
  have himg_open : IsOpen (Ψ₀ '' V) := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨p, hpV, rfl⟩
    have hpU : p ∈ U₀ := hVsub hpV
    obtain ⟨s, hps⟩ := Set.mem_iUnion.mp hpU
    have hsurj : Function.Surjective (mfderiv (MC n) (MCprod n) F (Ψ₀ p)) := by
      have h := (injective_mfderiv_of_section hFsm (hslab_open s) (hσsm s)
        (fun q hq => hσsect s q hq.1 hq.2) hps).2
      rw [hΨ₀val s p hps]
      exact h
    obtain ⟨W, hWopen, hyW, hWinj⟩ := locally_injective_of_surjective_mfderiv hn hFsm hsurj
    have hFcont : ContinuousAt F (Ψ₀ p) := hFsm.continuous.continuousAt
    have hFpV : F (Ψ₀ p) ∈ V := by rw [hΨ₀sect p hpU]; exact hpV
    have hFmem : F ⁻¹' V ∈ 𝓝 (Ψ₀ p) :=
      hFcont.preimage_mem_nhds (hVopen.mem_nhds hFpV)
    have hFU : F (Ψ₀ p) ∈ U₀ := hVsub hFpV
    have hΨFcont : ContinuousAt (fun x => Ψ₀ (F x)) (Ψ₀ p) := by
      have hΨc : ContinuousAt Ψ₀ (F (Ψ₀ p)) :=
        (hΨ₀sm.contMDiffAt (hU₀open.mem_nhds hFU)).continuousAt
      exact hΨc.comp hFcont
    have hyW' : Ψ₀ (F (Ψ₀ p)) ∈ W := by rw [hΨ₀sect p hpU]; exact hyW
    have hmem : W ∩ F ⁻¹' V ∩ (fun x => Ψ₀ (F x)) ⁻¹' W ∈ 𝓝 (Ψ₀ p) :=
      Filter.inter_mem (Filter.inter_mem (hWopen.mem_nhds hyW) hFmem)
        (hΨFcont.preimage_mem_nhds (hWopen.mem_nhds hyW'))
    refine Filter.mem_of_superset hmem ?_
    rintro x ⟨⟨hxW, hxV⟩, hxW'⟩
    have h1 : F x = F (Ψ₀ (F x)) := by rw [hΨ₀sect (F x) (hVsub hxV)]
    exact ⟨F x, hxV, (hWinj hxW hxW' h1).symm⟩
  -- the tube chart
  refine ⟨{ toFun := F
            invFun := Ψ₀
            source := Ψ₀ '' V
            target := V
            map_source' := ?_
            map_target' := ?_
            left_inv' := ?_
            right_inv' := ?_
            open_source := himg_open
            open_target := hVopen
            continuousOn_toFun := hFsm.continuous.continuousOn
            continuousOn_invFun := (hΨ₀sm.mono hVsub).continuousOn },
    ?_, ?_, ?_, ?_, ?_⟩
  · rintro y ⟨p, hpV, rfl⟩
    rw [hΨ₀sect p (hVsub hpV)]
    exact hpV
  · intro p hp
    exact ⟨p, hp, rfl⟩
  · rintro y ⟨p, hpV, rfl⟩
    rw [hΨ₀sect p (hVsub hpV)]
  · intro p hp
    exact hΨ₀sect p (hVsub hp)
  · -- smoothness of the chart
    exact hFsm.contMDiffOn
  · -- smoothness of the inverse
    exact hΨ₀sm.mono hVsub
  · -- the arc lies in the source
    rintro y ⟨t, ht, rfl⟩
    refine ⟨((0 : EuclideanSpace ℝ (Fin (n - 1))), t), ?_, ?_⟩
    · refine ⟨by simpa using hρpos, ?_⟩
      rw [Set.mem_Ioo]
      exact ⟨by linarith [ha'neg, ht.1], by linarith [hb'one, ht.2]⟩
    · exact hΨ₀core t ht
  · -- the source is inside `U`
    rintro y ⟨p, hpV, rfl⟩
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp (hVsub hpV)
    rw [hΨ₀val s p hs]
    exact hσU s p hs.1 hs.2
  · -- the value of the chart on the axis
    intro t ht
    obtain ⟨hP0, hg0⟩ := hcore t ht
    show F (γ t) = ((0 : EuclideanSpace ℝ (Fin (n - 1))), t)
    rw [hFdef]
    exact Prod.ext hP0 hg0

/-- **The target lemma.**  A smooth curve which is an immersion at every point of `[0,1]` and
injective on `[0,1]` is straight on `[1-s,1]` in a chart of the maximal atlas. -/
theorem straightenedChartStretch {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M] [T2Space M] [SecondCountableTopology M]
    {α : ℝ → M} (hα : ContMDiff Work.Noncompact.CompressionTube.MCreal
      (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder α)
    (himm : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → Function.Injective (mfderiv
      Work.Noncompact.CompressionTube.MCreal
      (Work.Noncompact.CompressionTube.MC n) α t))
    (hinj : Set.InjOn α (Set.Icc (0:ℝ) 1)) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    ∃ (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (w : EuclideanSpace ℝ (Fin n)),
      w ≠ 0 ∧ c ∈ IsManifold.maximalAtlas (Work.Noncompact.CompressionTube.MC n)
        Work.Noncompact.CompressionTube.smoothOrder M ∧ α 1 ∈ c.source ∧
      (∀ t : ℝ, 1 - s ≤ t → t ≤ 1 →
        α t ∈ c.source ∧ c (α t) = c (α 1) + (t - 1) • w) := by
  classical
    have hn0' : smoothOrder ≠ (0 : WithTop ℕ∞) := by simp [smoothOrder]
    rcases eq_or_ne n 0 with hn0 | hn0
    · subst hn0
      exfalso
      have hsub : Subsingleton (TangentSpace (MC 0) (α 0)) :=
        ⟨fun a b => PiLp.ext (fun i => i.elim0)⟩
      haveI := hsub
      have h01 : (0:ℝ) = 1 := by
        have h : mfderiv MCreal (MC 0) α 0 (0:ℝ) = mfderiv MCreal (MC 0) α 0 (1:ℝ) :=
          Subsingleton.elim _ _
        exact himm 0 ⟨le_refl 0, by norm_num⟩ h
      norm_num at h01
    have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn0
    -- windows
    obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := injective_mfderiv_on_window (n := n) (γ := α) hα himm
    obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := injOn_window_of_immersion (n := n) (γ := α) hα himm hinj
    set δ : ℝ := min δ₁ δ₂ with hδdef
    have hδpos : 0 < δ := lt_min hδ₁pos hδ₂pos
    have hδδ₁ : δ ≤ δ₁ := by rw [hδdef]; exact min_le_left _ _
    have hδδ₂ : δ ≤ δ₂ := by rw [hδdef]; exact min_le_right _ _
    have hδ₁' : ∀ t ∈ Set.Icc (-δ) (1 + δ), Function.Injective (mfderiv MCreal (MC n) α t) :=
      fun t ht => hδ₁ t ⟨by linarith [ht.1, hδδ₁], by linarith [ht.2, hδδ₁]⟩
    have hδ₂' : Set.InjOn α (Set.Icc (-δ) (1 + δ)) :=
      fun a ha b hb hab =>
        hδ₂ ⟨by linarith [ha.1, hδδ₂], by linarith [ha.2, hδδ₂]⟩
          ⟨by linarith [hb.1, hδδ₂], by linarith [hb.2, hδδ₂]⟩ hab
    -- the height on the window
    obtain ⟨g, hgsm, hg0⟩ := arc_height_on_Icc' (n := n) (a := -δ) (b := 1 + δ) (γ := α) hα hδ₁'
      (by linarith) hδ₂'
    -- the transverse coordinate
    have htrans_data : ∃ P : M → EuclideanSpace ℝ (Fin (n - 1)),
        ContMDiff (MC n) (MC (n - 1)) smoothOrder P ∧
        (∀ t ∈ Set.Icc (-(δ / 2)) (1 + δ / 2), P (α t) = 0) ∧
        (∀ t ∈ Set.Icc (-(δ / 2)) (1 + δ / 2), Transverse α g P t) := by
      rcases eq_or_ne n 1 with hn1' | hn1''
      · subst hn1'
        refine ⟨fun _ => 0, contMDiff_const, fun t _ => rfl, ?_⟩
        intro t ht v hv1 hv2
        have htwin : t ∈ Set.Icc (-δ) (1 + δ) :=
          ⟨by linarith [ht.1, hδpos], by linarith [ht.2, hδpos]⟩
        have hwin : ∀ u : ℝ, |u - t| < δ / 2 → g (α u) = u := by
          intro u hu
          exact hg0 u ⟨by linarith [(abs_lt.mp hu).1, ht.1], by linarith [(abs_lt.mp hu).2, ht.2]⟩
        let v₀ : EuclideanSpace ℝ (Fin 1) := v
        let u₀ : EuclideanSpace ℝ (Fin 1) := mfderiv MCreal (MC 1) α t (1:ℝ)
        let dgl : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ := mfderiv (MC 1) MCreal g (α t)
        have hvel : dgl u₀ = 1 := by
          have hev : (fun u : ℝ => g (α u)) =ᶠ[𝓝 t] id := by
            refine Filter.eventuallyEq_of_mem
              (Metric.ball_mem_nhds t (by linarith : (0:ℝ) < δ / 2)) ?_
            intro u hu
            rw [Metric.mem_ball, Real.dist_eq] at hu
            exact hwin u hu
          have hcomp : mfderiv MCreal MCreal (fun u : ℝ => g (α u)) t =
              (mfderiv (MC 1) MCreal g (α t)).comp (mfderiv MCreal (MC 1) α t) :=
            mfderiv_comp (I := MCreal) (I' := MC 1) (I'' := MCreal) (f := α) (g := g) t
              (hgsm.mdifferentiableAt hn0') (hα.mdifferentiableAt hn0')
          rw [hev.mfderiv_eq_v433, mfderiv_id] at hcomp
          have h := congrArg
            (fun (L : TangentSpace MCreal t →L[ℝ] TangentSpace MCreal t) => L 1) hcomp.symm
          simp only [ContinuousLinearMap.id_apply] at h
          exact h
        have hu0ne : u₀ ≠ 0 := by
          intro h0
          have h1 : dgl u₀ = 0 := by rw [h0]; exact map_zero dgl
          rw [hvel] at h1
          norm_num at h1
        have hv2' : dgl v = 0 := hv2
        have hc : u₀ 0 ≠ 0 := by
          intro h0
          refine hu0ne (PiLp.ext (fun i => ?_))
          have hi : i = 0 := Subsingleton.elim i 0
          subst hi
          simpa using h0
        have hspan : ∃ a : ℝ, v₀ = a • u₀ := by
          refine ⟨v₀ 0 / u₀ 0, ?_⟩
          refine PiLp.ext (fun i => ?_)
          have hi : i = 0 := Subsingleton.elim i 0
          subst hi
          simp [div_mul_cancel₀ _ hc]
        obtain ⟨a, ha⟩ := hspan
        have h3 : dgl (a • u₀) = 0 := by rw [← ha]; exact hv2'
        rw [map_smul, hvel] at h3
        have h4 : a = 0 := by simpa using h3
        rw [h4, zero_smul] at ha
        exact ha
      · exact Work.Noncompact.Routing.arc_transverse_local (n := n) (by omega) hα hgsm
          (a := -δ) (b := 1 + δ) (A := -(3 * δ / 4)) (B := 1 + 3 * δ / 4)
          (c := -(δ / 2)) (d := 1 + δ / 2)
          (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
          (fun t ht => hg0 t ht)
    obtain ⟨P, hPsm, hP0, hPT⟩ := htrans_data
    -- the local slabs
    have hloc : ∀ s ∈ Set.Icc (0:ℝ) 1, ∃ (r ε : ℝ) (σ : CollarParam n → M),
        0 < r ∧ 0 < ε ∧ ε ≤ s - (-δ) ∧ ε ≤ (1 + δ) - s ∧
        ContMDiffOn (MCprod n) (MC n) smoothOrder σ
          {p : CollarParam n | ‖p.1‖ < r ∧ |p.2 - s| < ε} ∧
        (∀ t : ℝ, |t - s| < ε → σ ((0 : EuclideanSpace ℝ (Fin (n - 1))), t) = α t) ∧
        (∀ p : CollarParam n, ‖p.1‖ < r → |p.2 - s| < ε → (P (σ p), g (σ p)) = p) ∧
        (∀ p : CollarParam n, ‖p.1‖ < r → |p.2 - s| < ε → σ p ∈ Set.univ) := by
      intro s hs
      have hswin : s ∈ Set.Icc (-(δ / 2)) (1 + δ / 2) :=
        ⟨by linarith [hs.1, hδpos], by linarith [hs.2, hδpos]⟩
      have hsbig : s ∈ Set.Icc (-δ) (1 + δ) :=
        ⟨by linarith [hs.1, hδpos], by linarith [hs.2, hδpos]⟩
      obtain ⟨r, ε, σ, hr, hε, hεη, hsm, hcore, hsect, hU⟩ :=
        Work.Noncompact.Routing.arc_local_section (n := n) hn1 (γ := α) hα hgsm hPsm
          (s := s) (η := δ / 4) (by linarith)
          (hP0 s hswin) (hg0 s hsbig)
          (fun t ht => hP0 t (by
            rw [abs_lt] at ht
            exact ⟨by linarith [ht.1, hs.1, hδpos], by linarith [ht.2, hs.2, hδpos]⟩))
          (fun t ht => hg0 t (by
            rw [abs_lt] at ht
            exact ⟨by linarith [ht.1, hs.1, hδpos], by linarith [ht.2, hs.2, hδpos]⟩))
          (hPT s hswin) isOpen_univ (Set.mem_univ _)
      exact ⟨r, ε, σ, hr, hε, by linarith [hεη, hδpos, hs.1],
        by linarith [hεη, hδpos, hs.2], hsm, hcore, hsect, fun p _ _ => Set.mem_univ _⟩
    -- the tube chart
    obtain ⟨e, he_sm, he_ssm, he_arc, he_sub, he_axis⟩ :=
      exists_tubeChart_with_axis (n := n) hn1 (γ := α) hα hgsm hPsm
        (a := -δ) (b := 1 + δ) (by linarith) (by linarith)
        (fun t ht => ⟨hP0 t ⟨by linarith [ht.1, hδpos], by linarith [ht.2, hδpos]⟩,
          hg0 t ⟨by linarith [ht.1, hδpos], by linarith [ht.2, hδpos]⟩⟩)
        isOpen_univ hloc
    -- the model chart
    have hfin : Module.finrank ℝ (CollarParam n) = Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
      show Module.finrank ℝ (EuclideanSpace ℝ (Fin (n - 1)) × ℝ) = _
      rw [Module.finrank_prod, finrank_euclideanSpace, finrank_euclideanSpace, Module.finrank_self,
        Fintype.card_fin, Fintype.card_fin]
      omega
    set L : CollarParam n ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
      ContinuousLinearEquiv.ofFinrankEq hfin with hLdef
    set w : EuclideanSpace ℝ (Fin n) := L ((0 : EuclideanSpace ℝ (Fin (n - 1))), 1) with hwdef
    have hbridge : MCprod n = modelWithCornersSelf ℝ (CollarParam n) :=
      (modelWithCornersSelf_prod (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin (n - 1))) (F := ℝ)).symm
    have hLsm : ContMDiff (MCprod n) (MC n) smoothOrder
        (L : CollarParam n → EuclideanSpace ℝ (Fin n)) := by
      rw [hbridge]
      exact (contMDiff_iff_contDiff (f := (L : CollarParam n → EuclideanSpace ℝ (Fin n)))).2
        L.contDiff
    have hLssm : ContMDiff (MC n) (MCprod n) smoothOrder
        ((L.symm) : EuclideanSpace ℝ (Fin n) → CollarParam n) := by
      rw [hbridge]
      exact (contMDiff_iff_contDiff (f := (L.symm : EuclideanSpace ℝ (Fin n) → CollarParam n))).2
        L.symm.contDiff
    set e' : OpenPartialHomeomorph (CollarParam n) (EuclideanSpace ℝ (Fin n)) :=
      (L : CollarParam n ≃ₜ EuclideanSpace ℝ (Fin n)).toOpenPartialHomeomorph with he'def
    have he'src : e'.source = univ := by
      rw [he'def]; exact Homeomorph.toOpenPartialHomeomorph_source _
    have he'tgt : e'.target = univ := by
      rw [he'def]; exact Homeomorph.toOpenPartialHomeomorph_target _
    have he'coe : (e' : CollarParam n → EuclideanSpace ℝ (Fin n))
        = (L : CollarParam n → EuclideanSpace ℝ (Fin n)) := by
      rw [he'def]; exact Homeomorph.toOpenPartialHomeomorph_apply _
    have he'scoe : (e'.symm : EuclideanSpace ℝ (Fin n) → CollarParam n)
        = (L.symm : EuclideanSpace ℝ (Fin n) → CollarParam n) := by
      rw [he'def]; exact Homeomorph.toOpenPartialHomeomorph_symm_apply _
    set c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) := e ≫ₕ e' with hcdef
    have hcsrc : c.source = e.source := by
      rw [hcdef, OpenPartialHomeomorph.trans_source, he'src, Set.preimage_univ, Set.inter_univ]
    have hcapp : (c : M → EuclideanSpace ℝ (Fin n)) = fun x => L (e x) := by
      funext x
      rw [hcdef, OpenPartialHomeomorph.trans_apply, he'coe]
    have hcsymm : (c.symm : EuclideanSpace ℝ (Fin n) → M) = fun y => e.symm (L.symm y) := by
      rw [hcdef, OpenPartialHomeomorph.coe_trans_symm, he'scoe]
      rfl
    have hcmem : c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M := by
      refine OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn c ?_ ?_
      · have h1 : ContMDiffOn (MC n) (MC n) smoothOrder
            ((L : CollarParam n → EuclideanSpace ℝ (Fin n)) ∘ (e : M → CollarParam n)) e.source :=
          hLsm.comp_contMDiffOn he_sm
        rw [hcapp, hcsrc]
        simpa only [Function.comp_def] using h1
      · have h2 : ContMDiffOn (MC n) (MC n) smoothOrder
            ((e.symm : CollarParam n → M) ∘ (L.symm : EuclideanSpace ℝ (Fin n) → CollarParam n))
            (L '' e.target) :=
          he_ssm.comp (hLssm.contMDiffOn.mono (Set.subset_univ _)) (fun y hy => by
            obtain ⟨z, hz, rfl⟩ := hy
            change L.symm (L z) ∈ e.target
            rw [ContinuousLinearEquiv.symm_apply_apply]
            exact hz)
        have htgt : c.target = L '' e.target := by
          rw [hcdef, OpenPartialHomeomorph.trans_target, he'tgt, Set.univ_inter, he'scoe]
          ext y
          constructor
          · intro hy
            exact ⟨L.symm y, hy, L.apply_symm_apply y⟩
          · rintro ⟨z, hz, rfl⟩
            have h1 : L.symm (L z) = z := L.symm_apply_apply z
            rw [Set.mem_preimage, h1]
            exact hz
        rw [hcsymm]
        rw [htgt]
        simpa only [Function.comp_def] using h2
    have hwne : w ≠ 0 := by
      rw [hwdef]
      intro h0
      have h1 : ((0 : EuclideanSpace ℝ (Fin (n - 1))), (1:ℝ)) = 0 :=
        L.injective (by rw [h0, map_zero])
      have h2 : (1:ℝ) = 0 := congrArg Prod.snd h1
      norm_num at h2
    have hc1 : α 1 ∈ c.source := by
      rw [hcsrc]
      exact he_arc ⟨1, ⟨by norm_num, le_refl 1⟩, rfl⟩
    refine ⟨c, w, hwne, hcmem, hc1, ?_⟩
    intro t ht1 ht2
    have ht01 : t ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, ht2⟩
    have hmem : α t ∈ c.source := by
      rw [hcsrc]
      exact he_arc ⟨t, ht01, rfl⟩
    refine ⟨hmem, ?_⟩
    have hct : c (α t) = t • w := by
      rw [congrFun hcapp (α t), he_axis t ht01, hwdef]
      have h2 : ((0 : EuclideanSpace ℝ (Fin (n - 1))), t)
          = t • ((0 : EuclideanSpace ℝ (Fin (n - 1))), (1:ℝ)) := by
        ext <;> simp
      rw [h2, map_smul]
    have hc1' : c (α 1) = w := by
      rw [congrFun hcapp (α 1), he_axis 1 ⟨by norm_num, le_refl 1⟩, hwdef]
    rw [hct, hc1']
    module

end Work.Routing
