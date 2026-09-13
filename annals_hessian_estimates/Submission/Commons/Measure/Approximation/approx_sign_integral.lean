import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Order.CompletePartialOrder

set_option linter.unusedVariables false

namespace Commons.Measure.Approximation

open MeasureTheory Metric Set Filter Function ContinuousLinearMap
open scoped Topology ENNReal RealInnerProductSpace InnerProductSpace Convolution

/-- A sequence of smooth bump functions on `EuclideanSpace ℝ (Fin n)`, centred at `0`, whose outer
radius is `1 / (k + 1)` and whose inner radius is `1 / (2 * (k + 1))`.  Hence the ratio
`rOut / rIn` is constantly `2` and the outer radius tends to `0`. -/
noncomputable def bumpSeq (n : ℕ) (k : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
  ⟨(1 / ((k : ℝ) + 1)) / 2, 1 / ((k : ℝ) + 1), by positivity, by
    have h : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    linarith⟩

/-- The topological support of a convolution `f ⋆ u` is contained in the sum of the topological
supports; consequently, if `support f ⊆ ball 0 a` (with `a` the outer radius of a bump function)
and `support u ⊆ closedBall 0 r`, then `tsupport (f ⋆ u) ⊆ closedBall 0 (a + r)`. -/
theorem tsupport_convolution_subset_closedBall {n : ℕ} {f u : EuclideanSpace ℝ (Fin n) → ℝ}
    {a r : ℝ} (hf : support f ⊆ ball 0 a) (hu : support u ⊆ closedBall 0 r) :
    tsupport (f ⋆[lsmul ℝ ℝ, volume] u) ⊆ closedBall 0 (a + r) := by
  refine (closure_minimal ?_ isClosed_closedBall)
  refine (support_convolution_subset (L := lsmul ℝ ℝ) (μ := volume)).trans ?_
  intro x hx
  rcases hx with ⟨p, hp, q, hq, rfl⟩
  have hp' := hf hp
  have hq' := hu hq
  simp only [mem_ball, dist_zero_right] at hp'
  simp only [mem_closedBall, dist_zero_right] at hq' ⊢
  exact le_of_lt (calc ‖p + q‖ ≤ ‖p‖ + ‖q‖ := norm_add_le _ _
    _ < a + r := add_lt_add_of_lt_of_le hp' hq')

open MeasureTheory Metric Set Filter Function in
open scoped Topology ENNReal RealInnerProductSpace InnerProductSpace Convolution in
/-- Given an integrable `g` on `EuclideanSpace ℝ (Fin n)` and `r > 0`, there is a sequence of
smooth functions `φ k`, supported in `closedBall 0 (r + 1/(k+1))` and bounded by `1` in absolute
value, such that `∫_{ball 0 r} φ k * g → ∫_{ball 0 r} |g|`.  In other words, the `φ k` approximate
the sign of `g` on the ball. -/
theorem approx_sign_integral {n : ℕ} {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : Integrable g volume)
    {r : ℝ} (hr : 0 < r) :
    ∃ φ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ,
      (∀ k, ContDiff ℝ (⊤ : ℕ∞) (φ k)) ∧
      (∀ k, tsupport (φ k) ⊆ Metric.closedBall 0 (r + 1 / (k + 1))) ∧
      (∀ k y, |φ k y| ≤ 1) ∧
      Tendsto (fun k => ∫ y in Metric.ball 0 r, φ k y * g y) atTop
        (𝓝 (∫ y in Metric.ball 0 r, |g y|)) := by
  -- A measurable representative `G` of `g` and the sign function `s` built from it.
  let G : EuclideanSpace ℝ (Fin n) → ℝ := hg.aemeasurable.mk
  have hG : Measurable G := hg.aemeasurable.measurable_mk
  have hGg : g =ᵐ[volume] G := hg.aemeasurable.ae_eq_mk
  let s : EuclideanSpace ℝ (Fin n) → ℝ := fun y => if 0 ≤ G y then 1 else -1
  have hs_meas : Measurable s := by
    refine Measurable.ite ?_ measurable_const measurable_const
    exact measurableSet_le measurable_const hG
  have hs_abs : ∀ y, |s y| ≤ 1 := by
    intro y; simp only [s]; split_ifs <;> norm_num
  have hs_mul : ∀ y, s y * G y = |G y| := by
    intro y; simp only [s]
    by_cases h : 0 ≤ G y
    · rw [if_pos h, one_mul, abs_of_nonneg h]
    · rw [if_neg h, neg_one_mul, abs_of_neg (lt_of_not_ge h)]
  -- `u` is the sign of `g` cut off outside `closedBall 0 r`.
  let u : EuclideanSpace ℝ (Fin n) → ℝ := (closedBall 0 r).indicator s
  have hu_meas : Measurable u := hs_meas.indicator measurableSet_closedBall
  have hu_abs : ∀ y, |u y| ≤ 1 := by
    intro y
    by_cases h : y ∈ closedBall 0 r
    · rw [show u y = s y from Set.indicator_of_mem h s]; exact hs_abs y
    · rw [show u y = 0 from Set.indicator_of_notMem h s]; norm_num
  have hu_supp : support u ⊆ closedBall 0 r := by
    intro y hy
    by_contra h
    exact hy (Set.indicator_of_notMem h s)
  have hu_locint : LocallyIntegrable u volume := by
    have hb : LocallyIntegrable
        ((closedBall 0 r).indicator (fun _ : EuclideanSpace ℝ (Fin n) => (1 : ℝ))) volume :=
      (locallyIntegrable_const (1 : ℝ)).indicator measurableSet_closedBall
    refine hb.mono hu_meas.aestronglyMeasurable ?_
    filter_upwards with y
    by_cases h : y ∈ closedBall 0 r
    · rw [show (closedBall 0 r).indicator
          (fun _ : EuclideanSpace ℝ (Fin n) => (1 : ℝ)) y = 1 from Set.indicator_of_mem h _]
      simp only [norm_one, Real.norm_eq_abs]
      exact hu_abs y
    · rw [show (closedBall 0 r).indicator
          (fun _ : EuclideanSpace ℝ (Fin n) => (1 : ℝ)) y = 0 from Set.indicator_of_notMem h _]
      rw [norm_zero, Real.norm_eq_abs]
      have : u y = 0 := Set.indicator_of_notMem h s
      rw [this, abs_zero]
  -- The approximating family: convolve `u` with the bump functions.
  let φ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun k => (bumpSeq n k).normed volume ⋆[lsmul ℝ ℝ, volume] u
  have hφ_tendsto : Tendsto (fun k => (bumpSeq n k).rOut) atTop (𝓝 0) := by
    have h : Tendsto (fun k : ℕ => (1 : ℝ) / (k + 1)) atTop (𝓝 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    exact h
  have hφ_ratio : ∀ᶠ k in atTop, (bumpSeq n k).rOut ≤ 2 * (bumpSeq n k).rIn := by
    filter_upwards with k
    have : 2 * (bumpSeq n k).rIn = (bumpSeq n k).rOut := by simp [bumpSeq]; ring
    exact this.ge
  have hcdiff : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (φ k) := by
    intro k
    exact (bumpSeq n k).hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
      ((bumpSeq n k).contDiff_normed (μ := volume) (n := ⊤)) hu_locint
  have hsupp : ∀ k, tsupport (φ k) ⊆ closedBall 0 (r + 1 / (k + 1)) := by
    intro k
    have h := tsupport_convolution_subset_closedBall (f := (bumpSeq n k).normed volume) (u := u)
        (le_of_eq (ContDiffBump.support_normed_eq (bumpSeq n k))) hu_supp
    change tsupport ((bumpSeq n k).normed volume ⋆[lsmul ℝ ℝ, volume] u)
      ⊆ closedBall 0 (r + 1 / (↑k + 1))
    rw [add_comm] at h
    exact h
  have habs : ∀ k y, |φ k y| ≤ 1 := by
    intro k y
    have hb := MeasureTheory.dist_convolution_le (μ := volume)
      (f := (bumpSeq n k).normed volume) (g := u) (x₀ := y) (R := (bumpSeq n k).rOut)
      (ε := 1) (z₀ := 0) zero_le_one
      (le_of_eq (ContDiffBump.support_normed_eq (bumpSeq n k)))
      (ContDiffBump.nonneg_normed (bumpSeq n k))
      (ContDiffBump.integral_normed (bumpSeq n k))
      hu_meas.aestronglyMeasurable
      (fun x _ => by rw [dist_zero_right, Real.norm_eq_abs]; exact hu_abs x)
    simpa only [dist_zero_right, Real.norm_eq_abs] using hb
  -- Almost everywhere convergence of the convolution to `u`.
  have hae : ∀ᵐ x ∂volume, Tendsto (fun k => φ k x) atTop (𝓝 (u x)) :=
    ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (μ := volume) (g := u) (K := 2)
      hφ_tendsto hφ_ratio hu_locint
  refine ⟨φ, hcdiff, hsupp, habs, ?_⟩
  -- On the ball, `u * g = |g|`; combined with the a.e. convergence this gives pointwise convergence
  -- of the integrands, and dominated convergence finishes.
  have h_lim : ∀ᵐ y ∂(volume.restrict (ball 0 r)),
      Tendsto (fun k => φ k y * g y) atTop (𝓝 (|g y|)) := by
    have h1 : ∀ᵐ y ∂(volume.restrict (ball 0 r)), Tendsto (fun k => φ k y) atTop (𝓝 (u y)) :=
      MeasureTheory.ae_restrict_of_ae hae
    have h2 : ∀ᵐ y ∂(volume.restrict (ball 0 r)), g y = G y :=
      MeasureTheory.ae_restrict_of_ae hGg
    have h3 : ∀ᵐ y ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin n)) r)),
        y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) r :=
      MeasureTheory.ae_restrict_mem (μ := volume) measurableSet_ball
    filter_upwards [h1, h2, h3] with y hy1 hy2 hyb
    have huy : u y = s y := by
      show (closedBall 0 r).indicator s y = s y
      exact Set.indicator_of_mem (ball_subset_closedBall hyb) s
    have hprod : u y * g y = |g y| := by
      rw [huy]
      calc s y * g y = s y * G y := by rw [hy2]
        _ = |G y| := hs_mul y
        _ = |g y| := by rw [hy2]
    rw [← hprod]
    exact hy1.mul_const (g y)
  have hbnd : ∀ k, ∀ᵐ y ∂(volume.restrict (ball 0 r)), ‖φ k y * g y‖ ≤ |g y| := by
    intro k
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (habs k y)
  have hmeas : ∀ k, AEStronglyMeasurable (fun y => φ k y * g y) (volume.restrict (ball 0 r)) := by
    intro k
    have hc : Continuous (φ k) := (hcdiff k).continuous
    exact (hc.aestronglyMeasurable (μ := volume.restrict (ball 0 r))).mul
      (hg.aestronglyMeasurable.mono_measure Measure.restrict_le_self)
  have hint : Integrable (fun y => |g y|) (volume.restrict (ball 0 r)) :=
    (hg.integrableOn (s := ball 0 r)).abs
  exact MeasureTheory.tendsto_integral_of_dominated_convergence (μ := volume.restrict (ball 0 r))
    (F := fun k y => φ k y * g y) (f := fun y => |g y|) (fun y => |g y|) hmeas hint hbnd h_lim

end Commons.Measure.Approximation