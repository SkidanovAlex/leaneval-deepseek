import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Order.CompletePartialOrder
import Submission.Commons.Measure.Approximation.approx_sign_integral

namespace Commons.Measure.Approximation

open MeasureTheory Metric Set Filter Function ContinuousLinearMap
open scoped Topology ENNReal RealInnerProductSpace InnerProductSpace Convolution

/-- Base radius `r / (k + 2)`, decreasing to `0`. -/
private noncomputable def bumpRadius (r : ℝ) (k : ℕ) : ℝ := r / ((k : ℝ) + 2)

private lemma bumpRadius_pos {r : ℝ} (hr : 0 < r) (k : ℕ) : 0 < bumpRadius r k :=
  div_pos hr (by positivity)

private lemma bumpRadius_half_lt {r : ℝ} (hr : 0 < r) (k : ℕ) :
    bumpRadius r k / 2 < bumpRadius r k := by
  have h := bumpRadius_pos hr k
  linarith

private lemma bumpRadius_tendsto {r : ℝ} :
    Tendsto (fun k : ℕ => bumpRadius r k) atTop (𝓝 0) := by
  have h1 : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have h2 : Tendsto (fun k : ℕ => (1 : ℝ) / (((k + 1 : ℕ) : ℝ) + 1)) atTop (𝓝 0) :=
    h1.comp (tendsto_add_atTop_nat 1)
  have h3 : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 2)) atTop (𝓝 0) := by
    have hEq : (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 2)) =
        fun k : ℕ => (1 : ℝ) / (((k + 1 : ℕ) : ℝ) + 1) := by
      funext k; push_cast; ring
    rw [hEq]; exact h2
  have h4 : Tendsto (fun k : ℕ => r * (1 / ((k : ℝ) + 2))) atTop (𝓝 (r * 0)) :=
    tendsto_const_nhds.mul h3
  rw [mul_zero] at h4
  simpa [bumpRadius, div_eq_mul_inv] using h4

/-- The smoothing bump centred at `0` used for the convolution. -/
private noncomputable def innerBump (n : ℕ) (r : ℝ) (hr : 0 < r) (k : ℕ) :
    ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
  ⟨bumpRadius r k / 2, bumpRadius r k, half_pos (bumpRadius_pos hr k), bumpRadius_half_lt hr k⟩

/-- The cutoff bump centred at `x₀`, equal to `1` near `x₀` and supported in `closedBall x₀ r`. -/
private noncomputable def cutoffBump (n : ℕ) (x₀ : EuclideanSpace ℝ (Fin n)) (r : ℝ)
    (hr : 0 < r) (k : ℕ) : ContDiffBump x₀ :=
  ⟨r * ((k : ℝ) + 1) / ((k : ℝ) + 2), r,
    div_pos (mul_pos hr (by positivity)) (by positivity),
    by
      have h : (0 : ℝ) < (k : ℝ) + 2 := by positivity
      rw [div_lt_iff₀ h]
      nlinarith [hr]⟩

open MeasureTheory Metric Set Filter Function ContinuousLinearMap in
open scoped Topology ENNReal RealInnerProductSpace InnerProductSpace Convolution in
theorem approx_sign_integral_ball {n : ℕ} (x₀ : EuclideanSpace ℝ (Fin n))
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : Integrable g volume) {r : ℝ} (hr : 0 < r) :
    ∃ φ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ,
      (∀ k, ContDiff ℝ (⊤ : ℕ∞) (φ k)) ∧
      (∀ k, tsupport (φ k) ⊆ Metric.closedBall x₀ r) ∧
      (∀ k y, |φ k y| ≤ 1) ∧
      Tendsto (fun k => ∫ y in Metric.ball x₀ r, φ k y * g y) atTop
        (𝓝 (∫ y in Metric.ball x₀ r, |g y|)) := by
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
  let u : EuclideanSpace ℝ (Fin n) → ℝ := (closedBall x₀ r).indicator s
  have hu_meas : Measurable u := hs_meas.indicator measurableSet_closedBall
  have hu_abs : ∀ y, |u y| ≤ 1 := by
    intro y
    by_cases h : y ∈ closedBall x₀ r
    · rw [show u y = s y from Set.indicator_of_mem h s]; exact hs_abs y
    · rw [show u y = 0 from Set.indicator_of_notMem h s]; norm_num
  have hu_locint : LocallyIntegrable u volume := by
    have hb : LocallyIntegrable
        ((closedBall x₀ r).indicator (fun _ : EuclideanSpace ℝ (Fin n) => (1 : ℝ))) volume :=
      (locallyIntegrable_const (1 : ℝ)).indicator measurableSet_closedBall
    refine hb.mono hu_meas.aestronglyMeasurable ?_
    filter_upwards with y
    by_cases h : y ∈ closedBall x₀ r
    · rw [show (closedBall x₀ r).indicator
          (fun _ : EuclideanSpace ℝ (Fin n) => (1 : ℝ)) y = 1 from Set.indicator_of_mem h _]
      simp only [norm_one, Real.norm_eq_abs]
      exact hu_abs y
    · rw [show (closedBall x₀ r).indicator
          (fun _ : EuclideanSpace ℝ (Fin n) => (1 : ℝ)) y = 0 from Set.indicator_of_notMem h _]
      rw [norm_zero, Real.norm_eq_abs]
      have : u y = 0 := Set.indicator_of_notMem h s
      rw [this, abs_zero]
  -- bump sequence and the convolution `ψ k`
  let β : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) := fun k => innerBump n r hr k
  let ψ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun k => (β k).normed volume ⋆[lsmul ℝ ℝ, volume] u
  have hβ_rOut : ∀ k, (β k).rOut = bumpRadius r k := fun k => rfl
  have hβ_rIn : ∀ k, (β k).rIn = bumpRadius r k / 2 := fun k => rfl
  have hψ_tendsto : Tendsto (fun k => (β k).rOut) atTop (𝓝 0) := by
    simpa only [hβ_rOut] using bumpRadius_tendsto (r := r)
  have hψ_ratio : ∀ᶠ k in atTop, (β k).rOut ≤ 2 * (β k).rIn := by
    filter_upwards with k
    rw [hβ_rOut, hβ_rIn]
    have hh : 2 * (bumpRadius r k / 2) = bumpRadius r k := by ring
    rw [hh]
  have hψ_cdiff : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (ψ k) := by
    intro k
    exact (β k).hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
      ((β k).contDiff_normed (μ := volume) (n := ⊤)) hu_locint
  have hψ_abs : ∀ k y, |ψ k y| ≤ 1 := by
    intro k y
    have hb := MeasureTheory.dist_convolution_le (μ := volume)
      (f := (β k).normed volume) (g := u) (x₀ := y) (R := (β k).rOut) (ε := 1) (z₀ := 0)
      zero_le_one (le_of_eq (ContDiffBump.support_normed_eq (β k)))
      (ContDiffBump.nonneg_normed (β k)) (ContDiffBump.integral_normed (β k))
      hu_meas.aestronglyMeasurable
      (fun x _ => by rw [dist_zero_right, Real.norm_eq_abs]; exact hu_abs x)
    simpa only [dist_zero_right, Real.norm_eq_abs] using hb
  have hψ_ae : ∀ᵐ x ∂volume, Tendsto (fun k => ψ k x) atTop (𝓝 (u x)) :=
    ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (μ := volume) (g := u) (K := 2)
      hψ_tendsto hψ_ratio hu_locint
  -- integrability data on the ball
  have hg_abs_int : Integrable (fun y => |g y|) (volume.restrict (ball x₀ r)) :=
    (hg.integrableOn (s := ball x₀ r)).abs
  have hψg_meas : ∀ k, AEStronglyMeasurable (fun y => ψ k y * g y)
      (volume.restrict (ball x₀ r)) := by
    intro k
    exact ((hψ_cdiff k).continuous.aestronglyMeasurable
        (μ := volume.restrict (ball x₀ r))).mul
      (hg.aestronglyMeasurable.mono_measure Measure.restrict_le_self)
  have hψg_bnd : ∀ k, ∀ᵐ y ∂(volume.restrict (ball x₀ r)), ‖ψ k y * g y‖ ≤ |g y| := by
    intro k
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (hψ_abs k y)
  have hψg_int : ∀ k, Integrable (fun y => ψ k y * g y) (volume.restrict (ball x₀ r)) :=
    fun k => hg_abs_int.mono' (hψg_meas k) (hψg_bnd k)
  -- integral convergence for `ψ`
  have hψ_int : Tendsto (fun k => ∫ y in Metric.ball x₀ r, ψ k y * g y) atTop
      (𝓝 (∫ y in Metric.ball x₀ r, |g y|)) := by
    have h_lim : ∀ᵐ y ∂(volume.restrict (ball x₀ r)),
        Tendsto (fun k => ψ k y * g y) atTop (𝓝 (|g y|)) := by
      have h1 : ∀ᵐ y ∂(volume.restrict (ball x₀ r)),
          Tendsto (fun k => ψ k y) atTop (𝓝 (u y)) :=
        MeasureTheory.ae_restrict_of_ae hψ_ae
      have h2 : ∀ᵐ y ∂(volume.restrict (ball x₀ r)), g y = G y :=
        MeasureTheory.ae_restrict_of_ae hGg
      have h3 : ∀ᵐ y ∂(volume.restrict (ball x₀ r)), y ∈ ball x₀ r :=
        MeasureTheory.ae_restrict_mem (μ := volume) measurableSet_ball
      filter_upwards [h1, h2, h3] with y hy1 hy2 hyb
      have huy : u y = s y := by
        show (closedBall x₀ r).indicator s y = s y
        exact Set.indicator_of_mem (ball_subset_closedBall hyb) s
      have hprod : u y * g y = |g y| := by
        rw [huy]
        calc s y * g y = s y * G y := by rw [hy2]
          _ = |G y| := hs_mul y
          _ = |g y| := by rw [hy2]
      rw [← hprod]
      exact hy1.mul_const (g y)
    exact MeasureTheory.tendsto_integral_of_dominated_convergence
      (μ := volume.restrict (ball x₀ r))
      (F := fun k y => ψ k y * g y) (f := fun y => |g y|) (fun y => |g y|)
      hψg_meas hg_abs_int hψg_bnd h_lim
  -- the cutoff family
  let γb : ℕ → ContDiffBump x₀ := fun k => cutoffBump n x₀ r hr k
  have hcut_rOut : ∀ k, (γb k).rOut = r := fun k => rfl
  have hcut_rIn : ∀ k, (γb k).rIn = r * ((k : ℝ) + 1) / ((k : ℝ) + 2) := fun k => rfl
  let φ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun k y => (γb k) y * ψ k y
  -- pointwise eventual statement for the cutoff
  have hcut_rIn_tendsto : Tendsto (fun k : ℕ => (γb k).rIn) atTop (𝓝 r) := by
    have hconst : Tendsto (fun _ : ℕ => r) atTop (𝓝 r) := tendsto_const_nhds
    have h := hconst.sub (bumpRadius_tendsto (r := r))
    rw [sub_zero] at h
    refine h.congr' ?_
    filter_upwards with k
    rw [hcut_rIn, bumpRadius]
    field_simp
    ring
  have hγev : ∀ᵐ y ∂(volume.restrict (ball x₀ r)), ∀ᶠ k in atTop, (γb k) y = 1 := by
    filter_upwards [MeasureTheory.ae_restrict_mem (μ := volume) measurableSet_ball] with y hy
    have hyd : dist y x₀ < r := by rwa [mem_ball] at hy
    have hev : ∀ᶠ k in atTop, dist y x₀ < (γb k).rIn :=
      (tendsto_order.1 hcut_rIn_tendsto).1 (dist y x₀) hyd
    filter_upwards [hev] with k hk
    exact ContDiffBump.one_of_mem_closedBall (f := γb k) (by rw [mem_closedBall]; exact le_of_lt hk)
  -- dominated convergence for the error term
  have hB_meas : ∀ k, AEStronglyMeasurable (fun y => (1 - (γb k) y) * (ψ k y * g y))
      (volume.restrict (ball x₀ r)) := by
    intro k
    exact (((continuous_const.sub (γb k).continuous).aestronglyMeasurable
        (μ := volume.restrict (ball x₀ r))).mul (hψg_meas k))
  have hB_bnd : ∀ k, ∀ᵐ y ∂(volume.restrict (ball x₀ r)),
      ‖(1 - (γb k) y) * (ψ k y * g y)‖ ≤ |g y| := by
    intro k
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_mul]
    have hγ1 : |1 - (γb k) y| ≤ 1 := by
      rw [abs_le]
      have hle : (γb k) y ≤ 1 := (γb k).le_one
      have hnn : 0 ≤ (γb k) y := (γb k).nonneg
      exact ⟨by linarith, by linarith⟩
    have hψg : |ψ k y * g y| ≤ |g y| := by
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (hψ_abs k y)
    calc |1 - (γb k) y| * |ψ k y * g y| ≤ 1 * |g y| :=
          mul_le_mul hγ1 hψg (abs_nonneg _) (by norm_num)
      _ = |g y| := one_mul _
  have hB_lim : ∀ᵐ y ∂(volume.restrict (ball x₀ r)),
      Tendsto (fun k => (1 - (γb k) y) * (ψ k y * g y)) atTop (𝓝 0) := by
    filter_upwards [hγev] with y hy
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hy] with k hk
    rw [hk]; ring
  have hB : Tendsto (fun k => ∫ y in Metric.ball x₀ r,
      (1 - (γb k) y) * (ψ k y * g y)) atTop (𝓝 0) := by
    have := MeasureTheory.tendsto_integral_of_dominated_convergence
      (μ := volume.restrict (ball x₀ r))
      (F := fun k y => (1 - (γb k) y) * (ψ k y * g y)) (f := fun _ => 0) (fun y => |g y|)
      hB_meas hg_abs_int hB_bnd hB_lim
    simpa using this
  -- exact value of the φ-integral
  have hφ_int_eq : ∀ k, ∫ y in Metric.ball x₀ r, φ k y * g y =
      (∫ y in Metric.ball x₀ r, ψ k y * g y) -
        ∫ y in Metric.ball x₀ r, (1 - (γb k) y) * (ψ k y * g y) := by
    intro k
    rw [← MeasureTheory.integral_sub (hψg_int k)
      (hg_abs_int.mono' (hB_meas k) (hB_bnd k))]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    show ((γb k) y * ψ k y) * g y = ψ k y * g y - (1 - (γb k) y) * (ψ k y * g y)
    ring
  -- main tendsto
  have hA_sub_B := hψ_int.sub hB
  rw [sub_zero] at hA_sub_B
  refine ⟨φ, ?_, ?_, ?_, ?_⟩
  · intro k
    exact (γb k).contDiff.mul (hψ_cdiff k)
  · intro k
    refine (tsupport_mul_subset_left (f := fun y => (γb k) y)
      (g := fun y => ψ k y)).trans ?_
    rw [ContDiffBump.tsupport_eq, hcut_rOut k]
  · intro k y
    rw [abs_mul]
    have hγ1 : |(γb k) y| ≤ 1 := by
      rw [abs_of_nonneg (γb k).nonneg]; exact (γb k).le_one
    have h := mul_le_mul hγ1 (hψ_abs k y) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    simpa using h
  · refine hA_sub_B.congr' ?_
    filter_upwards with k
    exact (hφ_int_eq k).symm

end Commons.Measure.Approximation