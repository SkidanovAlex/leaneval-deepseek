import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Order.CompletePartialOrder
import Submission.Commons.Measure.Integration.nonneg_integral_eq_lam

namespace Commons.Measure.Integration

open MeasureTheory Metric Set Filter Function in
open scoped ContDiff ENNReal Topology in
theorem integrable_nonneg_of_contDiff_tsupport_subset
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    [MeasurableSpace X] [BorelSpace X] {s : Set X} {Λ : (X → ℝ) → ℝ} {μ : Measure X}
    (hint : ∀ f : X → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ s → Integrable f μ)
    (hadd : ∀ φ ψ, ContDiff ℝ ∞ φ → tsupport φ ⊆ s → ContDiff ℝ ∞ ψ → tsupport ψ ⊆ s →
      Λ (φ + ψ) = Λ φ + Λ ψ)
    (hsmul : ∀ (a : ℝ) φ, ContDiff ℝ ∞ φ → tsupport φ ⊆ s → Λ (a • φ) = a * Λ φ)
    (hpos : ∀ φ, ContDiff ℝ ∞ φ → tsupport φ ⊆ s → 0 ≤ φ → 0 ≤ Λ φ)
    (hCc : ∀ f : X → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ s →
      ∫ x, f x ∂μ = Λ f)
    {Φ : X → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (hsub : tsupport Φ ⊆ s) (hΦ0 : 0 ≤ Φ) :
    Integrable Φ μ := by
  -- Monotonicity of `Λ` on admissible smooth functions.
  have Lam_mono : ∀ {f g : X → ℝ}, ContDiff ℝ ∞ f → tsupport f ⊆ s →
      ContDiff ℝ ∞ g → tsupport g ⊆ s → f ≤ g → Λ f ≤ Λ g := by
    intro f g hf hfs hg hgs hle
    have hdf : ContDiff ℝ ∞ (g - f) := hg.sub hf
    have hdfs : tsupport (g - f) ⊆ s := (tsupport_sub g f).trans (union_subset hgs hfs)
    have hnn : 0 ≤ g - f := fun x => sub_nonneg.mpr (hle x)
    have h0 : 0 ≤ Λ (g - f) := hpos _ hdf hdfs hnn
    have key : Λ g = Λ f + Λ (g - f) := by
      have h : f + (g - f) = g := by ext x; simp
      rw [← hadd f (g - f) hf hfs hdf hdfs, h]
    linarith
  -- Smooth compactly supported cutoffs that are `1` on balls around the origin.
  let χ : ℕ → ContDiffBump (0 : X) := fun n =>
    ⟨(n : ℝ) + 1, (n : ℝ) + 2, by positivity, by linarith⟩
  -- The functions compared against `Φ`.
  let f : ℕ → X → ℝ := fun n => (ball (0 : X) (n : ℝ)).indicator Φ
  let g : ℕ → X → ℝ := fun n => fun x => Φ x * (χ n) x
  have hgsmooth : ∀ n, ContDiff ℝ ∞ (g n) := by
    intro n
    dsimp only [g]
    exact hΦ.mul (χ n).contDiff
  have hgcompact : ∀ n, HasCompactSupport (g n) := by
    intro n
    dsimp only [g]
    exact (χ n).hasCompactSupport.mono'
      ((support_mul_subset_right Φ (χ n : X → ℝ)).trans subset_closure)
  have hgsupp : ∀ n, tsupport (g n) ⊆ s := by
    intro n
    dsimp only [g]
    exact (tsupport_mul_subset_left (f := Φ) (g := (χ n : X → ℝ))).trans hsub
  have hgnn : ∀ n, 0 ≤ g n := by
    intro n x
    dsimp only [g]
    exact mul_nonneg (hΦ0 x) (χ n).nonneg
  have hgle : ∀ n, g n ≤ Φ := by
    intro n x
    dsimp only [g]
    exact mul_le_of_le_one_right (hΦ0 x) (χ n).le_one
  -- Pointwise comparison of the truncations with the cut-off functions.
  have hf_le : ∀ n x, f n x ≤ g n x := by
    intro n x
    by_cases hx : x ∈ ball (0 : X) (n : ℝ)
    · have h1 : (χ n) x = 1 := by
        apply (χ n).one_of_mem_closedBall
        rw [mem_closedBall, dist_zero_right]
        change ‖x‖ ≤ (n : ℝ) + 1
        have hxn : ‖x‖ < (n : ℝ) := by
          have h := mem_ball.mp hx
          rwa [dist_zero_right] at h
        linarith
      dsimp only [f, g]
      rw [Set.indicator_of_mem hx, h1, mul_one]
    · dsimp only [f, g]
      rw [Set.indicator_of_notMem hx]
      exact mul_nonneg (hΦ0 x) (χ n).nonneg
  -- Monotone convergence setup.
  have hf_meas : ∀ n, AEMeasurable (fun x => ENNReal.ofReal (f n x)) μ := by
    intro n
    refine (Measurable.ennreal_ofReal ?_).aemeasurable
    dsimp only [f]
    exact hΦ.continuous.measurable.indicator measurableSet_ball
  have hf_mono : ∀ n, f n ≤ f (n + 1) := by
    intro n
    dsimp only [f]
    exact indicator_le_indicator_of_subset
      (ball_subset_ball (by exact_mod_cast Nat.le_succ n)) hΦ0
  have hFmono : ∀ᵐ x ∂μ, Monotone (fun n => ENNReal.ofReal (f n x)) :=
    Eventually.of_forall fun x => monotone_nat_of_le_succ fun n =>
      ENNReal.ofReal_le_ofReal (hf_mono n x)
  have hFtend : ∀ᵐ x ∂μ,
      Tendsto (fun n => ENNReal.ofReal (f n x)) atTop (𝓝 (ENNReal.ofReal (Φ x))) := by
    refine Eventually.of_forall fun x => ENNReal.tendsto_ofReal ?_
    obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    have hx : x ∈ ball (0 : X) (n : ℝ) := by
      rw [mem_ball, dist_zero_right]
      exact lt_of_lt_of_le hN (by exact_mod_cast hn)
    dsimp only [f]
    rw [Set.indicator_of_mem hx]
  have hMCT := lintegral_tendsto_of_tendsto_of_monotone hf_meas hFmono hFtend
  -- Uniform bound on the truncated integrals.
  have hbound : ∀ n, ∫⁻ x, ENNReal.ofReal (f n x) ∂μ ≤ ENNReal.ofReal (Λ Φ) := by
    intro n
    have hGint : Integrable (g n) μ := hint _ (hgsmooth n) (hgcompact n) (hgsupp n)
    have hGval : ∫ x, g n x ∂μ = Λ (g n) := hCc _ (hgsmooth n) (hgcompact n) (hgsupp n)
    have hGle : Λ (g n) ≤ Λ Φ := Lam_mono (hgsmooth n) (hgsupp n) hΦ hsub (hgle n)
    calc ∫⁻ x, ENNReal.ofReal (f n x) ∂μ
        ≤ ∫⁻ x, ENNReal.ofReal (g n x) ∂μ :=
          lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (hf_le n x))
      _ = ENNReal.ofReal (∫ x, g n x ∂μ) :=
          (ofReal_integral_eq_lintegral_ofReal hGint (Eventually.of_forall (hgnn n))).symm
      _ = ENNReal.ofReal (Λ (g n)) := by rw [hGval]
      _ ≤ ENNReal.ofReal (Λ Φ) := ENNReal.ofReal_le_ofReal hGle
  have hle_lin : ∫⁻ x, ENNReal.ofReal (Φ x) ∂μ ≤ ENNReal.ofReal (Λ Φ) :=
    le_of_tendsto hMCT (Eventually.of_forall hbound)
  -- Conclude integrability.
  refine ⟨hΦ.continuous.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have heq : (fun x => ‖Φ x‖ₑ) = fun x => ENNReal.ofReal (Φ x) := by
    funext x
    exact Real.enorm_eq_ofReal (hΦ0 x)
  rw [heq]
  exact lt_of_le_of_lt hle_lin ENNReal.ofReal_lt_top

end Commons.Measure.Integration