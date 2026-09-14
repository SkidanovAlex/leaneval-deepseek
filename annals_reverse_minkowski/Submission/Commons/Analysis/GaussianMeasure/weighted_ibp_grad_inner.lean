import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Order.CompletePartialOrder
import Submission.Commons.Analysis.Calculus.FDeriv.laplacian_eq_sum_second_partials
import Submission.Commons.Measure.Integral.integrable_pow_mul_exp_neg_norm_sq

namespace Commons.Analysis.GaussianMeasure

open MeasureTheory Set Real Filter
open scoped Real Topology BigOperators

set_option linter.unusedSectionVars false

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The gradient of a scalar function: `(toDual ℝ E).symm ∘ fderiv ℝ φ`. -/
private noncomputable def G (φ : E → ℝ) : E → E :=
  fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ φ x)

private lemma G_apply (φ : E → ℝ) (x : E) :
    G φ x = (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ φ x) := rfl

private lemma inner_G_apply (φ : E → ℝ) (x v : E) :
    inner ℝ (G φ x) v = fderiv ℝ φ x v := by
  rw [G_apply]
  exact InnerProductSpace.toDual_symm_apply

/-- The weight `exp (-f)`. -/
private noncomputable abbrev wt (f : E → ℝ) : E → ℝ := fun x => Real.exp (-(f x))

private lemma wt_pos (f : E → ℝ) (x : E) : 0 < wt f x := Real.exp_pos _

private lemma wt_contDiff (f : E → ℝ) (hf : ContDiff ℝ 1 f) : ContDiff ℝ 1 (wt f) :=
  Real.contDiff_exp.comp hf.neg

private lemma continuous_fderiv_apply (u : E → ℝ) (hu : ContDiff ℝ 2 u) (w : E) :
    Continuous (fun x : E => fderiv ℝ u x w) :=
  ((hu.fderiv_right (m := 1) (by norm_num)).continuous).clm_apply continuous_const

/-- `⟨∇φ, ∇ψ⟩` equals the sum of the products of the partial derivatives along any
orthonormal basis. -/
private lemma inner_G_eq_sum {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (φ ψ : E → ℝ) (x : E) :
    inner ℝ (G φ x) (G ψ x) = ∑ i, fderiv ℝ φ x (b i) * fderiv ℝ ψ x (b i) := by
  rw [← OrthonormalBasis.sum_inner_mul_inner b (G φ x) (G ψ x)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_G_apply, real_inner_comm, inner_G_apply]

/-- The Laplacian is the sum of the diagonal second derivatives along any orthonormal basis. -/
private lemma laplacian_eq_sum_fderiv {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (u : E → ℝ) (x : E) :
    Laplacian.laplacian u x = ∑ i, fderiv ℝ (fderiv ℝ u) x (b i) (b i) := by
  rw [Commons.Analysis.Calculus.FDeriv.laplacian_eq_sum_second_partials b u x]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [bilinearIteratedFDerivTwo_eq_iteratedFDeriv, iteratedFDeriv_two_apply]
  simp

/-- Derivative of `x ↦ fderiv ℝ u x z` in direction `z`. -/
private lemma fderiv_fderiv_apply_self (u : E → ℝ) (hu : ContDiff ℝ 2 u) (x z : E) :
    fderiv ℝ (fun y => fderiv ℝ u y z) x z = fderiv ℝ (fderiv ℝ u) x z z := by
  have hd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    ((hu.fderiv_right (m := 1) (by norm_num)).contDiffAt).differentiableAt (by norm_num)
  rw [fderiv_clm_apply hd (differentiableAt_const z)]
  simp [ContinuousLinearMap.flip_apply]

/-- A helper to bound the operator norm from a pointwise bound. -/
private lemma G_bound {φ : E → ℝ} {C : ℝ} (hC : 0 ≤ C) {N : ℕ}
    (h : ∀ x v : E, |fderiv ℝ φ x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖) (x : E) :
    ‖G φ x‖ ≤ C * (1 + ‖x‖) ^ N := by
  rw [G_apply]
  rw [LinearIsometryEquiv.norm_map]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [Real.norm_eq_abs]
  exact h x v

/-! ## Gradient product rules -/

private lemma G_mul (φ ψ : E → ℝ) (x : E) (hφ : DifferentiableAt ℝ φ x)
    (hψ : DifferentiableAt ℝ ψ x) :
    G (fun y => φ y * ψ y) x = φ x • G ψ x + ψ x • G φ x := by
  have h := fderiv_fun_mul hφ hψ
  rw [G_apply, G_apply, G_apply, h, map_add, map_smul, map_smul]

private lemma G_exp_neg (f : E → ℝ) (x : E) (hf : DifferentiableAt ℝ f x) :
    G (fun y => Real.exp (-(f y))) x = -(Real.exp (-(f x))) • G f x := by
  have hfd : fderiv ℝ (fun y : E => Real.exp (-(f y))) x
      = Real.exp (-(f x)) • (-(fderiv ℝ f x)) := by
    have h := (DifferentiableAt.hasFDerivAt hf.neg).exp
    simpa [fderiv_neg] using h.fderiv
  rw [G_apply, G_apply, hfd, map_smul, map_neg, neg_smul, smul_neg]

private lemma inner_G_triple (φ ψ χ : E → ℝ) (z : E) (x : E)
    (hφ : DifferentiableAt ℝ φ x) (hψ : DifferentiableAt ℝ ψ x) (hχ : DifferentiableAt ℝ χ x) :
    inner ℝ (G (fun y => φ y * ψ y * χ y) x) z
      = φ x * ψ x * inner ℝ (G χ x) z + φ x * χ x * inner ℝ (G ψ x) z
        + ψ x * χ x * inner ℝ (G φ x) z := by
  rw [show (fun y : E => φ y * ψ y * χ y) = (fun y => (φ y * ψ y) * χ y) from rfl,
    G_mul (fun y => φ y * ψ y) χ x (hφ.mul hψ) hχ,
    G_mul φ ψ x hφ hψ]
  simp only [real_inner_smul_left, inner_add_left]
  ring

/-! ## The integration-by-parts identity -/

/-- **Integration by parts for the Laplacian.**  If `ψ` is `C¹` with compact support then
`∫ ψ Δu = - ∫ ⟨∇ψ, ∇u⟩`. -/
private lemma integral_laplacian_eq_neg_inner {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (u : E → ℝ) (hu : ContDiff ℝ 2 u)
    (ψ : E → ℝ) (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ) :
    (∫ x, ψ x * Laplacian.laplacian u x) = -∫ x, inner ℝ (G ψ x) (G u x) := by
  have hdiffψ : ∀ x, DifferentiableAt ℝ ψ x :=
    fun x => hψ.contDiffAt.differentiableAt (by norm_num)
  have hcont_du : ∀ i : ι, Continuous (fun x : E => fderiv ℝ u x (b i)) :=
    fun i => continuous_fderiv_apply u hu (b i)
  have hcont_ddu : ∀ i : ι,
      Continuous (fun x : E => fderiv ℝ (fderiv ℝ u) x (b i) (b i)) :=
    fun i => (((hu.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by simp)).clm_apply
      continuous_const).clm_apply continuous_const
  have hdiff_du : ∀ (i : ι) (x : E), DifferentiableAt ℝ (fun y => fderiv ℝ u y (b i)) x := by
    intro i x
    have hc : DifferentiableAt ℝ (fderiv ℝ u) x :=
      ((hu.fderiv_right (m := 1) (by norm_num)).contDiffAt).differentiableAt (by norm_num)
    exact hc.clm_apply (differentiableAt_const (b i))
  have hcont_dψ : ∀ i : ι, Continuous (fun x : E => fderiv ℝ ψ x (b i)) :=
    fun i => (((hψ.fderiv_right (m := 0) (by simp)).continuous)).clm_apply continuous_const
  have hcs_dψ : ∀ i : ι, HasCompactSupport (fun x : E => fderiv ℝ ψ x (b i)) :=
    fun i => hcψ.fderiv_apply ℝ (b i)
  have hintA : ∀ i : ι, Integrable (fun x : E => fderiv ℝ ψ x (b i) * fderiv ℝ u x (b i)) :=
    fun i => ((hcont_dψ i).mul (hcont_du i)).integrable_of_hasCompactSupport (hcs_dψ i).mul_right
  have hintB : ∀ i : ι,
      Integrable (fun x : E => ψ x * fderiv ℝ (fun y => fderiv ℝ u y (b i)) x (b i)) := by
    intro i
    have hcont : Continuous
        (fun x : E => fderiv ℝ (fun y => fderiv ℝ u y (b i)) x (b i)) := by
      simpa only [fderiv_fderiv_apply_self u hu] using hcont_ddu i
    exact (hψ.continuous.mul hcont).integrable_of_hasCompactSupport hcψ.mul_right
  have hintC : ∀ i : ι, Integrable (fun x : E => ψ x * fderiv ℝ u x (b i)) :=
    fun i => (hψ.continuous.mul (hcont_du i)).integrable_of_hasCompactSupport hcψ.mul_right
  have key : ∀ i : ι,
      (∫ x, ψ x * fderiv ℝ (fun y => fderiv ℝ u y (b i)) x (b i))
        = -(∫ x, fderiv ℝ ψ x (b i) * fderiv ℝ u x (b i)) := by
    intro i
    exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
      (f := ψ) (g := fun x => fderiv ℝ u x (b i)) (v := b i)
      (hintA i) (hintB i) (hintC i) (fun x _ => hdiffψ x) (fun x _ => hdiff_du i x)
  have hInt_sum : ∀ i : ι, Integrable (fun x : E => ψ x * fderiv ℝ (fderiv ℝ u) x (b i) (b i)) :=
    fun i => (hψ.continuous.mul (hcont_ddu i)).integrable_of_hasCompactSupport hcψ.mul_right
  calc (∫ x, ψ x * Laplacian.laplacian u x)
      = ∫ x, ψ x * (∑ i, fderiv ℝ (fderiv ℝ u) x (b i) (b i)) := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          simp only []
          rw [laplacian_eq_sum_fderiv b u x]
      _ = ∫ x, ∑ i, ψ x * fderiv ℝ (fderiv ℝ u) x (b i) (b i) := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          simp only [Finset.mul_sum]
      _ = ∑ i, ∫ x, ψ x * fderiv ℝ (fderiv ℝ u) x (b i) (b i) := by
          simpa using integral_finsetSum (Finset.univ : Finset ι) (fun i _ => hInt_sum i)
      _ = ∑ i, ∫ x, ψ x * fderiv ℝ (fun y => fderiv ℝ u y (b i)) x (b i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          simp only []
          rw [fderiv_fderiv_apply_self u hu x (b i)]
      _ = ∑ i, -(∫ x, fderiv ℝ ψ x (b i) * fderiv ℝ u x (b i)) :=
          Finset.sum_congr rfl fun i _ => key i
      _ = -(∑ i, ∫ x, fderiv ℝ ψ x (b i) * fderiv ℝ u x (b i)) := by
          rw [Finset.sum_neg_distrib]
      _ = -(∫ x, ∑ i, fderiv ℝ ψ x (b i) * fderiv ℝ u x (b i)) := by
          rw [integral_finsetSum (Finset.univ : Finset ι) (fun i _ => hintA i)]
      _ = -(∫ x, inner ℝ (G ψ x) (G u x)) := by
          congr 1
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          simp only []
          exact (inner_G_eq_sum b ψ u x).symm

/-! ## Integrability helpers -/

private lemma integrable_poly_mul_gauss (Φ : E → ℝ) (b : ℝ) (hb : 0 < b)
    (hΦm : AEStronglyMeasurable Φ)
    (hΦd : ∃ C : ℝ, ∃ N : ℕ, ∀ x, ‖Φ x‖ ≤ C * ((1 + ‖x‖) ^ N * Real.exp (-b * ‖x‖ ^ 2))) :
    Integrable Φ := by
  obtain ⟨C, N, h⟩ := hΦd
  exact Integrable.mono' ((Commons.Measure.Integral.integrable_pow_mul_exp_neg_norm_sq b hb N).const_mul C) hΦm
    (ae_of_all _ h)

private lemma poly_mul_le {A B t : ℝ} {m n : ℕ} (ht : 1 ≤ t) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (A * t ^ m) * (B * t ^ n) = (A * B) * t ^ (m + n) := by
  rw [pow_add]; ring

private lemma poly_add_le {A B t : ℝ} {m n : ℕ} (ht : 1 ≤ t) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    A * t ^ m + B * t ^ n ≤ (A + B) * t ^ max m n := by
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  calc A * t ^ m + B * t ^ n ≤ A * t ^ max m n + B * t ^ max m n :=
        add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht (le_max_left _ _)) hA)
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht (le_max_right _ _)) hB)
    _ = (A + B) * t ^ max m n := by ring

/-! ## The radial cutoff -/

private noncomputable abbrev cut (ρ : ContDiffBump (0 : E)) (R : ℝ) : E → ℝ :=
  fun x => (ρ : E → ℝ) (R⁻¹ • x)

private lemma cut_contDiff (ρ : ContDiffBump (0 : E)) (R : ℝ) (n : ℕ∞) :
    ContDiff ℝ n (cut ρ R) :=
  ρ.contDiff.comp (contDiff_id.const_smul (R⁻¹))

private lemma cut_nonneg (ρ : ContDiffBump (0 : E)) (R : ℝ) (x : E) : 0 ≤ cut ρ R x :=
  ρ.nonneg

private lemma cut_le_one (ρ : ContDiffBump (0 : E)) (R : ℝ) (x : E) : cut ρ R x ≤ 1 :=
  ρ.le_one

private lemma cut_hasCompactSupport (ρ : ContDiffBump (0 : E)) (R : ℝ) (hR : R ≠ 0) :
    HasCompactSupport (cut ρ R) := by
  have h := (ρ.hasCompactSupport).comp_homeomorph
    (Homeomorph.smulOfNeZero R⁻¹ (by simpa using hR))
  simpa [cut, Function.comp_def] using h

private lemma rho_zero (ρ : ContDiffBump (0 : E)) : (ρ : E → ℝ) 0 = 1 :=
  ρ.one_of_mem_closedBall (by rw [Metric.mem_closedBall, dist_self]; exact ρ.rIn_pos.le)

private lemma cut_tendsto (ρ : ContDiffBump (0 : E)) (x : E) :
    Tendsto (fun R : ℝ => cut ρ R x) atTop (𝓝 1) := by
  have h1 : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 (0 : ℝ)) := tendsto_inv_atTop_zero
  have h2 : Tendsto (fun R : ℝ => R⁻¹ • x) atTop (𝓝 ((0 : ℝ) • x)) := h1.smul_const x
  rw [zero_smul] at h2
  have h3 : Tendsto (fun R : ℝ => (ρ : E → ℝ) (R⁻¹ • x)) atTop (𝓝 ((ρ : E → ℝ) 0)) :=
    (ρ.continuous.tendsto 0).comp h2
  rw [rho_zero] at h3
  simpa [cut] using h3

private lemma exists_rho_fderiv_bound (ρ : ContDiffBump (0 : E)) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ y : E, ‖fderiv ℝ (ρ : E → ℝ) y‖ ≤ Λ := by
  have hcont : Continuous (fun y : E => fderiv ℝ (ρ : E → ℝ) y) :=
    (ρ.contDiff (n := ⊤)).continuous_fderiv (by simp)
  obtain ⟨Λ, hΛ⟩ := hcont.bounded_above_of_compact_support (ρ.hasCompactSupport.fderiv ℝ)
  exact ⟨max Λ 0, le_max_right _ _, fun y => le_trans (hΛ y) (le_max_left _ _)⟩

private lemma cut_fderiv_apply_le (ρ : ContDiffBump (0 : E)) (Λ : ℝ) (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ y : E, ‖fderiv ℝ (ρ : E → ℝ) y‖ ≤ Λ)
    (R : ℝ) (hR : 0 < R) (x z : E) :
    ‖fderiv ℝ (cut ρ R) x z‖ ≤ Λ * R⁻¹ * ‖z‖ := by
  have hL : HasFDerivAt (fun x : E => R⁻¹ • x) (R⁻¹ • (1 : E →L[ℝ] E)) x :=
    ContinuousLinearMap.hasFDerivAt (R⁻¹ • (1 : E →L[ℝ] E)) (x := x)
  have hr : HasFDerivAt (ρ : E → ℝ) (fderiv ℝ (ρ : E → ℝ) (R⁻¹ • x)) (R⁻¹ • x) :=
    DifferentiableAt.hasFDerivAt
      (((ρ.contDiff (n := ⊤)).contDiffAt).differentiableAt (by simp))
  have hc : fderiv ℝ (cut ρ R) x
      = (fderiv ℝ (ρ : E → ℝ) (R⁻¹ • x)).comp (R⁻¹ • (1 : E →L[ℝ] E)) :=
    (hr.comp x hL).fderiv
  rw [hc, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply]
  calc ‖fderiv ℝ (ρ : E → ℝ) (R⁻¹ • x) (R⁻¹ • z)‖
      ≤ ‖fderiv ℝ (ρ : E → ℝ) (R⁻¹ • x)‖ * ‖R⁻¹ • z‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ Λ * (R⁻¹ * ‖z‖) := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le)]
        exact mul_le_mul_of_nonneg_right (hΛ _) (by positivity)
    _ = Λ * R⁻¹ * ‖z‖ := by ring

/-! ## Limits -/

private lemma tendsto_integral_cut_mul (ρ : ContDiffBump (0 : E)) (Ψ : E → ℝ)
    (hΨ : Integrable Ψ) :
    Tendsto (fun R : ℝ => ∫ x, cut ρ R x * Ψ x) atTop (𝓝 (∫ x, Ψ x)) := by
  refine tendsto_integral_filter_of_dominated_convergence (l := atTop) (fun x => ‖Ψ x‖) ?_ ?_
    hΨ.norm ?_
  · exact Eventually.of_forall fun R => AEStronglyMeasurable.mul
      (((cut_contDiff ρ R ⊤).continuous.measurable).aestronglyMeasurable) hΨ.aestronglyMeasurable
  · exact Eventually.of_forall fun R => ae_of_all _ fun x => by
      rw [norm_mul, Real.norm_eq_abs]
      calc |cut ρ R x| * ‖Ψ x‖ ≤ 1 * ‖Ψ x‖ := by
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            rw [abs_le]
            exact ⟨by linarith [cut_nonneg ρ R x], cut_le_one ρ R x⟩
        _ = ‖Ψ x‖ := one_mul _
  · exact ae_of_all _ fun x => by
      simpa using (cut_tendsto ρ x).mul tendsto_const_nhds

private lemma tendsto_integral_cut_fderiv_zero (ρ : ContDiffBump (0 : E)) (Λ : ℝ) (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ y : E, ‖fderiv ℝ (ρ : E → ℝ) y‖ ≤ Λ)
    (Ψ : E → ℝ) (V : E → E) (hint : Integrable (fun x => |Ψ x| * ‖V x‖)) :
    Tendsto (fun R : ℝ => ∫ x, Ψ x * fderiv ℝ (cut ρ R) x (V x)) atTop (𝓝 0) := by
  set C : ℝ := ∫ x, |Ψ x| * ‖V x‖ with hC
  have hC0 : 0 ≤ C := integral_nonneg fun x => mul_nonneg (abs_nonneg _) (norm_nonneg _)
  have hb : ∀ R : ℝ, 0 < R → ‖∫ x, Ψ x * fderiv ℝ (cut ρ R) x (V x)‖ ≤ Λ * R⁻¹ * C := by
    intro R hR
    have hdom : Integrable (fun x : E => Λ * R⁻¹ * (|Ψ x| * ‖V x‖)) := hint.const_mul _
    calc ‖∫ x, Ψ x * fderiv ℝ (cut ρ R) x (V x)‖
        ≤ ∫ x, ‖Ψ x * fderiv ℝ (cut ρ R) x (V x)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x, Λ * R⁻¹ * (|Ψ x| * ‖V x‖) := by
            refine integral_mono_of_nonneg (ae_of_all _ fun x => norm_nonneg _) hdom
              (ae_of_all _ fun x => ?_)
            show ‖Ψ x * fderiv ℝ (cut ρ R) x (V x)‖ ≤ Λ * R⁻¹ * (|Ψ x| * ‖V x‖)
            rw [norm_mul, Real.norm_eq_abs]
            calc |Ψ x| * ‖fderiv ℝ (cut ρ R) x (V x)‖
                ≤ |Ψ x| * (Λ * R⁻¹ * ‖V x‖) :=
                  mul_le_mul_of_nonneg_left (cut_fderiv_apply_le ρ Λ hΛ0 hΛ R hR x (V x))
                    (abs_nonneg _)
              _ = Λ * R⁻¹ * (|Ψ x| * ‖V x‖) := by ring
      _ = Λ * R⁻¹ * C := by rw [integral_const_mul]
  have hlim : Tendsto (fun R : ℝ => Λ * R⁻¹ * C) atTop (𝓝 0) := by
    have h1 : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 (0 : ℝ)) := tendsto_inv_atTop_zero
    simpa using (h1.const_mul Λ).mul_const C
  have hbound' : ∀ᶠ R : ℝ in atTop,
      ‖∫ x, Ψ x * fderiv ℝ (cut ρ R) x (V x)‖ ≤ Λ * R⁻¹ * C :=
    eventually_atTop.mpr ⟨1, fun R hR => hb R (lt_of_lt_of_le one_pos hR)⟩
  have hzero : Tendsto (fun R : ℝ => ‖∫ x, Ψ x * fderiv ℝ (cut ρ R) x (V x)‖) atTop (𝓝 0) :=
    squeeze_zero' (eventually_atTop.mpr ⟨1, fun R _ => norm_nonneg _⟩) hbound' hlim
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hzero

private lemma norm_mul_le_of_abs_le_one {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (y : ℝ) :
    ‖c * y‖ ≤ ‖y‖ := by
  rw [norm_mul, Real.norm_of_nonneg hc0]
  exact mul_le_of_le_one_left (norm_nonneg _) hc1

private lemma continuous_G (φ : E → ℝ) (hφ : ContDiff ℝ 1 φ) : Continuous (G φ) := by
  have h : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  exact (LinearIsometryEquiv.continuous (InnerProductSpace.toDual ℝ E).symm).comp h

/-- **Integration by parts for the Laplacian.**  If `u : E → ℝ` is `C²` and the weight
`ψ : E → ℝ` is `C¹` with compact support, then `∫ ψ Δu = - ∫ ⟨∇ψ, ∇u⟩`.

This is the (boundary-free) divergence theorem version of the Laplacian integration by parts,
formulated for an arbitrary finite-dimensional real inner product space.  It is the tool used
in `weighted_ibp_grad_inner` to move the gradient off `h` in the weighted
(unnormalized-Gaussian) inner product. -/
theorem integral_laplacian_mul_eq_neg_inner {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (u : E → ℝ) (hu : ContDiff ℝ 2 u)
    (ψ : E → ℝ) (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ) :
    (∫ x, ψ x * Laplacian.laplacian u x)
      = -∫ x, inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ ψ x))
          ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x)) := by
  have h := integral_laplacian_eq_neg_inner (stdOrthonormalBasis ℝ E) u hu ψ hψ hcψ
  simpa only [G_apply] using h

theorem weighted_ibp_grad_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    (f u h : E → ℝ)
    (hf : ContDiff ℝ 1 f) (hu : ContDiff ℝ 2 u) (hh : ContDiff ℝ 1 h)
    (hdec : ∃ c : ℝ, ∀ x : E, c + Real.pi * ‖x‖ ^ 2 ≤ f x)
    (hgf : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : E,
      |fderiv ℝ f x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖)
    (hgu : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v w : E,
      |u x| ≤ C * (1 + ‖x‖) ^ N ∧
      |fderiv ℝ u x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ∧
      |fderiv ℝ (fderiv ℝ u) x v w| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ * ‖w‖)
    (hgh : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : E,
      |h x| ≤ C * (1 + ‖x‖) ^ N ∧
      |fderiv ℝ h x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖) :
    (∫ x, inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x))
        ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ h x)) * Real.exp (-(f x)))
      = ∫ x, (- Laplacian.laplacian u x
          + inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
              ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x))) * h x
          * Real.exp (-(f x)) := by
  change (∫ x, inner ℝ (G u x) (G h x) * wt f x)
      = ∫ x, (- Laplacian.laplacian u x + inner ℝ (G f x) (G u x)) * h x * wt f x
  obtain ⟨Cf, hCf, Nf, hfN⟩ := hgf
  obtain ⟨Cu, hCu, Nu, huN⟩ := hgu
  obtain ⟨Ch, hCh, Nh, hhN⟩ := hgh
  obtain ⟨c, hc⟩ := hdec
  have hdh : ∀ x, DifferentiableAt ℝ h x :=
    fun x => hh.contDiffAt.differentiableAt (by norm_num)
  have hdf : ∀ x, DifferentiableAt ℝ f x :=
    fun x => hf.contDiffAt.differentiableAt (by norm_num)
  have hdwt : ∀ x, DifferentiableAt ℝ (wt f) x :=
    fun x => (wt_contDiff f hf).contDiffAt.differentiableAt (by norm_num)
  have hwtc : Continuous (wt f) := (wt_contDiff f hf).continuous
  have hGfc : Continuous (G f) := continuous_G f hf
  have hGuc : Continuous (G u) := continuous_G u (hu.of_le (by norm_num))
  have hGhc : Continuous (G h) := continuous_G h hh
  have hwtm : AEStronglyMeasurable (wt f) := hwtc.aestronglyMeasurable
  have hdecb : ∀ x, wt f x ≤ Real.exp (-c) * Real.exp (-Real.pi * ‖x‖ ^ 2) := by
    intro x
    rw [wt, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    linarith [hc x]
  have hGfb : ∀ x, ‖G f x‖ ≤ Cf * (1 + ‖x‖) ^ Nf :=
    fun x => G_bound hCf (fun x v => hfN x v) x
  have hGub : ∀ x, ‖G u x‖ ≤ Cu * (1 + ‖x‖) ^ Nu :=
    fun x => G_bound hCu (fun x v => (huN x v v).2.1) x
  have hGhb : ∀ x, ‖G h x‖ ≤ Ch * (1 + ‖x‖) ^ Nh :=
    fun x => G_bound hCh (fun x v => (hhN x v).2) x
  have hhb : ∀ x, |h x| ≤ Ch * (1 + ‖x‖) ^ Nh := fun x => (hhN x 0).1
  have hu2b : ∀ x v w, |fderiv ℝ (fderiv ℝ u) x v w| ≤ Cu * (1 + ‖x‖) ^ Nu * ‖v‖ * ‖w‖ :=
    fun x v w => (huN x v w).2.2
  have hP1 : ∀ x : E, (1 : ℝ) ≤ 1 + ‖x‖ := fun x => le_add_of_nonneg_right (norm_nonneg x)
  let ρ : ContDiffBump (0 : E) := default
  obtain ⟨Λ, hΛ0, hΛ⟩ := exists_rho_fderiv_bound ρ
  let b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E := stdOrthonormalBasis ℝ E
  have hΔcont : Continuous (fun x : E => Laplacian.laplacian u x) := by
    have hkey : (fun x : E => Laplacian.laplacian u x)
        = fun x => ∑ i : Fin (Module.finrank ℝ E),
            fderiv ℝ (fderiv ℝ u) x (b i) (b i) :=
      funext fun x => laplacian_eq_sum_fderiv b u x
    rw [hkey]
    refine continuous_finsetSum _ fun i _ => ?_
    exact (((hu.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by simp)).clm_apply
      continuous_const).clm_apply continuous_const
  have hΔb : ∀ x, |Laplacian.laplacian u x|
      ≤ ((Module.finrank ℝ E : ℝ) * Cu) * (1 + ‖x‖) ^ Nu := by
    intro x
    rw [laplacian_eq_sum_fderiv b u x]
    have hterm : ∀ i : Fin (Module.finrank ℝ E),
        |fderiv ℝ (fderiv ℝ u) x (b i) (b i)| ≤ Cu * (1 + ‖x‖) ^ Nu := by
      intro i
      have h := hu2b x (b i) (b i)
      simpa using h
    calc |∑ i : Fin (Module.finrank ℝ E), fderiv ℝ (fderiv ℝ u) x (b i) (b i)|
        ≤ ∑ i : Fin (Module.finrank ℝ E), |fderiv ℝ (fderiv ℝ u) x (b i) (b i)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin (Module.finrank ℝ E), Cu * (1 + ‖x‖) ^ Nu :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = ((Module.finrank ℝ E : ℝ) * Cu) * (1 + ‖x‖) ^ Nu := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  -- integrability of the limit integrands
  have hIntL1 : Integrable (fun x => wt f x * inner ℝ (G h x) (G u x)) := by
    refine integrable_poly_mul_gauss _ Real.pi Real.pi_pos ?_
      ⟨Real.exp (-c) * (Ch * Cu), Nh + Nu, fun x => ?_⟩
    · exact (hwtm.mul ((hGhc.inner hGuc).aestronglyMeasurable))
    · simp only [norm_mul, Real.norm_of_nonneg (wt_pos f x).le]
      calc wt f x * ‖inner ℝ (G h x) (G u x)‖
          ≤ (Real.exp (-c) * Real.exp (-Real.pi * ‖x‖ ^ 2)) *
              ((Ch * Cu) * (1 + ‖x‖) ^ (Nh + Nu)) := by
            refine mul_le_mul (hdecb x) ?_ (norm_nonneg _) (by positivity)
            calc ‖inner ℝ (G h x) (G u x)‖ = |inner ℝ (G h x) (G u x)| := Real.norm_eq_abs _
              _ ≤ ‖G h x‖ * ‖G u x‖ := abs_real_inner_le_norm _ _
              _ ≤ (Ch * (1 + ‖x‖) ^ Nh) * (Cu * (1 + ‖x‖) ^ Nu) :=
                    mul_le_mul (hGhb x) (hGub x) (norm_nonneg _) (by positivity)
              _ = (Ch * Cu) * (1 + ‖x‖) ^ (Nh + Nu) := poly_mul_le (hP1 x) hCh hCu
        _ = Real.exp (-c) * (Ch * Cu) *
              ((1 + ‖x‖) ^ (Nh + Nu) * Real.exp (-Real.pi * ‖x‖ ^ 2)) := by ring
  have hIntL3 : Integrable (fun x => h x * wt f x * inner ℝ (G f x) (G u x)) := by
    refine integrable_poly_mul_gauss _ Real.pi Real.pi_pos ?_
      ⟨Real.exp (-c) * (Ch * Cf * Cu), Nh + (Nf + Nu), fun x => ?_⟩
    · exact (((hh.continuous.measurable).aestronglyMeasurable.mul hwtm).mul
        ((hGfc.inner hGuc).aestronglyMeasurable))
    · simp only [norm_mul, norm_mul, Real.norm_of_nonneg (wt_pos f x).le]
      calc |h x| * wt f x * ‖inner ℝ (G f x) (G u x)‖
          ≤ (Ch * (1 + ‖x‖) ^ Nh) * (Real.exp (-c) * Real.exp (-Real.pi * ‖x‖ ^ 2)) *
              ((Cf * Cu) * (1 + ‖x‖) ^ (Nf + Nu)) := by
            refine mul_le_mul (mul_le_mul (hhb x) (hdecb x) (by positivity) (by positivity)) ?_
              (norm_nonneg _) (by positivity)
            calc ‖inner ℝ (G f x) (G u x)‖ = |inner ℝ (G f x) (G u x)| := Real.norm_eq_abs _
              _ ≤ ‖G f x‖ * ‖G u x‖ := abs_real_inner_le_norm _ _
              _ ≤ (Cf * (1 + ‖x‖) ^ Nf) * (Cu * (1 + ‖x‖) ^ Nu) :=
                    mul_le_mul (hGfb x) (hGub x) (norm_nonneg _) (by positivity)
              _ = (Cf * Cu) * (1 + ‖x‖) ^ (Nf + Nu) := poly_mul_le (hP1 x) hCf hCu
        _ = Real.exp (-c) * (Ch * Cf * Cu) *
              ((1 + ‖x‖) ^ (Nh + (Nf + Nu)) * Real.exp (-Real.pi * ‖x‖ ^ 2)) := by
            rw [pow_add, pow_add]; ring
  have hIntLA : Integrable (fun x => wt f x * h x * Laplacian.laplacian u x) := by
    refine integrable_poly_mul_gauss _ Real.pi Real.pi_pos ?_
      ⟨Real.exp (-c) * (Ch * ((Module.finrank ℝ E : ℝ) * Cu)), Nh + Nu, fun x => ?_⟩
    · exact ((hwtm.mul ((hh.continuous.measurable).aestronglyMeasurable)).mul
        hΔcont.aestronglyMeasurable)
    · simp only [norm_mul, norm_mul, Real.norm_of_nonneg (wt_pos f x).le]
      calc wt f x * |h x| * ‖Laplacian.laplacian u x‖
          ≤ (Real.exp (-c) * Real.exp (-Real.pi * ‖x‖ ^ 2)) * (Ch * (1 + ‖x‖) ^ Nh) *
              (((Module.finrank ℝ E : ℝ) * Cu) * (1 + ‖x‖) ^ Nu) := by
            refine mul_le_mul (mul_le_mul (hdecb x) (hhb x) (abs_nonneg _) (by positivity)) ?_
              (norm_nonneg _) (by positivity)
            rw [Real.norm_eq_abs]
            exact hΔb x
        _ = Real.exp (-c) * (Ch * ((Module.finrank ℝ E : ℝ) * Cu)) *
              ((1 + ‖x‖) ^ (Nh + Nu) * Real.exp (-Real.pi * ‖x‖ ^ 2)) := by
            rw [pow_add]; ring
  have hIntT2 : Integrable (fun x => |wt f x * h x| * ‖G u x‖) := by
    refine integrable_poly_mul_gauss _ Real.pi Real.pi_pos ?_
      ⟨Real.exp (-c) * (Ch * Cu), Nh + Nu, fun x => ?_⟩
    · exact (((hwtm.mul (hh.continuous.measurable).aestronglyMeasurable).norm).mul
        hGuc.norm.aestronglyMeasurable)
    · have hone : ‖|wt f x * h x| * ‖G u x‖‖ = wt f x * |h x| * ‖G u x‖ := by
        rw [norm_mul, Real.norm_of_nonneg (abs_nonneg _), Real.norm_eq_abs, abs_norm,
          abs_mul, abs_of_nonneg (wt_pos f x).le]
      rw [hone]
      calc wt f x * |h x| * ‖G u x‖
          ≤ (Real.exp (-c) * Real.exp (-Real.pi * ‖x‖ ^ 2)) * (Ch * (1 + ‖x‖) ^ Nh) *
              (Cu * (1 + ‖x‖) ^ Nu) :=
            mul_le_mul (mul_le_mul (hdecb x) (hhb x) (abs_nonneg _) (by positivity))
              (hGub x) (norm_nonneg _) (by positivity)
        _ = Real.exp (-c) * (Ch * Cu) *
              ((1 + ‖x‖) ^ (Nh + Nu) * Real.exp (-Real.pi * ‖x‖ ^ 2)) := by
            rw [pow_add]; ring
  have hexp : ∀ (R : ℝ) (x : E),
      inner ℝ (G (fun y => wt f y * cut ρ R y * h y) x) (G u x)
        = wt f x * cut ρ R x * inner ℝ (G h x) (G u x)
          + wt f x * h x * inner ℝ (G (cut ρ R) x) (G u x)
          - cut ρ R x * h x * wt f x * inner ℝ (G f x) (G u x) := by
    intro R x
    have hdcut : DifferentiableAt ℝ (cut ρ R) x :=
      (cut_contDiff ρ R 1).contDiffAt.differentiableAt (by norm_num)
    rw [inner_G_triple (wt f) (cut ρ R) h (G u x) x (hdwt x) hdcut (hdh x),
      G_exp_neg f x (hdf x), real_inner_smul_left]
    ring
  have hIntT1R : ∀ R : ℝ, 0 < R →
      Integrable (fun x => wt f x * cut ρ R x * inner ℝ (G h x) (G u x)) := by
    intro R _
    refine Integrable.mono' hIntL1.norm ?_ ?_
    · exact ((hwtm.mul (((cut_contDiff ρ R 1).continuous.measurable).aestronglyMeasurable)).mul
        ((hGhc.inner hGuc).aestronglyMeasurable))
    · filter_upwards with x
      have hc1 : cut ρ R x ≤ 1 := cut_le_one ρ R x
      have hc0' : 0 ≤ cut ρ R x := cut_nonneg ρ R x
      have hassoc : wt f x * cut ρ R x * inner ℝ (G h x) (G u x)
          = cut ρ R x * (wt f x * inner ℝ (G h x) (G u x)) := by ring
      rw [hassoc]
      exact norm_mul_le_of_abs_le_one hc0' hc1 _
  have hIntT2R : ∀ R : ℝ, 0 < R →
      Integrable (fun x => wt f x * h x * inner ℝ (G (cut ρ R) x) (G u x)) := by
    intro R hR
    refine Integrable.mono' (hIntT2.const_mul (Λ * R⁻¹)) ?_ ?_
    · exact ((hwtm.mul ((hh.continuous.measurable).aestronglyMeasurable)).mul
        ((continuous_G (cut ρ R) (cut_contDiff ρ R 1)).inner hGuc).aestronglyMeasurable)
    · filter_upwards with x
      rw [inner_G_apply]
      have hT2 : ‖wt f x * h x * fderiv ℝ (cut ρ R) x (G u x)‖
          = |wt f x * h x| * ‖fderiv ℝ (cut ρ R) x (G u x)‖ := by
        rw [norm_mul, Real.norm_eq_abs]
      rw [hT2]
      calc |wt f x * h x| * ‖fderiv ℝ (cut ρ R) x (G u x)‖
          ≤ |wt f x * h x| * (Λ * R⁻¹ * ‖G u x‖) :=
            mul_le_mul_of_nonneg_left (cut_fderiv_apply_le ρ Λ hΛ0 hΛ R hR x (G u x))
              (abs_nonneg _)
        _ = Λ * R⁻¹ * (|wt f x * h x| * ‖G u x‖) := by ring
  have hIntT3R : ∀ R : ℝ, 0 < R →
      Integrable (fun x => cut ρ R x * h x * wt f x * inner ℝ (G f x) (G u x)) := by
    intro R _
    refine Integrable.mono' hIntL3.norm ?_ ?_
    · exact (((((cut_contDiff ρ R 1).continuous.measurable).aestronglyMeasurable.mul
        (hh.continuous.measurable).aestronglyMeasurable).mul hwtm).mul
        ((hGfc.inner hGuc).aestronglyMeasurable))
    · filter_upwards with x
      have hc1 : cut ρ R x ≤ 1 := cut_le_one ρ R x
      have hc0' : 0 ≤ cut ρ R x := cut_nonneg ρ R x
      have hassoc : cut ρ R x * h x * wt f x * inner ℝ (G f x) (G u x)
          = cut ρ R x * (h x * wt f x * inner ℝ (G f x) (G u x)) := by ring
      rw [hassoc]
      exact norm_mul_le_of_abs_le_one hc0' hc1 _
  -- the per-R identity from integration by parts
  have hcompA : ∀ R : ℝ, 0 < R →
      (∫ x, wt f x * cut ρ R x * h x * Laplacian.laplacian u x)
        = -(∫ x, inner ℝ (G (fun y => wt f y * cut ρ R y * h y) x) (G u x)) := by
    intro R hR
    exact integral_laplacian_eq_neg_inner b u hu (fun y => wt f y * cut ρ R y * h y)
      (((wt_contDiff f hf).mul (cut_contDiff ρ R 1)).mul hh)
      ((cut_hasCompactSupport ρ R hR.ne').mono' fun x hx => subset_tsupport _
        (Function.mem_support.mpr fun hc => hx (by
          show wt f x * cut ρ R x * h x = 0
          rw [hc]; ring)))
  have hsplit : ∀ R : ℝ, 0 < R →
      (∫ x, inner ℝ (G (fun y => wt f y * cut ρ R y * h y) x) (G u x))
        = (∫ x, wt f x * cut ρ R x * inner ℝ (G h x) (G u x))
          + (∫ x, wt f x * h x * inner ℝ (G (cut ρ R) x) (G u x))
          - (∫ x, cut ρ R x * h x * wt f x * inner ℝ (G f x) (G u x)) := by
    intro R hR
    rw [show (fun x => inner ℝ (G (fun y => wt f y * cut ρ R y * h y) x) (G u x))
        = fun x => wt f x * cut ρ R x * inner ℝ (G h x) (G u x)
            + wt f x * h x * inner ℝ (G (cut ρ R) x) (G u x)
            - cut ρ R x * h x * wt f x * inner ℝ (G f x) (G u x) from
        funext fun x => hexp R x]
    rw [integral_sub (f := fun x => wt f x * cut ρ R x * inner ℝ (G h x) (G u x)
          + wt f x * h x * inner ℝ (G (cut ρ R) x) (G u x))
        (g := fun x => cut ρ R x * h x * wt f x * inner ℝ (G f x) (G u x))
        ((hIntT1R R hR).add (hIntT2R R hR)) (hIntT3R R hR),
      integral_add (f := fun x => wt f x * cut ρ R x * inner ℝ (G h x) (G u x))
        (g := fun x => wt f x * h x * inner ℝ (G (cut ρ R) x) (G u x))
        (hIntT1R R hR) (hIntT2R R hR)]
  -- limits
  have ltendA : Tendsto (fun R : ℝ => ∫ x, wt f x * cut ρ R x * h x * Laplacian.laplacian u x)
      atTop (𝓝 (∫ x, wt f x * h x * Laplacian.laplacian u x)) := by
    have h := tendsto_integral_cut_mul ρ (fun x => wt f x * h x * Laplacian.laplacian u x) hIntLA
    refine h.congr' (Eventually.of_forall fun R => ?_)
    exact integral_congr_ae (Eventually.of_forall fun x => by ring)
  have ltendT1 : Tendsto (fun R : ℝ => ∫ x, wt f x * cut ρ R x * inner ℝ (G h x) (G u x))
      atTop (𝓝 (∫ x, wt f x * inner ℝ (G h x) (G u x))) := by
    have h := tendsto_integral_cut_mul ρ (fun x => wt f x * inner ℝ (G h x) (G u x)) hIntL1
    refine h.congr' (Eventually.of_forall fun R => ?_)
    exact integral_congr_ae (Eventually.of_forall fun x => by ring)
  have ltendT3 : Tendsto (fun R : ℝ => ∫ x, cut ρ R x * h x * wt f x * inner ℝ (G f x) (G u x))
      atTop (𝓝 (∫ x, h x * wt f x * inner ℝ (G f x) (G u x))) := by
    have h := tendsto_integral_cut_mul ρ (fun x => h x * wt f x * inner ℝ (G f x) (G u x)) hIntL3
    refine h.congr' (Eventually.of_forall fun R => ?_)
    exact integral_congr_ae (Eventually.of_forall fun x => by ring)
  have ltendT2 : Tendsto (fun R : ℝ => ∫ x, wt f x * h x * inner ℝ (G (cut ρ R) x) (G u x))
      atTop (𝓝 0) := by
    have h := tendsto_integral_cut_fderiv_zero ρ Λ hΛ0 hΛ (fun x => wt f x * h x) (G u) hIntT2
    refine h.congr' (Eventually.of_forall fun R => ?_)
    exact integral_congr_ae (Eventually.of_forall fun x => by
      simp only []
      rw [inner_G_apply])
  have ltendg : Tendsto (fun R : ℝ =>
      (∫ x, wt f x * cut ρ R x * h x * Laplacian.laplacian u x)
        + ((∫ x, wt f x * cut ρ R x * inner ℝ (G h x) (G u x))
          + (∫ x, wt f x * h x * inner ℝ (G (cut ρ R) x) (G u x))
          - (∫ x, cut ρ R x * h x * wt f x * inner ℝ (G f x) (G u x)))) atTop
      (𝓝 ((∫ x, wt f x * h x * Laplacian.laplacian u x)
        + ((∫ x, wt f x * inner ℝ (G h x) (G u x)) + 0
          - (∫ x, h x * wt f x * inner ℝ (G f x) (G u x))))) :=
    ltendA.add ((ltendT1.add ltendT2).sub ltendT3)
  have hg0 : ∀ᶠ R : ℝ in atTop,
      (∫ x, wt f x * cut ρ R x * h x * Laplacian.laplacian u x)
        + ((∫ x, wt f x * cut ρ R x * inner ℝ (G h x) (G u x))
          + (∫ x, wt f x * h x * inner ℝ (G (cut ρ R) x) (G u x))
          - (∫ x, cut ρ R x * h x * wt f x * inner ℝ (G f x) (G u x))) = 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    rw [hcompA R hR, hsplit R hR]
    ring
  have ltendg0 : Tendsto (fun R : ℝ =>
      (∫ x, wt f x * cut ρ R x * h x * Laplacian.laplacian u x)
        + ((∫ x, wt f x * cut ρ R x * inner ℝ (G h x) (G u x))
          + (∫ x, wt f x * h x * inner ℝ (G (cut ρ R) x) (G u x))
          - (∫ x, cut ρ R x * h x * wt f x * inner ℝ (G f x) (G u x)))) atTop (𝓝 0) :=
    tendsto_const_nhds.congr' (hg0.mono fun R h => h.symm)
  have huniq := tendsto_nhds_unique ltendg0 ltendg
  have hL1 : (∫ x, wt f x * inner ℝ (G h x) (G u x))
      = (∫ x, h x * wt f x * inner ℝ (G f x) (G u x))
        - (∫ x, wt f x * h x * Laplacian.laplacian u x) := by linarith
  have hfinal : (∫ x, (- Laplacian.laplacian u x + inner ℝ (G f x) (G u x)) * h x * wt f x)
      = (∫ x, h x * wt f x * inner ℝ (G f x) (G u x))
        - (∫ x, wt f x * h x * Laplacian.laplacian u x) := by
    rw [← integral_sub hIntL3 hIntLA]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    ring
  have hone : (∫ x, inner ℝ (G u x) (G h x) * wt f x)
      = (∫ x, wt f x * inner ℝ (G h x) (G u x)) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only []
    rw [real_inner_comm (G h x) (G u x)]
    ring
  exact hone.trans (hL1.trans hfinal.symm)

end

end Commons.Analysis.GaussianMeasure
