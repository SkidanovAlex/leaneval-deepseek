import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Order.CompletePartialOrder
import Submission.Commons.Analysis.Convolution.fderiv_moll_weakGrad
import Submission.Commons.Analysis.Convolution.fderiv_fderiv_moll_apply
import Submission.Commons.Measure.Mollification.tendsto_pairing_mollMeasure
import Submission.Commons.Measure.Mollification.tendsto_integral_mul_bump
import Submission.Commons.Analysis.Asymptotics.integrable_pow_mul_exp_neg_sq
import Submission.Commons.Analysis.Calculus.FDeriv.laplacian_eq_sum_second_partials

open MeasureTheory Set Real Filter
open scoped Real Topology InnerProductSpace Convolution

namespace Commons.Analysis.GaussianMeasure

noncomputable section

set_option maxHeartbeats 1600000

/-! ## Gaussian decay helpers

These are the standard consequences of the strong convexity / convexity hypotheses: for an even
`f` with `f - π‖·‖²` convex and `D²f ⪰ 2π`, the weight `exp (-f)` decays like a Gaussian. -/

/-- For an even convex function, the origin is a global minimum. -/
lemma even_convex_min {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : E → ℝ}
    (hconv : ConvexOn ℝ Set.univ g) (he : ∀ x, g (-x) = g x) (x : E) : g 0 ≤ g x := by
  have h := hconv.2 (Set.mem_univ x) (Set.mem_univ (-x)) (by norm_num) (by norm_num)
    (by norm_num : ((1:ℝ)/2) + 1/2 = 1)
  have hx : ((1:ℝ)/2) • x + ((1:ℝ)/2) • (-x) = 0 := by module
  rw [hx, he x] at h
  simp only [smul_eq_mul] at h
  linarith

/-- `f - π‖·‖²` is convex and even, hence `π‖x‖² + f 0 ≤ f x`. -/
lemma pi_mul_norm_sq_add_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (he : ∀ x, f (-x) = f x)
    (hconv : ConvexOn ℝ Set.univ (fun x => f x - Real.pi * ‖x‖ ^ 2)) (x : E) :
    Real.pi * ‖x‖ ^ 2 + f 0 ≤ f x := by
  have hge : ∀ y : E, (fun y => f y - Real.pi * ‖y‖ ^ 2) (-y)
      = (fun y => f y - Real.pi * ‖y‖ ^ 2) y := by
    intro y; simp only [he y, norm_neg]
  have hmin := even_convex_min hconv hge x
  simp only [norm_zero, pow_two, mul_zero, sub_zero] at hmin
  linarith

/-- Decay bound: `exp (-f x) ≤ exp (-f 0) * exp (-π‖x‖²)`. -/
lemma exp_neg_le_gauss {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (he : ∀ x, f (-x) = f x)
    (hconv : ConvexOn ℝ Set.univ (fun x => f x - Real.pi * ‖x‖ ^ 2)) (x : E) :
    Real.exp (-(f x)) ≤ Real.exp (-(f 0)) * Real.exp (-(Real.pi * ‖x‖ ^ 2)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have := pi_mul_norm_sq_add_le f he hconv x
  linarith

/-- Integrability of `Φ x * exp (-f x)` when `Φ` has polynomial growth. -/
lemma integrable_mul_exp_neg_of_pow_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {f Φ : E → ℝ} (hf : Continuous f) (he : ∀ x, f (-x) = f x)
    (hconv : ConvexOn ℝ Set.univ (fun x => f x - Real.pi * ‖x‖ ^ 2))
    (hΦ : AEStronglyMeasurable Φ volume) (C : ℝ) (N : ℕ)
    (h : ∀ x, |Φ x| ≤ C * (1 + ‖x‖) ^ N) :
    Integrable (fun x => Φ x * Real.exp (-(f x))) volume := by
  have hbase : Integrable (fun x : E => (1 + ‖x‖) ^ N * Real.exp (-(Real.pi) * ‖x‖ ^ 2))
      volume := Commons.Analysis.Asymptotics.integrable_pow_mul_exp_neg_sq Real.pi Real.pi_pos N
  have hdom : Integrable (fun x : E => (|C| * Real.exp (-(f 0))) *
      ((1 + ‖x‖) ^ N * Real.exp (-(Real.pi) * ‖x‖ ^ 2))) volume := hbase.const_mul _
  refine hdom.mono' (hΦ.mul (by fun_prop)) ?_
  filter_upwards with x
  have hx1 : |Φ x| ≤ |C| * (1 + ‖x‖) ^ N := by
    have h0 : (0:ℝ) ≤ (1 + ‖x‖) ^ N := by positivity
    calc |Φ x| ≤ C * (1 + ‖x‖) ^ N := h x
      _ ≤ |C| * (1 + ‖x‖) ^ N := mul_le_mul_of_nonneg_right (le_abs_self C) h0
  have hx2 : Real.exp (-(f x)) ≤ Real.exp (-(f 0)) * Real.exp (-(Real.pi * ‖x‖ ^ 2)) :=
    exp_neg_le_gauss f he hconv x
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc |Φ x| * Real.exp (-(f x))
      ≤ (|C| * (1 + ‖x‖) ^ N) * (Real.exp (-(f 0)) * Real.exp (-(Real.pi * ‖x‖ ^ 2))) :=
        mul_le_mul hx1 hx2 (Real.exp_pos _).le (by positivity)
    _ = (|C| * Real.exp (-(f 0))) * ((1 + ‖x‖) ^ N * Real.exp (-(Real.pi) * ‖x‖ ^ 2)) := by ring_nf

/-! ## The even mollifier -/

/-- The even bump of radius `2/(k+1)` around `0`. -/
private def bump (n k : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
  ⟨((k : ℝ) + 1)⁻¹, 2 * ((k : ℝ) + 1)⁻¹, by positivity, by
    have h : (0 : ℝ) < ((k : ℝ) + 1)⁻¹ := by positivity
    linarith⟩

/-- The normalised kernel `kern n k`. -/
private def kern (n k : ℕ) : EuclideanSpace ℝ (Fin n) → ℝ := (bump n k).normed volume

private lemma kern_contDiff (n k : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (kern n k) :=
  ContDiffBump.contDiff_normed (bump n k)

private lemma kern_hasCompactSupport (n k : ℕ) : HasCompactSupport (kern n k) :=
  ContDiffBump.hasCompactSupport_normed (bump n k)

private lemma kern_neg (n k : ℕ) (x : EuclideanSpace ℝ (Fin n)) : kern n k (-x) = kern n k x :=
  ContDiffBump.normed_neg (bump n k) x

private lemma kern_nonneg (n k : ℕ) (x : EuclideanSpace ℝ (Fin n)) : 0 ≤ kern n k x :=
  ContDiffBump.nonneg_normed (bump n k) x

private lemma kern_integral (n k : ℕ) : ∫ x, kern n k x = 1 :=
  ContDiffBump.integral_normed (bump n k)

private lemma kern_tsupport (n k : ℕ) :
    tsupport (kern n k) = Metric.closedBall 0 (2 * ((k : ℝ) + 1)⁻¹) := by
  rw [kern, ContDiffBump.tsupport_normed_eq]
  rfl

private lemma kern_rOut_tendsto (n : ℕ) :
    Tendsto (fun k : ℕ => (bump n k).rOut) atTop (𝓝 0) := by
  have h1 : Tendsto (fun k : ℕ => ((k : ℝ) + 1)) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp h1
  have h3 : Tendsto (fun k : ℕ => 2 * ((k : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa using h2.const_mul (2:ℝ)
  refine h3.congr' ?_
  filter_upwards with k
  simp [bump]

/-- The mollification of `u` by `kern n k`. -/
private def moll (n k : ℕ) (u : EuclideanSpace ℝ (Fin n) → ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun x => ∫ t, u t * kern n k (x - t)

/-! ## The gradient and the mollification properties -/

private def gradF {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
  fun t => (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ u t)

private lemma inner_gradF {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (t v : EuclideanSpace ℝ (Fin n)) : ⟪gradF u t, v⟫_ℝ = fderiv ℝ u t v :=
  InnerProductSpace.toDual_symm_apply

private lemma continuous_gradF {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ) (hu : ContDiff ℝ 1 u) :
    Continuous (gradF u) :=
  (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.comp
    (hu.continuous_fderiv (by norm_num))

private lemma moll_eq_conv {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ) (k : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    moll n k u x = (kern n k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x := by
  have hfun : (fun z : EuclideanSpace ℝ (Fin n) => u z * kern n k (x - z))
      = fun z => u z * kern n k (z - x) := by
    funext z
    rw [show x - z = -(z - x) by abel, kern_neg]
  rw [show moll n k u x = ∫ z, u z * kern n k (x - z) from rfl, hfun]
  exact Commons.Measure.Mollification.mollify_eq_convolution u (bump n k) x

private lemma moll_contDiff {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (hu : LocallyIntegrable u volume) (k : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (moll n k u) := by
  have heq : moll n k u
      = fun x => (kern n k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x := by
    funext x
    exact moll_eq_conv u k x
  rw [heq]
  exact (kern_hasCompactSupport n k).contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (kern_contDiff n k) hu

private lemma moll_even {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (heven : ∀ x, u (-x) = u x) (k : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    moll n k u (-x) = moll n k u x := by
  have h1 : ∀ t, u t * kern n k (-x - t) = u t * kern n k (x + t) := by
    intro t
    rw [show -x - t = -(x + t) by abel, kern_neg]
  have h2 : ∀ t, u (-t) * kern n k (x + -t) = u t * kern n k (x - t) := by
    intro t
    rw [heven t, sub_eq_add_neg]
  calc moll n k u (-x)
      = ∫ t, u t * kern n k (-x - t) := rfl
    _ = ∫ t, u t * kern n k (x + t) := integral_congr_ae (Eventually.of_forall h1)
    _ = ∫ t, u (-t) * kern n k (x + -t) :=
        (integral_neg_eq_self (fun t => u t * kern n k (x + t)) volume).symm
    _ = ∫ t, u t * kern n k (x - t) := integral_congr_ae (Eventually.of_forall h2)
    _ = moll n k u x := rfl

/-- The support of the reflected kernel is contained in a ball of radius `rOut`. -/
private lemma tsupport_kern_sub_subset {n k : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    tsupport (fun t : EuclideanSpace ℝ (Fin n) => kern n k (x - t))
      ⊆ Metric.closedBall x (bump n k).rOut := by
  intro t ht
  have ht' : x - t ∈ tsupport (kern n k) :=
    Commons.Analysis.Convolution.tsupport_comp_sub_subset (kern n k) x ht
  rw [kern_tsupport, Metric.mem_closedBall, dist_eq_norm, sub_zero] at ht'
  rw [Metric.mem_closedBall, dist_eq_norm]
  rw [show t - x = -(x - t) by abel, norm_neg]
  simpa [bump] using ht'

private lemma continuous_kern_comp {n k : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    Continuous (fun t : EuclideanSpace ℝ (Fin n) => kern n k (x - t)) :=
  (kern_contDiff n k).continuous.comp (continuous_const.sub continuous_id)

private lemma hasCompactSupport_kern_comp {n k : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    HasCompactSupport (fun t : EuclideanSpace ℝ (Fin n) => kern n k (x - t)) :=
  (isCompact_closedBall x (bump n k).rOut).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_kern_sub_subset x)

/-- Integration by parts instance: for a `C¹` function `u` and a smooth compactly supported
`φ`, `∫ u ∂φ = -∫ ∂u φ` (the weak-gradient condition for `gradF u`). -/
private lemma ibp_contDiff {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ) (hu : ContDiff ℝ 1 u)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (v : EuclideanSpace ℝ (Fin n)) :
    ∫ y, u y * (fderiv ℝ φ y) v = -∫ y, φ y * ⟪gradF u y, v⟫_ℝ := by
  have hdu : Continuous (fun y => (fderiv ℝ u y) v) :=
    (hu.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hint1 : Integrable (fun y => (fderiv ℝ u y) v * φ y) volume :=
    (hdu.mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left
  have hint2 : Integrable (fun y => u y * (fderiv ℝ φ y) v) volume := by
    have hc : Continuous (fun y => u y * (fderiv ℝ φ y) v) :=
      hu.continuous.mul ((hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const)
    exact hc.integrable_of_hasCompactSupport (hφc.fderiv_apply ℝ v).mul_left
  have hint3 : Integrable (fun y => u y * φ y) volume :=
    (hu.continuous.mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := u) (g := φ) (v := v) hint1 hint2 hint3
    (fun y _ => hu.contDiffAt.differentiableAt (by norm_num))
    (fun y _ => hφ.contDiffAt.differentiableAt (by norm_num))
  rw [h, neg_inj]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only []
  rw [inner_gradF]
  ring

private lemma fderiv_moll_eq {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ) (hu : ContDiff ℝ 1 u)
    (k : ℕ) (x v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (moll n k u) x v = ∫ t, kern n k (x - t) * fderiv ℝ u t v := by
  have huloc : LocallyIntegrable u volume := hu.continuous.locallyIntegrable
  have hGloc : LocallyIntegrable (gradF u) volume := (continuous_gradF u hu).locallyIntegrable
  have hksupp : ∀ z ∈ tsupport (kern n k), (x - z) ∈ Metric.closedBall x (bump n k).rOut := by
    intro z hz
    rw [kern_tsupport, Metric.mem_closedBall, dist_eq_norm, sub_zero] at hz
    rw [Metric.mem_closedBall, dist_eq_norm]
    rw [show (x - z) - x = -z by abel, norm_neg]
    simpa [bump] using hz
  have hG : ∀ (φ : EuclideanSpace ℝ (Fin n) → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ →
      tsupport φ ⊆ Metric.closedBall x (bump n k).rOut → ∀ v,
      ∫ y, u y * (fderiv ℝ φ y) v = -∫ y, φ y * ⟪gradF u y, v⟫_ℝ := by
    intro φ hφ hsupp v
    have hφc : HasCompactSupport φ :=
      (isCompact_closedBall x (bump n k).rOut).of_isClosed_subset (isClosed_tsupport φ) hsupp
    exact ibp_contDiff u hu hφ hφc v
  have hmain := Commons.Analysis.Convolution.fderiv_moll_weakGrad (kern n k) u (gradF u)
    (Metric.closedBall x (bump n k).rOut) x (kern_contDiff n k) (kern_hasCompactSupport n k)
    huloc hGloc hksupp hG v
  change (fderiv ℝ (fun y => ∫ t, u t * kern n k (y - t)) x) v = _
  rw [hmain]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only []
  rw [inner_gradF]

/-- Swapping the roles in `fderiv (fun y => fderiv u y w) x v`. -/
private lemma fderiv_fderiv_apply {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (hu : ContDiff ℝ 2 u) (x v w : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun y => fderiv ℝ u y w) x v = fderiv ℝ (fderiv ℝ u) x v w := by
  have hd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    ((hu.fderiv_right (m := 1) (by norm_num)).contDiffAt).differentiableAt (by norm_num)
  rw [fderiv_clm_apply (c := fderiv ℝ u)
    (u := fun _ : EuclideanSpace ℝ (Fin n) => w) hd (differentiableAt_const w)]
  simp [ContinuousLinearMap.flip_apply]

private lemma fderiv_fderiv_moll_eq {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (hu : ContDiff ℝ 2 u) (k : ℕ) (x v w : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fderiv ℝ (moll n k u)) x v w
      = ∫ t, kern n k (x - t) * fderiv ℝ (fderiv ℝ u) t v w := by
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hU1 : ContDiff ℝ 1 (fun t : EuclideanSpace ℝ (Fin n) => fderiv ℝ u t w) :=
    (hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hL1 := fderiv_moll_eq (fun t : EuclideanSpace ℝ (Fin n) => fderiv ℝ u t w) hU1 k x v
  have hfeq : moll n k (fun t : EuclideanSpace ℝ (Fin n) => fderiv ℝ u t w)
      = fun x' => fderiv ℝ (moll n k u) x' w := by
    funext x'
    rw [show moll n k (fun t => fderiv ℝ u t w) x'
        = ∫ t, (fderiv ℝ u t w) * kern n k (x' - t) from rfl]
    rw [fderiv_moll_eq u hu1 k x' w]
    exact integral_congr_ae (Eventually.of_forall fun t => by ring)
  have hid1 : fderiv ℝ (moll n k (fun t => fderiv ℝ u t w)) x v
      = fderiv ℝ (fderiv ℝ (moll n k u)) x v w := by
    rw [hfeq]
    exact fderiv_fderiv_apply (moll n k u)
      ((moll_contDiff u hu.continuous.locallyIntegrable k).of_le (WithTop.coe_le_coe.mpr le_top)) x v w
  rw [← hid1, hL1]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only []
  rw [fderiv_fderiv_apply u hu t v w]

/-! ### A polarization bound for symmetric bilinear forms -/

/-- A symmetric bilinear form bounded on the diagonal is bounded: `|B v w| ≤ M‖v‖‖w‖`. -/
private lemma bilinear_bound_of_diag {n : ℕ}
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
    {M : ℝ} (hM : 0 ≤ M) (hdiag : ∀ v, |B v v| ≤ M * ‖v‖ ^ 2)
    (hsym : ∀ v w, B v w = B w v) (v w : EuclideanSpace ℝ (Fin n)) :
    |B v w| ≤ M * ‖v‖ * ‖w‖ := by
  have hgen : ∀ a b : EuclideanSpace ℝ (Fin n),
      |B a b| ≤ (M / 2) * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
    intro a b
    have h1 : B (a + b) (a + b) = B a a + B a b + B b a + B b b := by
      simp only [map_add, ContinuousLinearMap.add_apply]; ring
    have h2 : B (a - b) (a - b) = B a a - B a b - B b a + B b b := by
      simp only [map_sub, ContinuousLinearMap.sub_apply]; ring
    have hkey : B a b = (1 / 4) * (B (a + b) (a + b) - B (a - b) (a - b)) := by
      rw [h1, h2, hsym a b]; ring
    have hb1 := hdiag (a + b)
    have hb2 := hdiag (a - b)
    have hpar : ‖a + b‖ ^ 2 + ‖a - b‖ ^ 2 = 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) :=
      parallelogram_law_with_norm ℝ a b
    rw [hkey]
    calc |(1 / 4) * (B (a + b) (a + b) - B (a - b) (a - b))|
        = (1 / 4) * |B (a + b) (a + b) - B (a - b) (a - b)| := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)]
      _ ≤ (1 / 4) * (|B (a + b) (a + b)| + |B (a - b) (a - b)|) :=
          mul_le_mul_of_nonneg_left (abs_sub _ _) (by norm_num)
      _ ≤ (1 / 4) * (M * ‖a + b‖ ^ 2 + M * ‖a - b‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (add_le_add hb1 hb2) (by norm_num)
      _ = (M / 2) * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by nlinarith [hpar]
  rcases eq_or_ne v 0 with hv | hv
  · rw [hv]; simp
  rcases eq_or_ne w 0 with hw | hw
  · rw [hw, map_zero]; simp
  have hnv : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hv
  have hnw : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
  set t : ℝ := Real.sqrt (‖w‖ / ‖v‖) with htdef
  have htpos : 0 < t := Real.sqrt_pos.mpr (div_pos hnw hnv)
  have ht2 : t ^ 2 = ‖w‖ / ‖v‖ := Real.sq_sqrt (div_nonneg hnw.le hnv.le)
  have hscale : B (t • v) (t⁻¹ • w) = B v w := by
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ htpos.ne', one_mul]
  have h := hgen (t • v) (t⁻¹ • w)
  rw [hscale] at h
  have hn1 : ‖t • v‖ ^ 2 = ‖w‖ * ‖v‖ := by
    rw [norm_smul, Real.norm_of_nonneg htpos.le, mul_pow, ht2]
    field_simp
  have hn2 : ‖t⁻¹ • w‖ ^ 2 = ‖v‖ * ‖w‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr htpos.le), mul_pow,
      inv_pow, ht2]
    field_simp
  rw [hn1, hn2] at h
  linarith [h, hM]

/-- Bound for the convolution of a polynomially growing function against a compactly supported
kernel. -/
private lemma abs_integral_support_mul_le {n : ℕ} {K g : EuclideanSpace ℝ (Fin n) → ℝ}
    {R : ℝ} (hR : 0 ≤ R) (hKcont : Continuous K) (hKc : HasCompactSupport K)
    (hKsupp : ∀ t, K t ≠ 0 → t ∈ Metric.closedBall 0 R)
    {C : ℝ} (hC : 0 ≤ C) {N : ℕ} (hg : ∀ t, |g t| ≤ C * (1 + ‖t‖) ^ N)
    (hgcont : Continuous g) (x : EuclideanSpace ℝ (Fin n)) :
    |∫ t, K (x - t) * g t| ≤ (∫ t, |K t|) * C * (1 + ‖x‖ + R) ^ N := by
  have hts : tsupport K ⊆ Metric.closedBall 0 R :=
    closure_minimal (fun t ht => hKsupp t (Function.mem_support.mp ht)) Metric.isClosed_closedBall
  have hcompKx : HasCompactSupport (fun t : EuclideanSpace ℝ (Fin n) => K (x - t)) := by
    refine (isCompact_closedBall x R).of_isClosed_subset (isClosed_tsupport _) ?_
    intro t ht
    have ht' : x - t ∈ tsupport K := Commons.Analysis.Convolution.tsupport_comp_sub_subset K x ht
    have h2 := hts ht'
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h2
    rw [Metric.mem_closedBall, dist_eq_norm]
    rw [show t - x = -(x - t) by abel, norm_neg]
    exact h2
  have hcont1 : Continuous (fun t : EuclideanSpace ℝ (Fin n) => K (x - t) * g t) :=
    (hKcont.comp (continuous_const.sub continuous_id)).mul hgcont
  have hint1 : Integrable (fun t : EuclideanSpace ℝ (Fin n) => K (x - t) * g t) volume :=
    hcont1.integrable_of_hasCompactSupport (hcompKx.mul_right)
  have hint2 : Integrable (fun t : EuclideanSpace ℝ (Fin n) =>
      |K (x - t)| * (C * (1 + ‖x‖ + R) ^ N)) volume :=
    (((hKcont.comp (continuous_const.sub continuous_id)).abs).mul continuous_const)
      |>.integrable_of_hasCompactSupport ((hcompKx.abs).mul_right)
  have hpt : ∀ t, |K (x - t) * g t| ≤ |K (x - t)| * (C * (1 + ‖x‖ + R) ^ N) := by
    intro t
    rw [abs_mul]
    by_cases hkt : K (x - t) = 0
    · rw [hkt, abs_zero, zero_mul, zero_mul]
    · have hmem : t ∈ Metric.closedBall x R := by
        have h1 := hKsupp (x - t) hkt
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h1
        rw [Metric.mem_closedBall, dist_eq_norm]
        rw [show t - x = -(x - t) by abel, norm_neg]
        exact h1
      have htn : ‖t‖ ≤ ‖x‖ + R := by
        have h1 : ‖t - x‖ ≤ R := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using hmem
        calc ‖t‖ = ‖(t - x) + x‖ := by rw [sub_add_cancel]
          _ ≤ ‖t - x‖ + ‖x‖ := norm_add_le _ _
          _ ≤ R + ‖x‖ := by linarith
          _ = ‖x‖ + R := by ring
      have hg' : |g t| ≤ C * (1 + ‖x‖ + R) ^ N :=
        (hg t).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) (by linarith) N) hC)
      exact mul_le_mul_of_nonneg_left hg' (abs_nonneg _)
  have hsub : (∫ t, |K (x - t)|) = ∫ t, |K t| := by
    rw [show (fun t : EuclideanSpace ℝ (Fin n) => |K (x - t)|)
        = fun t => (fun s => |K (-s)|) (t - x) from by
      funext t; rw [show x - t = -(t - x) by abel]]
    exact (integral_sub_right_eq_self (fun s => |K (-s)|) x).trans
      (integral_neg_eq_self (fun s => |K s|) volume)
  calc |∫ t, K (x - t) * g t|
      ≤ ∫ t, |K (x - t) * g t| := abs_integral_le_integral_abs
    _ ≤ ∫ t, |K (x - t)| * (C * (1 + ‖x‖ + R) ^ N) :=
        integral_mono hint1.abs hint2 hpt
    _ = (C * (1 + ‖x‖ + R) ^ N) * ∫ t, |K (x - t)| := by
        rw [integral_mul_const]; ring
    _ = (C * (1 + ‖x‖ + R) ^ N) * ∫ t, |K t| := by rw [hsub]
    _ = (∫ t, |K t|) * C * (1 + ‖x‖ + R) ^ N := by ring

/-- Identity for the third derivative: the differentiation direction is the first slot. -/
private lemma fderiv3_apply {n : ℕ} (v : EuclideanSpace ℝ (Fin n) → ℝ) (hv : ContDiff ℝ 3 v)
    (x v1 w z : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun y => fderiv ℝ (fderiv ℝ v) y w z) x v1
      = fderiv ℝ (fderiv ℝ (fderiv ℝ v)) x v1 w z := by
  have hd1 : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ v)) x := by
    have hC : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ v)) :=
      (hv.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)
    exact hC.contDiffAt.differentiableAt (by norm_num)
  have h1 : fderiv ℝ (fun y => fderiv ℝ (fderiv ℝ v) y w) x
      = (fderiv ℝ (fderiv ℝ (fderiv ℝ v)) x).flip w := by
    rw [fderiv_clm_apply (c := fderiv ℝ (fderiv ℝ v))
      (u := fun _ : EuclideanSpace ℝ (Fin n) => w) hd1 (differentiableAt_const w)]
    ext a; simp [ContinuousLinearMap.flip_apply]
  have hd2 : DifferentiableAt ℝ (fun y => fderiv ℝ (fderiv ℝ v) y w) x :=
    hd1.clm_apply (differentiableAt_const w)
  have h2 : fderiv ℝ (fun y => fderiv ℝ (fderiv ℝ v) y w z) x
      = (fderiv ℝ (fun y => fderiv ℝ (fderiv ℝ v) y w) x).flip z := by
    rw [fderiv_clm_apply (c := fun y => fderiv ℝ (fderiv ℝ v) y w)
      (u := fun _ : EuclideanSpace ℝ (Fin n) => z) hd2 (differentiableAt_const z)]
    ext a; simp [ContinuousLinearMap.flip_apply]
  rw [h2, h1]
  simp [ContinuousLinearMap.flip_apply]

/-- The bound for a convolution against `kern n k`. -/
private lemma abs_integral_kern_mul_le {n k : ℕ} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hgcont : Continuous g) {C : ℝ} (hC : 0 ≤ C) {N : ℕ}
    (hg : ∀ t, |g t| ≤ C * (1 + ‖t‖) ^ N) (x : EuclideanSpace ℝ (Fin n)) :
    |∫ t, kern n k (x - t) * g t| ≤ C * (1 + ‖x‖ + (bump n k).rOut) ^ N := by
  have hrOut : 0 ≤ (bump n k).rOut := (bump n k).rOut_pos.le
  have hKsupp : ∀ t, kern n k t ≠ 0 → t ∈ Metric.closedBall 0 (bump n k).rOut := by
    intro t ht
    have h2 : t ∈ tsupport (kern n k) := subset_tsupport _ ht
    rw [kern_tsupport] at h2
    simpa [bump] using h2
  have h := abs_integral_support_mul_le (K := kern n k) (g := g) (R := (bump n k).rOut) hrOut
    (kern_contDiff n k).continuous (kern_hasCompactSupport n k) hKsupp hC hg hgcont x
  have hKint : (∫ t, |kern n k t|) = 1 := by
    rw [show (fun t => |kern n k t|) = kern n k from by
      funext t; rw [abs_of_nonneg (kern_nonneg n k t)]]
    exact kern_integral n k
  rw [hKint, one_mul] at h
  exact h

private lemma moll_growth {n k : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ} (huc : Continuous u)
    {C : ℝ} (hC : 0 ≤ C) {N : ℕ} (hu : ∀ t, |u t| ≤ C * (1 + ‖t‖) ^ N)
    (x : EuclideanSpace ℝ (Fin n)) :
    |moll n k u x| ≤ C * (1 + ‖x‖ + (bump n k).rOut) ^ N := by
  have h1 : moll n k u x = ∫ t, kern n k (x - t) * u t := by
    rw [show moll n k u x = ∫ t, u t * kern n k (x - t) from rfl]
    exact integral_congr_ae (Eventually.of_forall fun t => by ring)
  rw [h1]
  exact abs_integral_kern_mul_le huc hC hu x

private lemma fderiv_moll_growth {n k : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) {C : ℝ} (hC : 0 ≤ C) {N : ℕ}
    (hg : ∀ t v, |fderiv ℝ u t v| ≤ C * (1 + ‖t‖) ^ N * ‖v‖)
    (x v : EuclideanSpace ℝ (Fin n)) :
    |fderiv ℝ (moll n k u) x v| ≤ C * (1 + ‖x‖ + (bump n k).rOut) ^ N * ‖v‖ := by
  rw [fderiv_moll_eq u hu k x v]
  have h := abs_integral_kern_mul_le (k := k) (n := n) ((hu.continuous_fderiv (by norm_num)).clm_apply continuous_const)
    (mul_nonneg hC (norm_nonneg v)) (fun t => by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hg t v) x
  convert h using 1
  ring

private lemma fderiv_fderiv_moll_growth {n k : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 2 u) {C : ℝ} (hC : 0 ≤ C) {N : ℕ}
    (hg : ∀ t v w, |fderiv ℝ (fderiv ℝ u) t v w| ≤ C * (1 + ‖t‖) ^ N * ‖v‖ * ‖w‖)
    (x v w : EuclideanSpace ℝ (Fin n)) :
    |fderiv ℝ (fderiv ℝ (moll n k u)) x v w|
      ≤ C * (1 + ‖x‖ + (bump n k).rOut) ^ N * ‖v‖ * ‖w‖ := by
  rw [fderiv_fderiv_moll_eq u hu k x v w]
  have h := abs_integral_kern_mul_le (k := k) (n := n)
    ((((hu.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)).clm_apply
      continuous_const).clm_apply continuous_const)
    (mul_nonneg (mul_nonneg hC (norm_nonneg v)) (norm_nonneg w)) (fun t => by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hg t v w) x
  convert h using 1
  ring

/-! ### Derived compactness and smoothness facts for the kernel -/

private lemma kern_fderiv_cs (n k : ℕ) : HasCompactSupport (fderiv ℝ (kern n k)) :=
  (kern_hasCompactSupport n k).fderiv ℝ

private lemma kern_fderiv_infty (n k : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (kern n k)) :=
  (contDiff_infty_iff_fderiv.mp (kern_contDiff n k)).2

private lemma kern_fderiv_fderiv_infty (n k : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (fderiv ℝ (kern n k))) :=
  (contDiff_infty_iff_fderiv.mp (kern_fderiv_infty n k)).2

private lemma kern_fderiv_fderiv_cs (n k : ℕ) :
    HasCompactSupport (fderiv ℝ (fderiv ℝ (kern n k))) :=
  (kern_fderiv_cs n k).fderiv ℝ

private lemma kern_fderiv_fderiv_cont (n k : ℕ) :
    Continuous (fderiv ℝ (fderiv ℝ (kern n k))) :=
  (kern_fderiv_fderiv_infty n k).continuous

private lemma kern_fderiv_fderiv_norm_cont (n k : ℕ) :
    Continuous (fun t : EuclideanSpace ℝ (Fin n) => ‖fderiv ℝ (fderiv ℝ (kern n k)) t‖) :=
  ((contDiff_infty_iff_fderiv.mp (contDiff_infty_iff_fderiv.mp (kern_contDiff n k)).2).2).continuous.norm

private lemma kern_fderiv_fderiv_norm_cs (n k : ℕ) :
    HasCompactSupport (fun t : EuclideanSpace ℝ (Fin n) =>
      ‖fderiv ℝ (fderiv ℝ (kern n k)) t‖) :=
  (((kern_hasCompactSupport n k).fderiv ℝ).fderiv ℝ).comp_left
    (g := fun (A : EuclideanSpace ℝ (Fin n) →L[ℝ] (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) => ‖A‖)
    (by exact ContinuousLinearMap.opNorm_zero)

private lemma kern_fderiv_fderiv_apply_sm (n k : ℕ) (w z : EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun s => fderiv ℝ (fderiv ℝ (kern n k)) s w z) :=
  ((kern_fderiv_fderiv_infty n k).clm_apply contDiff_const).clm_apply contDiff_const

private lemma kern_fderiv_fderiv_apply_cs (n k : ℕ) (w z : EuclideanSpace ℝ (Fin n)) :
    HasCompactSupport (fun s => fderiv ℝ (fderiv ℝ (kern n k)) s w z) :=
  ((kern_fderiv_fderiv_cs n k).comp_left
    (g := fun (A : EuclideanSpace ℝ (Fin n) →L[ℝ] (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) => A w)
    (by simp)).comp_left (g := fun (A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) => A z) (by simp)

private lemma kern_fderiv_fderiv_apply_cont (n k : ℕ) (w z : EuclideanSpace ℝ (Fin n)) :
    Continuous (fun s => fderiv ℝ (fderiv ℝ (kern n k)) s w z) :=
  ((kern_fderiv_fderiv_cont n k).clm_apply continuous_const).clm_apply continuous_const

private lemma third_deriv_moll_growth {n k : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 2 u) {C : ℝ} (hC : 0 ≤ C) {N : ℕ}
    (hg : ∀ t v, |fderiv ℝ u t v| ≤ C * (1 + ‖t‖) ^ N * ‖v‖)
    (x v w z : EuclideanSpace ℝ (Fin n)) :
    |fderiv ℝ (fderiv ℝ (fderiv ℝ (moll n k u))) x v w z|
      ≤ (∫ s, ‖fderiv ℝ (fderiv ℝ (kern n k)) s‖) * C
          * (1 + ‖x‖ + (bump n k).rOut) ^ N * ‖v‖ * ‖w‖ * ‖z‖ := by
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have huloc : LocallyIntegrable u volume := hu.continuous.locallyIntegrable
  have hu3 : ContDiff ℝ 3 (moll n k u) :=
    (moll_contDiff u huloc k).of_le (WithTop.coe_le_coe.mpr le_top)
  have hts : tsupport (fderiv ℝ (fderiv ℝ (kern n k))) ⊆ tsupport (kern n k) :=
    (tsupport_fderiv_subset ℝ).trans (tsupport_fderiv_subset ℝ)
  have hts' : tsupport (fun s : EuclideanSpace ℝ (Fin n) => fderiv ℝ (fderiv ℝ (kern n k)) s w z)
      ⊆ tsupport (fderiv ℝ (fderiv ℝ (kern n k))) :=
    closure_mono (fun s hs => by
      rw [Function.mem_support] at hs ⊢
      intro hcon
      exact hs (by rw [hcon]; simp))
  have hk'supp : ∀ t, (fun s : EuclideanSpace ℝ (Fin n) =>
        fderiv ℝ (fderiv ℝ (kern n k)) s w z) t ≠ 0
      → t ∈ Metric.closedBall 0 (bump n k).rOut := by
    intro t ht
    have h5 := hts (hts' (subset_tsupport _ (Function.mem_support.mpr ht)))
    rw [kern_tsupport, Metric.mem_closedBall, dist_eq_norm, sub_zero] at h5
    simpa [bump] using h5
  have hksupp : ∀ t ∈ tsupport
      (fun s : EuclideanSpace ℝ (Fin n) => fderiv ℝ (fderiv ℝ (kern n k)) s w z),
      (x - t) ∈ Metric.closedBall x (bump n k).rOut := by
    intro t ht
    have h5 := hts (hts' ht)
    rw [kern_tsupport, Metric.mem_closedBall, dist_eq_norm, sub_zero] at h5
    rw [Metric.mem_closedBall, dist_eq_norm]
    rw [show (x - t) - x = -t by abel, norm_neg]
    simpa [bump] using h5
  have hD2 : ∀ y : EuclideanSpace ℝ (Fin n),
      fderiv ℝ (fderiv ℝ (moll n k u)) y w z
        = ∫ t, u t * (fderiv ℝ (fderiv ℝ (kern n k)) (y - t) w z) := by
    intro y
    exact Commons.Analysis.Convolution.fderiv_fderiv_moll_apply (kern n k) u y w z
      (kern_hasCompactSupport n k) (kern_contDiff n k) huloc
  have hG : ∀ (φ : EuclideanSpace ℝ (Fin n) → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ →
      tsupport φ ⊆ Metric.closedBall x (bump n k).rOut → ∀ v',
      ∫ y, u y * (fderiv ℝ φ y) v' = -∫ y, φ y * ⟪gradF u y, v'⟫_ℝ := by
    intro φ hφ hsupp v'
    have hφc : HasCompactSupport φ :=
      (isCompact_closedBall x (bump n k).rOut).of_isClosed_subset (isClosed_tsupport φ) hsupp
    exact ibp_contDiff u hu1 hφ hφc v'
  have hmain := Commons.Analysis.Convolution.fderiv_moll_weakGrad
    (fun s : EuclideanSpace ℝ (Fin n) => fderiv ℝ (fderiv ℝ (kern n k)) s w z) u (gradF u)
    (Metric.closedBall x (bump n k).rOut) x (kern_fderiv_fderiv_apply_sm n k w z)
    (kern_fderiv_fderiv_apply_cs n k w z) huloc
    (continuous_gradF u hu1).locallyIntegrable hksupp hG v
  have hident : fderiv ℝ (fderiv ℝ (fderiv ℝ (moll n k u))) x v w z
      = (fderiv ℝ (fun y => ∫ t, u t *
          (fderiv ℝ (fderiv ℝ (kern n k)) (y - t) w z)) x) v := by
    rw [← fderiv3_apply (moll n k u) hu3 x v w z]
    have heq : (fun y => fderiv ℝ (fderiv ℝ (moll n k u)) y w z)
        = fun y => ∫ t, u t * (fderiv ℝ (fderiv ℝ (kern n k)) (y - t) w z) :=
      funext hD2
    rw [heq]
  have hKint_le : (∫ t, |fderiv ℝ (fderiv ℝ (kern n k)) t w z|)
      ≤ ‖w‖ * ‖z‖ * (∫ t, ‖fderiv ℝ (fderiv ℝ (kern n k)) t‖) := by
    have h1 : Integrable (fun t => |fderiv ℝ (fderiv ℝ (kern n k)) t w z|) volume :=
      ((kern_fderiv_fderiv_apply_cont n k w z).abs.integrable_of_hasCompactSupport
        (kern_fderiv_fderiv_apply_cs n k w z).abs)
    have h2 : Integrable (fun t => ‖w‖ * ‖z‖ * ‖fderiv ℝ (fderiv ℝ (kern n k)) t‖) volume :=
      ((kern_fderiv_fderiv_norm_cont n k).integrable_of_hasCompactSupport
        (kern_fderiv_fderiv_norm_cs n k)).const_mul _
    calc (∫ t, |fderiv ℝ (fderiv ℝ (kern n k)) t w z|)
        ≤ ∫ t, ‖w‖ * ‖z‖ * ‖fderiv ℝ (fderiv ℝ (kern n k)) t‖ :=
          integral_mono h1 h2 (fun t => by
            calc |fderiv ℝ (fderiv ℝ (kern n k)) t w z|
                ≤ ‖fderiv ℝ (fderiv ℝ (kern n k)) t w‖ * ‖z‖ := by
                  simpa [Real.norm_eq_abs] using ContinuousLinearMap.le_opNorm
                    (fderiv ℝ (fderiv ℝ (kern n k)) t w) z
              _ ≤ (‖fderiv ℝ (fderiv ℝ (kern n k)) t‖ * ‖w‖) * ‖z‖ := by
                  gcongr
                  simpa [Real.norm_eq_abs] using ContinuousLinearMap.le_opNorm
                    (fderiv ℝ (fderiv ℝ (kern n k)) t) w
              _ = ‖w‖ * ‖z‖ * ‖fderiv ℝ (fderiv ℝ (kern n k)) t‖ := by ring)
      _ = ‖w‖ * ‖z‖ * ∫ t, ‖fderiv ℝ (fderiv ℝ (kern n k)) t‖ := integral_const_mul _ _
  have hbase := abs_integral_support_mul_le
    (K := fun s : EuclideanSpace ℝ (Fin n) => fderiv ℝ (fderiv ℝ (kern n k)) s w z)
    (g := fun t : EuclideanSpace ℝ (Fin n) => fderiv ℝ u t v) (R := (bump n k).rOut)
    (bump n k).rOut_pos.le
    (kern_fderiv_fderiv_apply_cont n k w z) (kern_fderiv_fderiv_apply_cs n k w z) hk'supp
    (mul_nonneg hC (norm_nonneg v)) (fun t => by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hg t v)
    ((hu.continuous_fderiv (by norm_num)).clm_apply continuous_const) x
  rw [hident, hmain]
  simp only [inner_gradF]
  have hstep2 : (∫ t, |fderiv ℝ (fderiv ℝ (kern n k)) t w z|) * (C * ‖v‖)
        * (1 + ‖x‖ + (bump n k).rOut) ^ N
      ≤ (‖w‖ * ‖z‖ * (∫ t, ‖fderiv ℝ (fderiv ℝ (kern n k)) t‖)) * (C * ‖v‖)
        * (1 + ‖x‖ + (bump n k).rOut) ^ N := by
    rw [show (∫ t, |fderiv ℝ (fderiv ℝ (kern n k)) t w z|) * (C * ‖v‖)
            * (1 + ‖x‖ + (bump n k).rOut) ^ N
        = (∫ t, |fderiv ℝ (fderiv ℝ (kern n k)) t w z|)
            * ((C * ‖v‖) * (1 + ‖x‖ + (bump n k).rOut) ^ N) from by ring,
      show (‖w‖ * ‖z‖ * (∫ t, ‖fderiv ℝ (fderiv ℝ (kern n k)) t‖)) * (C * ‖v‖)
            * (1 + ‖x‖ + (bump n k).rOut) ^ N
        = (‖w‖ * ‖z‖ * (∫ t, ‖fderiv ℝ (fderiv ℝ (kern n k)) t‖))
            * ((C * ‖v‖) * (1 + ‖x‖ + (bump n k).rOut) ^ N) from by ring]
    exact mul_le_mul_of_nonneg_right hKint_le
      (mul_nonneg (mul_nonneg hC (norm_nonneg v))
        (pow_nonneg (by have h := (bump n k).rOut_pos; linarith [norm_nonneg x]) N))
  calc |∫ t, (fderiv ℝ (fderiv ℝ (kern n k)) (x - t) w z) * fderiv ℝ u t v|
      ≤ (∫ t, |fderiv ℝ (fderiv ℝ (kern n k)) t w z|) * (C * ‖v‖)
          * (1 + ‖x‖ + (bump n k).rOut) ^ N := hbase
    _ ≤ (‖w‖ * ‖z‖ * (∫ t, ‖fderiv ℝ (fderiv ℝ (kern n k)) t‖)) * (C * ‖v‖)
          * (1 + ‖x‖ + (bump n k).rOut) ^ N := hstep2
    _ = (∫ s, ‖fderiv ℝ (fderiv ℝ (kern n k)) s‖) * C
          * (1 + ‖x‖ + (bump n k).rOut) ^ N * ‖v‖ * ‖w‖ * ‖z‖ := by ring

/-- The standard orthonormal basis, bundled with its index type. -/
private noncomputable def stdB (n : ℕ) :
    OrthonormalBasis (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))) ℝ
      (EuclideanSpace ℝ (Fin n)) :=
  stdOrthonormalBasis ℝ _

/-- Orthonormal-basis representation of the norm squared of a linear functional. -/
private lemma clm_norm_sq_eq_sum {n : ℕ} (L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :
    ‖L‖ ^ 2 = ∑ i, (L (stdB n i)) ^ 2 := by
  have h := OrthonormalBasis.sum_sq_inner_left (stdB n)
    ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm L)
  rw [LinearIsometryEquiv.norm_map] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [InnerProductSpace.toDual_symm_apply]

/-- The Laplacian as a sum of diagonal second derivatives. -/
private lemma laplacian_eq_sum_fderiv {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    Laplacian.laplacian u x = ∑ i, fderiv ℝ (fderiv ℝ u) x (stdB n i) (stdB n i) := by
  rw [Commons.Analysis.Calculus.FDeriv.laplacian_eq_sum_second_partials (stdB n) u x]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [bilinearIteratedFDerivTwo_eq_iteratedFDeriv, iteratedFDeriv_two_apply]
  simp

/-- The inner product of two gradients as an orthonormal-basis sum. -/
private lemma inner_grad_eq_sum {n : ℕ} (φ ψ : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    inner ℝ ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ φ x))
        ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ ψ x))
      = ∑ i, fderiv ℝ φ x (stdB n i) * fderiv ℝ ψ x (stdB n i) := by
  rw [← OrthonormalBasis.sum_inner_mul_inner (stdB n) _ _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [InnerProductSpace.toDual_symm_apply, real_inner_comm, InnerProductSpace.toDual_symm_apply]

/-- Reflection of the kernel. -/
private lemma kern_reflect {n k : ℕ} (x z : EuclideanSpace ℝ (Fin n)) :
    (bump n k).normed volume (z - x) = kern n k (x - z) := by
  rw [show z - x = -(x - z) by abel]
  exact kern_neg n k (x - z)

/-- Convergence of the mollification. -/
private lemma moll_tendsto {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ) (hu : Continuous u)
    (x : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun k => moll n k u x) atTop (𝓝 (u x)) := by
  have h := Commons.Measure.Mollification.tendsto_integral_mul_bump hu (kern_rOut_tendsto n) x
  refine h.congr' (Eventually.of_forall fun k => ?_)
  show (∫ z, u z * (bump n k).normed volume (z - x)) = moll n k u x
  rw [show moll n k u x = ∫ z, u z * kern n k (x - z) from rfl]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  show u z * (bump n k).normed volume (z - x) = u z * kern n k (x - z)
  rw [kern_reflect x z]

/-- Convergence of the derivative of the mollification. -/
private lemma fderiv_moll_tendsto {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (hu : ContDiff ℝ 2 u) (x v : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun k => fderiv ℝ (moll n k u) x v) atTop (𝓝 (fderiv ℝ u x v)) := by
  have hcont : Continuous (fun t : EuclideanSpace ℝ (Fin n) => fderiv ℝ u t v) :=
    (hu.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have h := Commons.Measure.Mollification.tendsto_integral_mul_bump hcont (kern_rOut_tendsto n) x
  refine h.congr' (Eventually.of_forall fun k => ?_)
  show (∫ z, (fderiv ℝ u z) v * (bump n k).normed volume (z - x))
      = fderiv ℝ (moll n k u) x v
  rw [fderiv_moll_eq u (hu.of_le (by norm_num)) k x v]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  show (fderiv ℝ u z) v * (bump n k).normed volume (z - x)
      = kern n k (x - z) * (fderiv ℝ u z) v
  rw [kern_reflect x z]; ring

/-- Convergence of the diagonal second derivative of the mollification. -/
private lemma fderiv_fderiv_moll_tendsto {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (hu : ContDiff ℝ 2 u) (x : EuclideanSpace ℝ (Fin n))
    (i : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))) :
    Tendsto (fun k => fderiv ℝ (fderiv ℝ (moll n k u)) x (stdB n i) (stdB n i)) atTop
      (𝓝 (fderiv ℝ (fderiv ℝ u) x (stdB n i) (stdB n i))) := by
  have hcont : Continuous (fun t : EuclideanSpace ℝ (Fin n) =>
      fderiv ℝ (fderiv ℝ u) t (stdB n i) (stdB n i)) :=
    (((hu.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)).clm_apply
      continuous_const).clm_apply continuous_const
  have h := Commons.Measure.Mollification.tendsto_integral_mul_bump hcont (kern_rOut_tendsto n) x
  refine h.congr' (Eventually.of_forall fun k => ?_)
  show (∫ z, fderiv ℝ (fderiv ℝ u) z (stdB n i) (stdB n i)
        * (bump n k).normed volume (z - x))
      = fderiv ℝ (fderiv ℝ (moll n k u)) x (stdB n i) (stdB n i)
  rw [fderiv_fderiv_moll_eq u hu k x (stdB n i) (stdB n i)]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  show fderiv ℝ (fderiv ℝ u) z (stdB n i) (stdB n i) * (bump n k).normed volume (z - x)
      = kern n k (x - z) * fderiv ℝ (fderiv ℝ u) z (stdB n i) (stdB n i)
  rw [kern_reflect x z]; ring

private lemma moll_contDiff_two {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (hu : LocallyIntegrable u volume) (k : ℕ) : ContDiff ℝ 2 (moll n k u) :=
  (moll_contDiff u hu k).of_le (WithTop.coe_le_coe.mpr le_top)

private lemma continuous_laplacian {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hφ : ContDiff ℝ 2 φ) : Continuous (fun x => Laplacian.laplacian φ x) := by
  rw [funext fun x => laplacian_eq_sum_fderiv φ x]
  exact continuous_finset_sum _ (fun i _ =>
    (((hφ.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)).clm_apply
      continuous_const).clm_apply continuous_const)

private lemma continuous_inner_grad {n : ℕ} (φ ψ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hφ : ContDiff ℝ 1 φ) (hψ : ContDiff ℝ 1 ψ) :
    Continuous (fun x => inner ℝ
      ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ φ x))
      ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ ψ x))) := by
  rw [funext fun x => inner_grad_eq_sum φ ψ x]
  refine continuous_finset_sum _ (fun i _ => ?_)
  exact ((hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul
    ((hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const)

theorem creation_energy_bound_even_of_smooth {n : ℕ} (H : ∀ (f u : EuclideanSpace ℝ (Fin n) → ℝ), ContDiff ℝ 2 f → (∀ x, f (-x) = f x) → (∀ x v : EuclideanSpace ℝ (Fin n), 2 * Real.pi * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) x v v) → ConvexOn ℝ Set.univ (fun x => f x - Real.pi * ‖x‖ ^ 2) → (∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : EuclideanSpace ℝ (Fin n), |fderiv ℝ f x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ∧ |fderiv ℝ (fderiv ℝ f) x v v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ^ 2) → ContDiff ℝ 3 u → (∀ x, u (-x) = u x) → (∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v w z : EuclideanSpace ℝ (Fin n), |u x| ≤ C * (1 + ‖x‖) ^ N ∧ |fderiv ℝ u x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ∧ |fderiv ℝ (fderiv ℝ u) x v w| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ * ‖w‖ ∧ |fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x v w z| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ * ‖w‖ * ‖z‖) → 4 * Real.pi * (∫ x, ‖fderiv ℝ u x‖ ^ 2 * Real.exp (-(f x))) ≤ (∫ x, (- Laplacian.laplacian u x + inner ℝ ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ f x)) ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ u x))) ^ 2 * Real.exp (-(f x)))) (f u : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 2 f) (hfe : ∀ x, f (-x) = f x) (hH : ∀ x v : EuclideanSpace ℝ (Fin n), 2 * Real.pi * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) x v v) (hconv : ConvexOn ℝ Set.univ (fun x => f x - Real.pi * ‖x‖ ^ 2)) (hgf : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : EuclideanSpace ℝ (Fin n), |fderiv ℝ f x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ∧ |fderiv ℝ (fderiv ℝ f) x v v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ^ 2) (hu : ContDiff ℝ 2 u) (hueven : ∀ x, u (-x) = u x) (hgu : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : EuclideanSpace ℝ (Fin n), |u x| ≤ C * (1 + ‖x‖) ^ N ∧ |fderiv ℝ u x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ∧ |fderiv ℝ (fderiv ℝ u) x v v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ^ 2) : 4 * Real.pi * (∫ x, ‖fderiv ℝ u x‖ ^ 2 * Real.exp (-(f x))) ≤ (∫ x, (- Laplacian.laplacian u x + inner ℝ ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ f x)) ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ u x))) ^ 2 * Real.exp (-(f x))) := by
  obtain ⟨Cu, hCu0, Nu, hguN⟩ := hgu
  obtain ⟨Cf, hCf0, Nf, hFbd⟩ := hgf
  have huC : Continuous u := hu.continuous
  have huLoc : LocallyIntegrable u volume := huC.locallyIntegrable
  -- Off-diagonal second-derivative bound for `u`
  have hgu2 : ∀ t v w : EuclideanSpace ℝ (Fin n),
      |fderiv ℝ (fderiv ℝ u) t v w| ≤ Cu * (1 + ‖t‖) ^ Nu * ‖v‖ * ‖w‖ := by
    intro t v w
    refine bilinear_bound_of_diag (fderiv ℝ (fderiv ℝ u) t)
      (mul_nonneg hCu0 (by positivity)) (fun z => ?_)
      (fun a b => ?_) v w
    · exact (hguN t z).2.2
    · exact (hu.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq a b
  -- Uniform smallness of the kernel's radius
  have hrOut_le : ∀ k : ℕ, (bump n k).rOut ≤ 2 := by
    intro k
    have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by have h : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k; linarith
    calc (bump n k).rOut = 2 * ((k : ℝ) + 1)⁻¹ := rfl
      _ ≤ 2 * 1 := by gcongr; exact inv_le_one_of_one_le₀ hk1
      _ = 2 := by ring
  have h3pow : ∀ (k : ℕ) (x : EuclideanSpace ℝ (Fin n)),
      (1 + ‖x‖ + (bump n k).rOut) ^ Nu ≤ 3 ^ Nu * (1 + ‖x‖) ^ Nu := by
    intro k x
    have hle : 1 + ‖x‖ + (bump n k).rOut ≤ 3 * (1 + ‖x‖) := by
      have := hrOut_le k; nlinarith [norm_nonneg x]
    calc (1 + ‖x‖ + (bump n k).rOut) ^ Nu ≤ (3 * (1 + ‖x‖)) ^ Nu :=
          pow_le_pow_left₀ (by have h := (bump n k).rOut_pos; linarith [norm_nonneg x]) hle Nu
      _ = 3 ^ Nu * (1 + ‖x‖) ^ Nu := by rw [mul_pow]
  -- The four-fold growth bound for the mollification
  have hgroth : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v w z : EuclideanSpace ℝ (Fin n),
      |moll n k u x| ≤ C * (1 + ‖x‖) ^ N ∧
      |fderiv ℝ (moll n k u) x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ∧
      |fderiv ℝ (fderiv ℝ (moll n k u)) x v w| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ * ‖w‖ ∧
      |fderiv ℝ (fderiv ℝ (fderiv ℝ (moll n k u))) x v w z|
        ≤ C * (1 + ‖x‖) ^ N * ‖v‖ * ‖w‖ * ‖z‖ := by
    intro k
    set Kop : ℝ := ∫ s, ‖fderiv ℝ (fderiv ℝ (kern n k)) s‖ with hKop
    have hKop0 : 0 ≤ Kop := integral_nonneg (fun s => ContinuousLinearMap.opNorm_nonneg _)
    refine ⟨(Cu + Cu * Kop + 1) * 3 ^ Nu,
      mul_nonneg (by nlinarith [hCu0, hKop0, mul_nonneg hCu0 hKop0]) (pow_nonneg (by norm_num) Nu),
      Nu, ?_⟩
    intro x v w z
    have hb1 := moll_growth (u := u) (k := k) huC hCu0 (fun t => (hguN t 0).1) x
    have hb2 := fderiv_moll_growth (u := u) (k := k) (hu.of_le (by norm_num)) hCu0
      (fun t v => (hguN t v).2.1) x v
    have hb3 := fderiv_fderiv_moll_growth (u := u) (k := k) hu hCu0 hgu2 x v w
    have hb4 := third_deriv_moll_growth (u := u) (k := k) hu hCu0
      (fun t v => (hguN t v).2.1) x v w z
    have hCk1 : Cu * 3 ^ Nu ≤ ((Cu + Cu * Kop + 1) * 3 ^ Nu) :=
      mul_le_mul_of_nonneg_right
        (by nlinarith [mul_nonneg hCu0 hKop0]) (pow_nonneg (by norm_num) Nu)
    have hCk2 : Cu * Kop * 3 ^ Nu ≤ ((Cu + Cu * Kop + 1) * 3 ^ Nu) :=
      mul_le_mul_of_nonneg_right (by linarith [hCu0]) (pow_nonneg (by norm_num) Nu)
    refine ⟨?_, ?_, ?_, ?_⟩
    · calc |moll n k u x| ≤ Cu * (1 + ‖x‖ + (bump n k).rOut) ^ Nu := hb1
        _ ≤ Cu * (3 ^ Nu * (1 + ‖x‖) ^ Nu) := mul_le_mul_of_nonneg_left (h3pow k x) hCu0
        _ = (Cu * 3 ^ Nu) * (1 + ‖x‖) ^ Nu := by ring
        _ ≤ ((Cu + Cu * Kop + 1) * 3 ^ Nu) * (1 + ‖x‖) ^ Nu :=
            mul_le_mul_of_nonneg_right hCk1 (by positivity)
    · calc |fderiv ℝ (moll n k u) x v| ≤ Cu * (1 + ‖x‖ + (bump n k).rOut) ^ Nu * ‖v‖ := hb2
        _ ≤ Cu * (3 ^ Nu * (1 + ‖x‖) ^ Nu) * ‖v‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (h3pow k x) hCu0) (norm_nonneg v)
        _ = (Cu * 3 ^ Nu) * (1 + ‖x‖) ^ Nu * ‖v‖ := by ring
        _ ≤ ((Cu + Cu * Kop + 1) * 3 ^ Nu) * (1 + ‖x‖) ^ Nu * ‖v‖ := by
            gcongr
    · calc |fderiv ℝ (fderiv ℝ (moll n k u)) x v w|
          ≤ Cu * (1 + ‖x‖ + (bump n k).rOut) ^ Nu * ‖v‖ * ‖w‖ := hb3
        _ ≤ Cu * (3 ^ Nu * (1 + ‖x‖) ^ Nu) * ‖v‖ * ‖w‖ := by
            gcongr
            exact h3pow k x
        _ = (Cu * 3 ^ Nu) * (1 + ‖x‖) ^ Nu * ‖v‖ * ‖w‖ := by ring
        _ ≤ ((Cu + Cu * Kop + 1) * 3 ^ Nu) * (1 + ‖x‖) ^ Nu * ‖v‖ * ‖w‖ := by
            gcongr
    · calc |fderiv ℝ (fderiv ℝ (fderiv ℝ (moll n k u))) x v w z|
          ≤ Kop * Cu * (1 + ‖x‖ + (bump n k).rOut) ^ Nu * ‖v‖ * ‖w‖ * ‖z‖ := hb4
        _ ≤ Cu * Kop * (3 ^ Nu * (1 + ‖x‖) ^ Nu) * ‖v‖ * ‖w‖ * ‖z‖ := by
            rw [show Kop * Cu = Cu * Kop from by ring]
            gcongr
            exact h3pow k x
        _ = (Cu * Kop * 3 ^ Nu) * (1 + ‖x‖) ^ Nu * ‖v‖ * ‖w‖ * ‖z‖ := by ring
        _ ≤ ((Cu + Cu * Kop + 1) * 3 ^ Nu) * (1 + ‖x‖) ^ Nu * ‖v‖ * ‖w‖ * ‖z‖ := by
            gcongr
  -- Apply `H`
  have hineq : ∀ k : ℕ, 4 * Real.pi * (∫ x, ‖fderiv ℝ (moll n k u) x‖ ^ 2 * Real.exp (-(f x)))
      ≤ (∫ x, (- Laplacian.laplacian (moll n k u) x + inner ℝ
          ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ f x))
          ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
            (fderiv ℝ (moll n k u) x))) ^ 2 * Real.exp (-(f x))) := by
    intro k
    refine H f (moll n k u) hf hfe hH hconv ⟨Cf, hCf0, Nf, hFbd⟩ ?_ (fun x => moll_even hueven k x) (hgroth k)
    exact (moll_contDiff u huLoc k).of_le (WithTop.coe_le_coe.mpr le_top)
  set m : ℕ := Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) with hm
  have hLHS : Tendsto (fun k : ℕ => ∫ x, ‖fderiv ℝ (moll n k u) x‖ ^ 2 * Real.exp (-(f x))) atTop
      (𝓝 (∫ x, ‖fderiv ℝ u x‖ ^ 2 * Real.exp (-(f x)))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => (Cu * 3 ^ Nu * (1 + ‖x‖) ^ Nu) ^ 2 * Real.exp (-(f x))) ?_ ?_ ?_ ?_
    · intro k
      have hc : Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
          ‖fderiv ℝ (moll n k u) x‖ ^ 2 * Real.exp (-(f x))) :=
        (((moll_contDiff_two u huLoc k).continuous_fderiv (by norm_num)).norm.pow 2).mul
          (Real.continuous_exp.comp (hf.continuous.neg))
      exact hc.aestronglyMeasurable
    · refine integrable_mul_exp_neg_of_pow_bound hf.continuous hfe hconv (by fun_prop)
        ((Cu * 3 ^ Nu) ^ 2) (Nu * 2) (fun x => ?_)
      rw [abs_of_nonneg (by positivity),
        show (Cu * 3 ^ Nu * (1 + ‖x‖) ^ Nu) ^ 2
          = (Cu * 3 ^ Nu) ^ 2 * ((1 + ‖x‖) ^ Nu) ^ 2 from by ring, ← pow_mul]
    · intro k
      filter_upwards with x
      rw [Real.norm_of_nonneg (by positivity)]
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
      have h := fderiv_moll_growth (u := u) (k := k) (hu.of_le (by norm_num)) hCu0
        (fun t v => (hguN t v).2.1) x v
      calc ‖(fderiv ℝ (moll n k u) x) v‖ = |fderiv ℝ (moll n k u) x v| := Real.norm_eq_abs _
        _ ≤ Cu * (1 + ‖x‖ + (bump n k).rOut) ^ Nu * ‖v‖ := h
        _ ≤ (Cu * 3 ^ Nu * (1 + ‖x‖) ^ Nu) * ‖v‖ := by
            rw [show Cu * (1 + ‖x‖ + (bump n k).rOut) ^ Nu * ‖v‖
                = (Cu * (1 + ‖x‖ + (bump n k).rOut) ^ Nu) * ‖v‖ from by ring]
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg v)
            calc Cu * (1 + ‖x‖ + (bump n k).rOut) ^ Nu
                ≤ Cu * (3 ^ Nu * (1 + ‖x‖) ^ Nu) :=
                  mul_le_mul_of_nonneg_left (h3pow k x) hCu0
              _ = Cu * 3 ^ Nu * (1 + ‖x‖) ^ Nu := by ring
    · filter_upwards with x
      have h1 : Tendsto (fun k : ℕ => ∑ i, (fderiv ℝ (moll n k u) x (stdB n i)) ^ 2) atTop
          (𝓝 (∑ i, (fderiv ℝ u x (stdB n i)) ^ 2)) :=
        tendsto_finset_sum _ (fun i _ => (fderiv_moll_tendsto u hu x (stdB n i)).pow 2)
      have h2 : (fun k : ℕ => ∑ i, (fderiv ℝ (moll n k u) x (stdB n i)) ^ 2)
          = fun k => ‖fderiv ℝ (moll n k u) x‖ ^ 2 :=
        funext fun k => (clm_norm_sq_eq_sum _).symm
      have h3 : (∑ i, (fderiv ℝ u x (stdB n i)) ^ 2) = ‖fderiv ℝ u x‖ ^ 2 :=
        (clm_norm_sq_eq_sum _).symm
      rw [h2, h3] at h1
      exact h1.mul_const (Real.exp (-(f x)))
  have hRHS : Tendsto (fun k : ℕ => ∫ x, (- Laplacian.laplacian (moll n k u) x + inner ℝ
        ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ f x))
        ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
          (fderiv ℝ (moll n k u) x))) ^ 2 * Real.exp (-(f x))) atTop
      (𝓝 (∫ x, (- Laplacian.laplacian u x + inner ℝ
        ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ f x))
        ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
          (fderiv ℝ u x))) ^ 2 * Real.exp (-(f x)))) := by
    set K : ℝ := (m : ℝ) * (Cu * 3 ^ Nu + Cf * Cu * 3 ^ Nu) with hK
    have hK0 : 0 ≤ K := by rw [hK]; positivity
    have hbd : ∀ (k : ℕ) (x : EuclideanSpace ℝ (Fin n)),
        |(- Laplacian.laplacian (moll n k u) x + inner ℝ
          ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ f x))
          ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
            (fderiv ℝ (moll n k u) x)))| ≤ K * (1 + ‖x‖) ^ (Nf + Nu) := by
      intro k x
      have hm1 : |Laplacian.laplacian (moll n k u) x|
          ≤ (m : ℝ) * (Cu * 3 ^ Nu) * (1 + ‖x‖) ^ (Nf + Nu) := by
        rw [laplacian_eq_sum_fderiv]
        calc |∑ i, fderiv ℝ (fderiv ℝ (moll n k u)) x (stdB n i) (stdB n i)|
            ≤ ∑ i, |fderiv ℝ (fderiv ℝ (moll n k u)) x (stdB n i) (stdB n i)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i : Fin m, Cu * 3 ^ Nu * (1 + ‖x‖) ^ (Nf + Nu) := by
              refine Finset.sum_le_sum fun i _ => ?_
              have hb := fderiv_fderiv_moll_growth (u := u) (k := k) hu hCu0 hgu2 x (stdB n i) (stdB n i)
              calc |fderiv ℝ (fderiv ℝ (moll n k u)) x (stdB n i) (stdB n i)|
                  ≤ Cu * (1 + ‖x‖ + (bump n k).rOut) ^ Nu * ‖stdB n i‖ * ‖stdB n i‖ := hb
                _ = Cu * (1 + ‖x‖ + (bump n k).rOut) ^ Nu := by
                    rw [OrthonormalBasis.norm_eq_one]; ring
                _ ≤ Cu * (3 ^ Nu * (1 + ‖x‖) ^ Nu) := mul_le_mul_of_nonneg_left (h3pow k x) hCu0
                _ = Cu * 3 ^ Nu * (1 + ‖x‖) ^ Nu := by ring
                _ ≤ Cu * 3 ^ Nu * (1 + ‖x‖) ^ (Nf + Nu) := by
                    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                    exact pow_le_pow_right₀ (by linarith [norm_nonneg x]) (Nat.le_add_left Nu Nf)
          _ = (m : ℝ) * (Cu * 3 ^ Nu * (1 + ‖x‖) ^ (Nf + Nu)) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          _ = (m : ℝ) * (Cu * 3 ^ Nu) * (1 + ‖x‖) ^ (Nf + Nu) := by ring
      have hm2 : |inner ℝ
          ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ f x))
          ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
            (fderiv ℝ (moll n k u) x))|
          ≤ (m : ℝ) * (Cf * Cu * 3 ^ Nu) * (1 + ‖x‖) ^ (Nf + Nu) := by
        rw [inner_grad_eq_sum]
        calc |∑ i, fderiv ℝ f x (stdB n i) * fderiv ℝ (moll n k u) x (stdB n i)|
            ≤ ∑ i, |fderiv ℝ f x (stdB n i) * fderiv ℝ (moll n k u) x (stdB n i)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i : Fin m, (Cf * (1 + ‖x‖) ^ Nf) * (Cu * 3 ^ Nu * (1 + ‖x‖) ^ Nu) := by
              refine Finset.sum_le_sum fun i _ => ?_
              rw [abs_mul]
              refine mul_le_mul ?_ ?_ (abs_nonneg _) (by positivity)
              · simpa [OrthonormalBasis.norm_eq_one] using (hFbd x (stdB n i)).1
              · have h := fderiv_moll_growth (u := u) (k := k) (hu.of_le (by norm_num)) hCu0
                  (fun t v => (hguN t v).2.1) x (stdB n i)
                calc |fderiv ℝ (moll n k u) x (stdB n i)|
                    ≤ Cu * (1 + ‖x‖ + (bump n k).rOut) ^ Nu * ‖stdB n i‖ := h
                  _ = Cu * (1 + ‖x‖ + (bump n k).rOut) ^ Nu := by
                      rw [OrthonormalBasis.norm_eq_one]; ring
                  _ ≤ Cu * (3 ^ Nu * (1 + ‖x‖) ^ Nu) := mul_le_mul_of_nonneg_left (h3pow k x) hCu0
                  _ = Cu * 3 ^ Nu * (1 + ‖x‖) ^ Nu := by ring
          _ = (m : ℝ) * ((Cf * (1 + ‖x‖) ^ Nf) * (Cu * 3 ^ Nu * (1 + ‖x‖) ^ Nu)) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          _ = (m : ℝ) * (Cf * Cu * 3 ^ Nu) * (1 + ‖x‖) ^ (Nf + Nu) := by
              rw [show Cf * (1 + ‖x‖) ^ Nf * (Cu * 3 ^ Nu * (1 + ‖x‖) ^ Nu)
                  = Cf * Cu * 3 ^ Nu * ((1 + ‖x‖) ^ Nf * (1 + ‖x‖) ^ Nu) from by ring,
                ← pow_add]
              ring
      calc |(- Laplacian.laplacian (moll n k u) x) + inner ℝ
            ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ f x))
            ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
              (fderiv ℝ (moll n k u) x))|
          ≤ |Laplacian.laplacian (moll n k u) x| + |inner ℝ
              ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ f x))
              ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
                (fderiv ℝ (moll n k u) x))| := by
              simpa only [abs_neg] using abs_add_le (-Laplacian.laplacian (moll n k u) x)
                (inner ℝ ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ f x))
                  ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
                    (fderiv ℝ (moll n k u) x)))
        _ ≤ ((m : ℝ) * (Cu * 3 ^ Nu) + (m : ℝ) * (Cf * Cu * 3 ^ Nu)) * (1 + ‖x‖) ^ (Nf + Nu) := by
            rw [add_mul]; exact add_le_add hm1 hm2
        _ = K * (1 + ‖x‖) ^ (Nf + Nu) := by rw [hK]; ring
    refine tendsto_integral_of_dominated_convergence
      (fun x => (K * (1 + ‖x‖) ^ (Nf + Nu)) ^ 2 * Real.exp (-(f x))) ?_ ?_ ?_ ?_
    · intro k
      have hc : Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
          (- Laplacian.laplacian (moll n k u) x + inner ℝ
            ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ f x))
            ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
              (fderiv ℝ (moll n k u) x))) ^ 2 * Real.exp (-(f x))) :=
        ((((continuous_laplacian (moll n k u) (moll_contDiff_two u huLoc k)).neg).add
          (continuous_inner_grad f (moll n k u) (hf.of_le (by norm_num))
            ((moll_contDiff_two u huLoc k).of_le (by norm_num)))).pow 2).mul
          (Real.continuous_exp.comp (hf.continuous.neg))
      exact hc.aestronglyMeasurable
    · refine integrable_mul_exp_neg_of_pow_bound hf.continuous hfe hconv (by fun_prop)
        (K ^ 2) ((Nf + Nu) * 2) (fun x => ?_)
      rw [abs_of_nonneg (by positivity),
        show (K * (1 + ‖x‖) ^ (Nf + Nu)) ^ 2
          = K ^ 2 * ((1 + ‖x‖) ^ (Nf + Nu)) ^ 2 from by ring, ← pow_mul]
    · intro k
      filter_upwards with x
      rw [Real.norm_of_nonneg (by positivity)]
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      rw [sq_le_sq, abs_of_nonneg (mul_nonneg hK0 (by positivity))]
      exact hbd k x
    · filter_upwards with x
      simp only [laplacian_eq_sum_fderiv, inner_grad_eq_sum]
      have h := (tendsto_finset_sum Finset.univ
          (fun i _ => fderiv_fderiv_moll_tendsto u hu x i)).neg.add
        (tendsto_finset_sum Finset.univ (fun i _ =>
          (fderiv_moll_tendsto u hu x (stdB n i)).const_mul (fderiv ℝ f x (stdB n i))))
      exact h.pow 2 |>.mul_const (Real.exp (-(f x)))
  exact le_of_tendsto_of_tendsto (hLHS.const_mul (4 * Real.pi)) hRHS (Eventually.of_forall hineq)

end
end Commons.Analysis.GaussianMeasure