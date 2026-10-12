import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.SmallBoxBridge.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `kinFT f` is real-analytic (`Work.SmallBoxBridge.kinFT_analyticAt`)

`Submission.BoseGases.kinFT f p = ∫_y e^{−i⟪p,y⟫} f(y) dy` is the `p`-convention Fourier
transform of `f`.  For `f` continuous with compact support it is (the restriction of) an entire
function of `p`, hence real-analytic at every point.  This file proves the explicit power-series
expansion.

* `linC z` is the continuous linear map `v ↦ −i⟪z,v⟫`;
* `phiCoeff n z` is the continuous `n`-multilinear map `v ↦ ∏_{i<n} (−i⟪z, v_i⟫)` (built by
  composing the product multilinear map with the family `linC z`), with `‖phiCoeff n z‖ ≤ ‖z‖ⁿ`;
* `kinFTCoeff f p n` is the Bochner integral `∫_z e^{−i⟪p,z⟫}f(z) • phiCoeff n z`, so that on the
  diagonal `kinFTCoeff f p n (fun _ ↦ y) = ∫_z e^{−i⟪p,z⟫}f(z)(−i⟪z,y⟫)ⁿ dz`;
* `kinFTSeries f p n = (n!)⁻¹ • kinFTCoeff f p n` is the formal Taylor series of `kinFT f` at `p`;
* its diagonal sum is `∑_n (n!)⁻¹ ∫_z e^{−i⟪p,z⟫}f(z)(−i⟪z,y⟫)ⁿ dz = ∫_z e^{−i⟪p+y,z⟫}f(z)dz`
  by the exponential series + dominated convergence, and the coefficients are bounded by
  `(n!)⁻¹Rⁿ∫‖f‖` with `R` a radius of the support, so the radius of convergence is `⊤`.
-/

noncomputable section

open MeasureTheory
open scoped Topology ContDiff BigOperators ENNReal

local notation "𝔼" => EuclideanSpace ℝ (Fin 3)

namespace Work.SmallBoxBridge

/-! ## 0. Elementary auxiliary estimates -/

/-- The norm of the image of a real number in `ℂ` is its absolute value. -/
lemma norm_ofReal_c (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq_eq_abs]

/-- Partial sums of the exponential series are bounded by `Real.exp`. -/
lemma sum_range_inv_factorial_mul_pow_le_exp (a : ℝ) (ha : 0 ≤ a) (N : ℕ) :
    ∑ n ∈ Finset.range N, ((n.factorial : ℝ))⁻¹ * a ^ n ≤ Real.exp a := by
  have hsum : Summable (fun n : ℕ => a ^ n / ((n.factorial : ℝ))) :=
    Real.summable_pow_div_factorial a
  have hexp : Real.exp a = ∑' n : ℕ, a ^ n / ((n.factorial : ℝ)) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  have h2 : ∑ n ∈ Finset.range N, a ^ n / ((n.factorial : ℝ)) ≤ Real.exp a := by
    rw [hexp]
    exact hsum.sum_le_tsum (Finset.range N) (fun i _ =>
      div_nonneg (pow_nonneg ha i) (Nat.cast_nonneg _))
  calc ∑ n ∈ Finset.range N, ((n.factorial : ℝ))⁻¹ * a ^ n
      = ∑ n ∈ Finset.range N, a ^ n / ((n.factorial : ℝ)) :=
        Finset.sum_congr rfl (fun n _ => by rw [div_eq_inv_mul])
    _ ≤ Real.exp a := h2

/-- Compact-support bookkeeping: the support of `z ↦ g z * f z` is inside that of `f`. -/
lemma support_mul_subset_right {f g : 𝔼 → ℂ} :
    Function.support (fun z => g z * f z) ⊆ Function.support f := by
  intro z hz
  rw [Function.mem_support] at hz ⊢
  intro hfz
  exact hz (by simp [hfz])

/-- Compact-support bookkeeping: the support of `z ↦ f z • g z` is inside that of `f`. -/
lemma support_smul_subset_left {n : ℕ} {f : 𝔼 → ℂ}
    {g : 𝔼 → ContinuousMultilinearMap ℝ (fun _ : Fin n => 𝔼) ℂ} :
    Function.support (fun z => f z • g z) ⊆ Function.support f := by
  intro z hz
  rw [Function.mem_support] at hz ⊢
  intro hfz
  exact hz (by rw [hfz]; exact zero_smul ℂ (g z))

/-! ## 1. The coefficient multilinear maps -/

/-- The continuous linear map `v ↦ −i⟪z,v⟫`. -/
noncomputable def linC (z : 𝔼) : 𝔼 →L[ℝ] ℂ :=
  (Complex.ofRealCLM.comp (innerSL ℝ z)).smulRight (-Complex.I)

lemma linC_apply (z v : 𝔼) : linC z v = -Complex.I * (inner ℝ z v : ℂ) := by
  rw [linC, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, coe_innerSL_apply, smul_eq_mul, mul_comm]

lemma linC_norm_le (z : 𝔼) : ‖linC z‖ ≤ ‖z‖ := by
  apply ContinuousLinearMap.opNorm_le_bound (linC z) (norm_nonneg z)
  intro v
  rw [linC_apply, norm_mul, norm_neg, Complex.norm_I, one_mul, norm_ofReal_c]
  exact abs_real_inner_le_norm z v

lemma linC_dist_le (z z' : 𝔼) : dist (linC z) (linC z') ≤ dist z z' := by
  rw [dist_eq_norm, dist_eq_norm]
  apply ContinuousLinearMap.opNorm_le_bound (linC z - linC z') (norm_nonneg (z - z'))
  intro v
  have h : (linC z - linC z') v = -Complex.I * (inner ℝ (z - z') v : ℂ) := by
    rw [sub_apply, linC_apply, linC_apply, inner_sub_left, Complex.ofReal_sub]
    ring
  rw [h, norm_mul, norm_neg, Complex.norm_I, one_mul, norm_ofReal_c]
  exact abs_real_inner_le_norm (z - z') v

lemma linC_lipschitz : LipschitzWith 1 linC := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro z z'
  simpa using linC_dist_le z z'

lemma linC_continuous : Continuous linC := linC_lipschitz.continuous

/-- The continuous `n`-multilinear map `v ↦ ∏_{i<n} (−i⟪z, v_i⟫)`. -/
noncomputable def phiCoeff (n : ℕ) (z : 𝔼) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => 𝔼) ℂ :=
  ContinuousMultilinearMap.compContinuousLinearMapLRight
    (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℂ) (fun _ : Fin n => linC z)

lemma phiCoeff_apply (n : ℕ) (z : 𝔼) (v : Fin n → 𝔼) :
    phiCoeff n z v = ∏ i, linC z (v i) := by
  rw [phiCoeff, ContinuousMultilinearMap.compContinuousLinearMapLRight_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply]

lemma phiCoeff_diag (n : ℕ) (z y : 𝔼) :
    phiCoeff n z (fun _ => y) = (-Complex.I * (inner ℝ z y : ℂ))^n := by
  rw [phiCoeff_apply]
  simp only [linC_apply]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma phiCoeff_norm_le (n : ℕ) (z : 𝔼) : ‖phiCoeff n z‖ ≤ ‖z‖^n := by
  apply ContinuousMultilinearMap.opNorm_le_bound (M := ‖z‖^n) (pow_nonneg (norm_nonneg z) n)
  intro v
  rw [phiCoeff_apply]
  calc ‖∏ i, linC z (v i)‖ ≤ ∏ i, ‖linC z (v i)‖ := Finset.norm_prod_le _ _
    _ ≤ ∏ i, (‖linC z‖ * ‖v i‖) :=
        Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => (linC z).le_opNorm (v i))
    _ ≤ ∏ i, (‖z‖ * ‖v i‖) :=
        Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i _ => by
          gcongr; exact linC_norm_le z)
    _ = ‖z‖ ^ n * ∏ i, ‖v i‖ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma phiCoeff_continuous (n : ℕ) : Continuous (fun z : 𝔼 => phiCoeff n z) := by
  have h1 : Continuous (fun z : 𝔼 => (fun _ : Fin n => linC z)) :=
    continuous_pi (fun _ => linC_continuous)
  exact (ContinuousMultilinearMap.compContinuousLinearMapLRight
    (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℂ)).cont.comp h1

/-! ## 2. The Bochner integral of the coefficient maps -/

lemma continuous_kinFTweight (p : 𝔼) :
    Continuous (fun z : 𝔼 => Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))) := by
  fun_prop

lemma norm_kinFTweight (p z : 𝔼) :
    ‖Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))‖ = 1 := by
  rw [Complex.norm_exp]
  have : (-(Complex.I * (inner ℝ p z : ℂ))).re = 0 := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im]
  rw [this, Real.exp_zero]

/-- The `n`-th coefficient of the Taylor series of `kinFT f` at `p`, as a Bochner integral of
multilinear maps. -/
noncomputable def kinFTCoeff (f : 𝔼 → ℂ) (p : 𝔼) (n : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => 𝔼) ℂ :=
  ∫ z, (Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * f z) • phiCoeff n z

lemma integrable_kinFTCoeff (f : 𝔼 → ℂ) (p : 𝔼) (n : ℕ) (hf : Continuous f)
    (hcs : HasCompactSupport f) :
    Integrable (fun z : 𝔼 =>
      (Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * f z) • phiCoeff n z) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact ((continuous_kinFTweight p).mul hf).smul (phiCoeff_continuous n)
  · exact hcs.mono (support_smul_subset_left.trans support_mul_subset_right)

/-- The norm majorant `z ↦ ‖f z‖ ‖z‖ⁿ` is integrable. -/
lemma integrable_norm_mul_norm_pow (f : 𝔼 → ℂ) (n : ℕ) (hf : Continuous f)
    (hcs : HasCompactSupport f) : Integrable (fun z : 𝔼 => ‖f z‖ * ‖z‖^n) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact (continuous_norm.comp hf).mul (continuous_norm.pow n)
  · refine hcs.mono ?_
    intro z hz
    rw [Function.mem_support] at hz ⊢
    intro hfz
    exact hz (by simp [hfz])

lemma kinFTCoeff_apply (f : 𝔼 → ℂ) (p : 𝔼) (n : ℕ) (hf : Continuous f)
    (hcs : HasCompactSupport f) (v : Fin n → 𝔼) :
    kinFTCoeff f p n v
      = ∫ z, (Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * f z) * (phiCoeff n z v) := by
  rw [kinFTCoeff,
    ContinuousMultilinearMap.integral_apply (integrable_kinFTCoeff f p n hf hcs) v]
  simp [smul_apply]

lemma kinFTCoeff_norm_le (f : 𝔼 → ℂ) (p : 𝔼) (n : ℕ) (hf : Continuous f)
    (hcs : HasCompactSupport f) :
    ‖kinFTCoeff f p n‖ ≤ ∫ z, ‖f z‖ * ‖z‖^n := by
  rw [kinFTCoeff]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hpt : ∀ z : 𝔼,
      ‖(Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * f z) • phiCoeff n z‖
        ≤ ‖f z‖ * ‖z‖^n := by
    intro z
    rw [norm_smul, norm_mul, norm_kinFTweight, one_mul]
    exact mul_le_mul_of_nonneg_left (phiCoeff_norm_le n z) (norm_nonneg _)
  exact integral_mono_of_nonneg (Filter.Eventually.of_forall (fun z => norm_nonneg _))
    (integrable_norm_mul_norm_pow f n hf hcs) (Filter.Eventually.of_forall hpt)

/-! ## 3. The formal power series -/

/-- The Taylor series of `kinFT f` at `p`: `(n!)⁻¹` times the `n`-th coefficient. -/
noncomputable def kinFTSeries (f : 𝔼 → ℂ) (p : 𝔼) : FormalMultilinearSeries ℝ 𝔼 ℂ :=
  fun n => ((n.factorial : ℝ))⁻¹ • kinFTCoeff f p n

lemma kinFTSeries_apply_diag (f : 𝔼 → ℂ) (p : 𝔼) (n : ℕ) (hf : Continuous f)
    (hcs : HasCompactSupport f) (y : 𝔼) :
    kinFTSeries f p n (fun _ => y)
      = ∫ z, (((n.factorial : ℝ))⁻¹ : ℂ)
          * ((Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * f z)
              * (-Complex.I * (inner ℝ z y : ℂ))^n) := by
  have hint : (∫ z, (Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * f z)
        * (phiCoeff n z (fun _ => y)))
      = ∫ z, (Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * f z)
          * (-Complex.I * (inner ℝ z y : ℂ))^n := by
    apply integral_congr_ae
    filter_upwards with z
    rw [phiCoeff_diag]
  rw [kinFTSeries, smul_apply, kinFTCoeff_apply f p n hf hcs, hint, Complex.real_smul,
    Complex.ofReal_inv, Complex.ofReal_natCast, integral_const_mul]

/-! ## 4. Compact support gives a uniform norm bound on its support -/

lemma exists_norm_le_of_hasCompactSupport (f : 𝔼 → ℂ) (hcs : HasCompactSupport f) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ z : 𝔼, f z ≠ 0 → ‖z‖ ≤ R := by
  obtain ⟨r, hr⟩ := hcs.isBounded.subset_closedBall (0 : 𝔼)
  refine ⟨max r 0, le_max_right _ _, fun z hz => ?_⟩
  have hz' : z ∈ Metric.closedBall (0 : 𝔼) r :=
    hr (subset_tsupport f (Function.mem_support.mpr hz))
  have h1 : ‖z‖ ≤ r := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz'
  exact h1.trans (le_max_left _ _)

/-! ## 5. Integral and norm bounds -/

lemma integrable_norm_of_hasCompactSupport (f : 𝔼 → ℂ) (hf : Continuous f)
    (hcs : HasCompactSupport f) : Integrable (fun z : 𝔼 => ‖f z‖) := by
  refine Continuous.integrable_of_hasCompactSupport (continuous_norm.comp hf) ?_
  refine hcs.mono ?_
  intro z hz
  rw [Function.mem_support] at hz ⊢
  intro hfz
  exact hz (by simp [hfz])

lemma integral_norm_mul_norm_pow_le (f : 𝔼 → ℂ) (n : ℕ) (hf : Continuous f)
    (hcs : HasCompactSupport f) {R : ℝ} (hR : 0 ≤ R)
    (hb : ∀ z : 𝔼, f z ≠ 0 → ‖z‖ ≤ R) :
    ∫ z, ‖f z‖ * ‖z‖^n ≤ R^n * ∫ z, ‖f z‖ := by
  have h1 : Integrable (fun z : 𝔼 => ‖f z‖ * ‖z‖^n) :=
    integrable_norm_mul_norm_pow f n hf hcs
  have h2 : Integrable (fun z : 𝔼 => ‖f z‖ * R^n) :=
    (integrable_norm_of_hasCompactSupport f hf hcs).mul_const _
  have hpt : ∀ z : 𝔼, ‖f z‖ * ‖z‖^n ≤ ‖f z‖ * R^n := by
    intro z
    rcases eq_or_ne (f z) 0 with h | h
    · simp [h]
    · exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hb z h) n) (norm_nonneg _)
  calc ∫ z, ‖f z‖ * ‖z‖^n ≤ ∫ z, ‖f z‖ * R^n := integral_mono h1 h2 hpt
    _ = R^n * ∫ z, ‖f z‖ := by rw [integral_mul_const, mul_comm]

lemma kinFTSeries_norm_le (f : 𝔼 → ℂ) (p : 𝔼) (n : ℕ) (hf : Continuous f)
    (hcs : HasCompactSupport f) {R : ℝ} (hR : 0 ≤ R)
    (hb : ∀ z : 𝔼, f z ≠ 0 → ‖z‖ ≤ R) :
    ‖kinFTSeries f p n‖ ≤ ((n.factorial : ℝ))⁻¹ * (R^n * ∫ z, ‖f z‖) := by
  rw [kinFTSeries, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc ‖kinFTCoeff f p n‖ ≤ ∫ z, ‖f z‖ * ‖z‖^n := kinFTCoeff_norm_le f p n hf hcs
    _ ≤ R^n * ∫ z, ‖f z‖ := integral_norm_mul_norm_pow_le f n hf hcs hR hb

lemma kinFTSeries_radius_pos (f : 𝔼 → ℂ) (p : 𝔼) (hf : Continuous f)
    (hcs : HasCompactSupport f) {R : ℝ} (hR : 0 ≤ R)
    (hb : ∀ z : 𝔼, f z ≠ 0 → ‖z‖ ≤ R) :
    (1 : NNReal) ≤ (kinFTSeries f p).radius := by
  have hM : 0 ≤ ∫ z, ‖f z‖ := integral_nonneg (fun z => norm_nonneg _)
  refine FormalMultilinearSeries.le_radius_of_bound _ ((∫ z, ‖f z‖) * Real.exp R) ?_
  intro n
  rw [NNReal.coe_one, one_pow, mul_one]
  refine (kinFTSeries_norm_le f p n hf hcs hR hb).trans ?_
  have h2 : ((n.factorial : ℝ))⁻¹ * (R^n * ∫ z, ‖f z‖)
      = (R^n / (n.factorial : ℝ)) * ∫ z, ‖f z‖ := by
    rw [div_eq_inv_mul, mul_assoc]
  rw [h2]
  calc (R^n / (n.factorial : ℝ)) * ∫ z, ‖f z‖ ≤ Real.exp R * ∫ z, ‖f z‖ :=
        mul_le_mul_of_nonneg_right (Real.pow_div_factorial_le_exp R hR n) hM
    _ = (∫ z, ‖f z‖) * Real.exp R := mul_comm _ _

/-! ## 6. Continuity and norm of a single term -/

lemma continuous_kFTterm (f : 𝔼 → ℂ) (hf : Continuous f) (p y : 𝔼) (n : ℕ) :
    Continuous (fun z : 𝔼 => (((n.factorial : ℝ))⁻¹ : ℂ)
      * ((Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * f z)
          * (-Complex.I * (inner ℝ z y : ℂ))^n)) := by
  fun_prop

lemma norm_kFTterm (f : 𝔼 → ℂ) (p y z : 𝔼) (n : ℕ) :
    ‖(((n.factorial : ℝ))⁻¹ : ℂ)
      * ((Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * f z)
          * (-Complex.I * (inner ℝ z y : ℂ))^n)‖
      = ((n.factorial : ℝ))⁻¹ * (‖f z‖ * |inner ℝ z y| ^ n) := by
  have hcoe : ‖(((n.factorial : ℝ))⁻¹ : ℂ)‖ = ((n.factorial : ℝ))⁻¹ := by
    rw [norm_inv, norm_ofReal_c, abs_of_nonneg (Nat.cast_nonneg _)]
  have h1 : ‖Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * f z‖ = ‖f z‖ := by
    rw [norm_mul, norm_kinFTweight, one_mul]
  have h2 : ‖(-Complex.I * (inner ℝ z y : ℂ))^n‖ = |inner ℝ z y| ^ n := by
    rw [norm_pow, norm_mul, norm_neg, Complex.norm_I, one_mul, norm_ofReal_c]
  rw [norm_mul, hcoe, norm_mul, h1, h2]

lemma kinFTSeries_norm_apply_le (f : 𝔼 → ℂ) (p : 𝔼) (hf : Continuous f)
    (hcs : HasCompactSupport f) {R : ℝ} (hR : 0 ≤ R)
    (hb : ∀ z : 𝔼, f z ≠ 0 → ‖z‖ ≤ R) (n : ℕ) (y : 𝔼) :
    ‖kinFTSeries f p n (fun _ => y)‖
      ≤ ((n.factorial : ℝ))⁻¹ * (R * ‖y‖)^n * ∫ z, ‖f z‖ := by
  rw [kinFTSeries_apply_diag f p n hf hcs y]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hconst : 0 ≤ ((n.factorial : ℝ))⁻¹ * (R * ‖y‖)^n := by positivity
  have hint : Integrable (fun z : 𝔼 => (((n.factorial : ℝ))⁻¹ * (R * ‖y‖)^n) * ‖f z‖) :=
    (integrable_norm_of_hasCompactSupport f hf hcs).const_mul _
  have hpt : ∀ z : 𝔼,
      ‖(((n.factorial : ℝ))⁻¹ : ℂ)
        * ((Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * f z)
            * (-Complex.I * (inner ℝ z y : ℂ))^n)‖
        ≤ (((n.factorial : ℝ))⁻¹ * (R * ‖y‖)^n) * ‖f z‖ := by
    intro z
    rw [norm_kFTterm]
    rcases eq_or_ne (f z) 0 with h | h
    · simp [h]
    · have h1 : |inner ℝ z y| ^ n ≤ (R * ‖y‖)^n := by
        refine pow_le_pow_left₀ (abs_nonneg _) ?_ n
        calc |inner ℝ z y| ≤ ‖z‖ * ‖y‖ := abs_real_inner_le_norm z y
          _ ≤ R * ‖y‖ := by gcongr; exact hb z h
      calc ((n.factorial : ℝ))⁻¹ * (‖f z‖ * |inner ℝ z y| ^ n)
          ≤ ((n.factorial : ℝ))⁻¹ * (‖f z‖ * (R * ‖y‖)^n) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)) (by positivity)
        _ = (((n.factorial : ℝ))⁻¹ * (R * ‖y‖)^n) * ‖f z‖ := by ring
  calc ∫ z, ‖(((n.factorial : ℝ))⁻¹ : ℂ)
        * ((Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * f z)
            * (-Complex.I * (inner ℝ z y : ℂ))^n)‖
      ≤ ∫ z, (((n.factorial : ℝ))⁻¹ * (R * ‖y‖)^n) * ‖f z‖ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall (fun z => norm_nonneg _)) hint
          (Filter.Eventually.of_forall hpt)
    _ = (((n.factorial : ℝ))⁻¹ * (R * ‖y‖)^n) * ∫ z, ‖f z‖ := integral_const_mul _ _

/-! ## 7. Summability of the diagonal -/

lemma summable_kinFTSeries_diag (f : 𝔼 → ℂ) (p : 𝔼) (hf : Continuous f)
    (hcs : HasCompactSupport f) {R : ℝ} (hR : 0 ≤ R)
    (hb : ∀ z : 𝔼, f z ≠ 0 → ‖z‖ ≤ R) (y : 𝔼) :
    Summable (fun n : ℕ => kinFTSeries f p n (fun _ => y)) := by
  have hbase : Summable (fun n : ℕ => (R * ‖y‖)^n / ((n.factorial : ℝ))) :=
    Real.summable_pow_div_factorial (R * ‖y‖)
  have hG : Summable (fun n : ℕ =>
      ((n.factorial : ℝ))⁻¹ * (R * ‖y‖)^n * ∫ z, ‖f z‖) := by
    have h := hbase.mul_right (∫ z, ‖f z‖)
    refine h.congr (fun n => ?_)
    have h2 : (R * ‖y‖)^n / ((n.factorial : ℝ))
        = ((n.factorial : ℝ))⁻¹ * (R * ‖y‖)^n := by
      rw [div_eq_inv_mul, mul_comm]
    rw [h2]
  exact Summable.of_norm_bounded hG
    (fun n => kinFTSeries_norm_apply_le f p hf hcs hR hb n y)

/-! ## 8. The dominated-convergence step -/

lemma norm_partialSum_le (f : 𝔼 → ℂ) (p y z : 𝔼) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, (((n.factorial : ℝ))⁻¹ : ℂ)
      * ((Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * f z)
          * (-Complex.I * (inner ℝ z y : ℂ))^n)‖
      ≤ Real.exp (‖y‖ * ‖z‖) * ‖f z‖ := by
  have hwy : |inner ℝ z y| ≤ ‖y‖ * ‖z‖ := by
    calc |inner ℝ z y| = |inner ℝ y z| := by rw [real_inner_comm]
      _ ≤ ‖y‖ * ‖z‖ := abs_real_inner_le_norm y z
  calc ‖∑ n ∈ Finset.range N, (((n.factorial : ℝ))⁻¹ : ℂ)
        * ((Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * f z)
            * (-Complex.I * (inner ℝ z y : ℂ))^n)‖
      ≤ ∑ n ∈ Finset.range N, ‖(((n.factorial : ℝ))⁻¹ : ℂ)
        * ((Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * f z)
            * (-Complex.I * (inner ℝ z y : ℂ))^n)‖ := norm_sum_le _ _
    _ = ∑ n ∈ Finset.range N, ((n.factorial : ℝ))⁻¹ * (‖f z‖ * |inner ℝ z y| ^ n) := by
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [norm_kFTterm]
    _ = ‖f z‖ * ∑ n ∈ Finset.range N, ((n.factorial : ℝ))⁻¹ * |inner ℝ z y| ^ n := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun n _ => by ring)
    _ ≤ ‖f z‖ * Real.exp |inner ℝ z y| := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact sum_range_inv_factorial_mul_pow_le_exp _ (abs_nonneg _) N
    _ ≤ ‖f z‖ * Real.exp (‖y‖ * ‖z‖) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hwy) (norm_nonneg _)
    _ = Real.exp (‖y‖ * ‖z‖) * ‖f z‖ := by ring

lemma hasSum_kFTterm (f : 𝔼 → ℂ) (p y z : 𝔼) :
    HasSum (fun n : ℕ => (((n.factorial : ℝ))⁻¹ : ℂ)
      * ((Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * f z)
          * (-Complex.I * (inner ℝ z y : ℂ))^n))
      ((Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * f z)
        * Complex.exp (-(Complex.I * (inner ℝ z y : ℂ)))) := by
  have h0 := NormedSpace.expSeries_hasSum_exp (𝕂 := ℂ) (-(Complex.I * (inner ℝ z y : ℂ)))
  have h0' : HasSum (fun n : ℕ => ((n.factorial : ℂ))⁻¹ * (-(Complex.I * (inner ℝ z y : ℂ)))^n)
      (NormedSpace.exp (-(Complex.I * (inner ℝ z y : ℂ)))) := by
    simpa only [NormedSpace.expSeries_apply_eq, smul_eq_mul] using h0
  have h1 : HasSum (fun n : ℕ => ((n.factorial : ℂ))⁻¹ * (-(Complex.I * (inner ℝ z y : ℂ)))^n)
      (Complex.exp (-(Complex.I * (inner ℝ z y : ℂ)))) := by
    rwa [← Complex.exp_eq_exp_ℂ] at h0'
  have h3 : HasSum (fun n : ℕ => (Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * f z)
      * (((n.factorial : ℂ))⁻¹ * (-(Complex.I * (inner ℝ z y : ℂ)))^n))
      ((Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * f z)
        * Complex.exp (-(Complex.I * (inner ℝ z y : ℂ)))) :=
    h1.mul_left _
  have hsummand : (fun n : ℕ => (((n.factorial : ℝ))⁻¹ : ℂ)
      * ((Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * f z)
          * (-Complex.I * (inner ℝ z y : ℂ))^n))
      = fun n : ℕ => (Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * f z)
          * (((n.factorial : ℂ))⁻¹ * (-(Complex.I * (inner ℝ z y : ℂ)))^n) := by
    funext n
    push_cast
    ring
  rw [hsummand]
  exact h3

lemma integral_kinFTweight_eq (f : 𝔼 → ℂ) (p y : 𝔼) :
    (∫ z, (Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * f z)
        * Complex.exp (-(Complex.I * (inner ℝ z y : ℂ))))
      = Submission.BoseGases.kinFT f (p + y) := by
  rw [Submission.BoseGases.kinFT]
  apply integral_congr_ae
  filter_upwards with z
  have h : (inner ℝ (p + y) z : ℂ) = (inner ℝ p z : ℂ) + (inner ℝ z y : ℂ) := by
    rw [inner_add_left, real_inner_comm y z]
    push_cast
    ring
  have harg : -(Complex.I * ((inner ℝ p z : ℂ) + (inner ℝ z y : ℂ)))
      = -(Complex.I * (inner ℝ p z : ℂ)) + -(Complex.I * (inner ℝ z y : ℂ)) := by ring
  rw [h, harg, Complex.exp_add]
  ring

lemma integrable_exp_bound (f : 𝔼 → ℂ) (hf : Continuous f) (hcs : HasCompactSupport f)
    (y : 𝔼) : Integrable (fun z : 𝔼 => Real.exp (‖y‖ * ‖z‖) * ‖f z‖) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact (Real.continuous_exp.comp (continuous_const.mul continuous_norm)).mul
      (continuous_norm.comp hf)
  · refine hcs.mono ?_
    intro z hz
    rw [Function.mem_support] at hz ⊢
    intro hfz
    exact hz (by simp [hfz])

lemma hasSum_kinFTSeries_diag (f : 𝔼 → ℂ) (p : 𝔼) (hf : Continuous f)
    (hcs : HasCompactSupport f) {R : ℝ} (hR : 0 ≤ R)
    (hb : ∀ z : 𝔼, f z ≠ 0 → ‖z‖ ≤ R) (y : 𝔼) :
    HasSum (fun n : ℕ => kinFTSeries f p n (fun _ => y))
      (Submission.BoseGases.kinFT f (p + y)) := by
  have hsumm := summable_kinFTSeries_diag f p hf hcs hR hb y
  rw [hsumm.hasSum_iff_tendsto_nat]
  set Ff : ℕ → 𝔼 → ℂ := fun N z => ∑ n ∈ Finset.range N,
    (((n.factorial : ℝ))⁻¹ : ℂ)
      * ((Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * f z)
          * (-Complex.I * (inner ℝ z y : ℂ))^n) with hFf
  have hInt_eq : ∀ N, (∫ z, Ff N z) = ∑ n ∈ Finset.range N, kinFTSeries f p n (fun _ => y) := by
    intro N
    rw [hFf]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [kinFTSeries_apply_diag f p n hf hcs y]
    · intro n _
      refine Continuous.integrable_of_hasCompactSupport ?_ ?_
      · exact continuous_kFTterm f hf p y n
      · refine hcs.mono ?_
        intro z hz
        rw [Function.mem_support] at hz ⊢
        intro hfz
        exact hz (by simp [hfz])
  have htend := tendsto_integral_of_dominated_convergence
    (fun z : 𝔼 => Real.exp (‖y‖ * ‖z‖) * ‖f z‖)
    (F := Ff)
    (f := fun z : 𝔼 => (Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * f z)
        * Complex.exp (-(Complex.I * (inner ℝ z y : ℂ))))
    (fun N => by
      rw [hFf]
      exact (continuous_finsetSum _ (fun n _ => continuous_kFTterm f hf p y n)).aestronglyMeasurable)
    (integrable_exp_bound f hf hcs y)
    (fun N => Filter.Eventually.of_forall (fun z => by
      rw [hFf]
      exact norm_partialSum_le f p y z N))
    (Filter.Eventually.of_forall (fun z => (hasSum_kFTterm f p y z).tendsto_sum_nat))
  rw [← integral_kinFTweight_eq f p y]
  exact Filter.Tendsto.congr' (Filter.Eventually.of_forall fun N => hInt_eq N) htend

/-! ## 9. The theorem -/

lemma kinFTSeries_le_radius (f : 𝔼 → ℂ) (p : 𝔼) (hf : Continuous f)
    (hcs : HasCompactSupport f) {R : ℝ} (hR : 0 ≤ R)
    (hb : ∀ z : 𝔼, f z ≠ 0 → ‖z‖ ≤ R) :
    (1 : ENNReal) ≤ (kinFTSeries f p).radius := by
  have h := kinFTSeries_radius_pos f p hf hcs hR hb
  simpa using h

theorem kinFT_analyticAt {f : EuclideanSpace ℝ (Fin 3) → ℂ} (hf : Continuous f)
    (hcs : HasCompactSupport f) (p : EuclideanSpace ℝ (Fin 3)) :
    AnalyticAt ℝ (Submission.BoseGases.kinFT f) p := by
  obtain ⟨R, hR, hb⟩ := exists_norm_le_of_hasCompactSupport f hcs
  refine ⟨kinFTSeries f p, 1, kinFTSeries_le_radius f p hf hcs hR hb, by norm_num, ?_⟩
  intro y _
  exact hasSum_kinFTSeries_diag f p hf hcs hR hb y

end Work.SmallBoxBridge
