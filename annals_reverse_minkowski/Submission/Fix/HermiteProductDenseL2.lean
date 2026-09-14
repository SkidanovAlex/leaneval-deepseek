-- ⚠ IMPORT-CLASH WORKAROUND (session 123): verbatim copy of Submission.Commons.Analysis.GaussianMeasure.hermite_product_dense_L2
-- with the import chain redirected so that the duplicate constant `toLp_norm_sq` of
-- `…bobkov_strong_nD` is not pulled into the same environment as
-- `…brascamp_lieb_truncated`.  Do not import both this file and the commons original.
import Mathlib
import Submission.Commons.Analysis.GaussianMeasure.integrable_exp_neg_norm_sq_half
import Submission.Commons.Analysis.GaussianMeasure.integrable_exp_two_abs_inner_mul_exp_neg_sq_half
import Submission.MvPolyMemLp
import Submission.Commons.Analysis.GaussianMeasure.integral_mul_mvpoly_eq_zero_of_hermite

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

namespace Commons.Analysis.GaussianMeasure

private abbrev γ (N : ℕ) : Measure (EuclideanSpace ℝ (Fin N)) :=
  volume.withDensity
    (fun x : EuclideanSpace ℝ (Fin N) => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2 / 2)))

private lemma isFiniteMeasure_gamma (N : ℕ) : IsFiniteMeasure (γ N) := by
  refine isFiniteMeasure_withDensity ?_
  have h := (integrable_exp_neg_norm_sq_half (n := N)).hasFiniteIntegral
  rw [MeasureTheory.HasFiniteIntegral] at h
  have hrew : ∀ a : EuclideanSpace ℝ (Fin N),
      ‖Real.exp (-‖a‖ ^ 2 / 2)‖ₑ = ENNReal.ofReal (Real.exp (-‖a‖ ^ 2 / 2)) := by
    intro a
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (Real.exp_nonneg _)]
  simp only [hrew] at h
  exact ne_of_lt h

private lemma inner_eq_sum {N : ℕ} (x t : EuclideanSpace ℝ (Fin N)) :
    inner ℝ x t = ∑ i, x.ofLp i * t.ofLp i := by
  simp [PiLp.inner_apply, mul_comm]

private lemma real_exp_eq_tsum (y : ℝ) :
    Real.exp y = ∑' n : ℕ, y ^ n / (n.factorial : ℝ) := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ]
  apply tsum_congr
  intro n
  rw [smul_eq_mul, div_eq_mul_inv, mul_comm]

private lemma hasSum_exp_series (z : ℂ) :
    HasSum (fun n : ℕ => z ^ n / (n.factorial : ℂ)) (Complex.exp z) := by
  have h : HasSum (fun n : ℕ => ((n.factorial : ℂ))⁻¹ • z ^ n) (Complex.exp z) := by
    have hh := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (𝔸 := ℂ) z
    rw [Complex.exp_eq_exp_ℂ]
    exact hh
  simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using h

private def expSum {N : ℕ} (t : EuclideanSpace ℝ (Fin N)) (M : ℕ)
    (x : EuclideanSpace ℝ (Fin N)) : ℂ :=
  ∑ n ∈ Finset.range M, ((((inner ℝ x t : ℝ)) : ℂ) * Complex.I) ^ n / (n.factorial : ℂ)

private lemma continuous_expSum {N : ℕ} (t : EuclideanSpace ℝ (Fin N)) (M : ℕ) :
    Continuous (fun x : EuclideanSpace ℝ (Fin N) => expSum t M x) := by
  unfold expSum
  apply continuous_finsetSum
  intro n _
  fun_prop

private lemma norm_term {N : ℕ} (t x : EuclideanSpace ℝ (Fin N)) (n : ℕ) :
    ‖((((inner ℝ x t : ℝ)) : ℂ) * Complex.I) ^ n / (n.factorial : ℂ)‖
      = |inner ℝ x t| ^ n / (n.factorial : ℝ) := by
  rw [norm_div, norm_pow, norm_mul, Complex.norm_I, mul_one, Complex.norm_natCast]
  have h : ‖((inner ℝ x t : ℝ) : ℂ)‖ = |inner ℝ x t| := RCLike.norm_ofReal (K := ℂ) _
  rw [h]

private lemma norm_expSum_le {N : ℕ} (t x : EuclideanSpace ℝ (Fin N)) (M : ℕ) :
    ‖expSum t M x‖ ≤ Real.exp (|inner ℝ x t|) := by
  calc ‖expSum t M x‖
      = ‖∑ n ∈ Finset.range M, ((((inner ℝ x t : ℝ)) : ℂ) * Complex.I) ^ n
          / (n.factorial : ℂ)‖ := rfl
    _ ≤ ∑ n ∈ Finset.range M, ‖((((inner ℝ x t : ℝ)) : ℂ) * Complex.I) ^ n
          / (n.factorial : ℂ)‖ := norm_sum_le _ _
    _ = ∑ n ∈ Finset.range M, |inner ℝ x t| ^ n / (n.factorial : ℝ) := by
        apply Finset.sum_congr rfl
        intro n _
        rw [norm_term]
    _ ≤ ∑' n : ℕ, |inner ℝ x t| ^ n / (n.factorial : ℝ) := by
        apply Summable.sum_le_tsum
        · intro i _
          positivity
        · exact Real.summable_pow_div_factorial _
    _ = Real.exp |inner ℝ x t| := (real_exp_eq_tsum _).symm

private lemma integrable_exp_two_abs_inner (N : ℕ) (t : EuclideanSpace ℝ (Fin N)) :
    Integrable (fun x : EuclideanSpace ℝ (Fin N) => Real.exp (2 * |inner ℝ x t|)) (γ N) := by
  have hiff := integrable_withDensity_iff
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin N))))
    (f := fun x : EuclideanSpace ℝ (Fin N) => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2 / 2)))
    ((Real.measurable_exp.comp (by fun_prop)).ennreal_ofReal)
    (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))
    (g := fun x : EuclideanSpace ℝ (Fin N) => Real.exp (2 * |inner ℝ x t|))
  refine hiff.mpr ?_
  refine (integrable_exp_two_abs_inner_mul_exp_neg_sq_half (n := N) t).congr ?_
  filter_upwards with x
  have hcomm : |inner ℝ t x| = |inner ℝ x t| := by rw [real_inner_comm]
  rw [ENNReal.toReal_ofReal (Real.exp_nonneg _), hcomm]

private lemma memLp_exp_abs_inner (N : ℕ) (t : EuclideanSpace ℝ (Fin N)) :
    MemLp (fun x : EuclideanSpace ℝ (Fin N) => Real.exp |inner ℝ x t|) 2 (γ N) := by
  haveI : IsFiniteMeasure (γ N) := isFiniteMeasure_gamma N
  rw [memLp_two_iff_integrable_sq (by fun_prop)]
  have hgoal : (fun x : EuclideanSpace ℝ (Fin N) => (Real.exp |inner ℝ x t|) ^ 2)
      = fun x : EuclideanSpace ℝ (Fin N) => Real.exp (2 * |inner ℝ x t|) := by
    funext x
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  rw [hgoal]
  exact integrable_exp_two_abs_inner N t

private noncomputable def linPoly {N : ℕ} (t : EuclideanSpace ℝ (Fin N)) :
    MvPolynomial (Fin N) ℝ :=
  ∑ i, MvPolynomial.C (t.ofLp i) * MvPolynomial.X i

private lemma eval_linPoly {N : ℕ} (t x : EuclideanSpace ℝ (Fin N)) :
    MvPolynomial.eval (fun i => x.ofLp i) (linPoly t) = inner ℝ x t := by
  simp only [linPoly, map_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  rw [inner_eq_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

private lemma integral_expSum_mul (N : ℕ) (φ : EuclideanSpace ℝ (Fin N) → ℝ)
    (hφ : MemLp φ 2 (γ N))
    (h : ∀ P : MvPolynomial (Fin N) ℝ,
      ∫ x, φ x * MvPolynomial.eval (fun i => x.ofLp i) P ∂(γ N) = 0)
    (t : EuclideanSpace ℝ (Fin N)) (M : ℕ) :
    ∫ x, (φ x : ℂ) * expSum t M x ∂(γ N) = 0 := by
  haveI : IsFiniteMeasure (γ N) := isFiniteMeasure_gamma N
  have key : ∀ n : ℕ,
      ∫ x, (φ x : ℂ) * (((((inner ℝ x t : ℝ)) : ℂ) * Complex.I) ^ n / (n.factorial : ℂ))
        ∂(γ N) = 0 := by
    intro n
    have hreal : (∫ x, φ x * ((inner ℝ x t) ^ n) ∂(γ N)) = 0 := by
      have hpoly : (fun x : EuclideanSpace ℝ (Fin N) => φ x * ((inner ℝ x t) ^ n))
          = fun x => φ x * MvPolynomial.eval (fun i => x.ofLp i) (linPoly t ^ n) := by
        funext x
        rw [MvPolynomial.eval_pow, eval_linPoly]
      rw [hpoly, h _]
    have step1 : ∫ x, (φ x : ℂ) *
          (((((inner ℝ x t : ℝ)) : ℂ) * Complex.I) ^ n / (n.factorial : ℂ)) ∂(γ N)
        = (Complex.I ^ n / (n.factorial : ℂ)) *
            ∫ x, (((φ x * (inner ℝ x t) ^ n : ℝ)) : ℂ) ∂(γ N) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      rw [mul_pow, Complex.ofReal_mul, Complex.ofReal_pow]
      ring
    have step2 : (Complex.I ^ n / (n.factorial : ℂ)) *
          ∫ x, (((φ x * (inner ℝ x t) ^ n : ℝ)) : ℂ) ∂(γ N)
        = (Complex.I ^ n / (n.factorial : ℂ)) *
            ((∫ x, φ x * ((inner ℝ x t) ^ n) ∂(γ N) : ℝ) : ℂ) := by
      congr 1
      exact integral_ofReal
    rw [step1, step2, hreal]
    simp
  have hint : ∀ n ∈ Finset.range M,
      Integrable (fun x : EuclideanSpace ℝ (Fin N) =>
        (φ x : ℂ) * (((((inner ℝ x t : ℝ)) : ℂ) * Complex.I) ^ n / (n.factorial : ℂ)))
        (γ N) := by
    intro n _
    have hre : Integrable (fun x : EuclideanSpace ℝ (Fin N) =>
        φ x * MvPolynomial.eval (fun i => x.ofLp i) (linPoly t ^ n)) (γ N) :=
      (memLp_one_iff_integrable).mp
        ((memLp_mvpoly_withDensity_exp_neg_sq_half (linPoly t ^ n)).mul' hφ)
    have hc : Integrable (fun x : EuclideanSpace ℝ (Fin N) =>
        (Complex.I ^ n / (n.factorial : ℂ)) *
          (((φ x * MvPolynomial.eval (fun i => x.ofLp i) (linPoly t ^ n) : ℝ)) : ℂ)) (γ N) :=
      hre.ofReal.const_mul (Complex.I ^ n / (n.factorial : ℂ))
    refine hc.congr (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [MvPolynomial.eval_pow, eval_linPoly, mul_pow, Complex.ofReal_mul, Complex.ofReal_pow]
    ring
  unfold expSum
  simp only [Finset.mul_sum]
  rw [integral_finsetSum]
  · exact Finset.sum_eq_zero (fun n _ => key n)
  · intro n hn
    exact hint n hn

private lemma tendsto_integral_expSum (N : ℕ) (φ : EuclideanSpace ℝ (Fin N) → ℝ)
    (hφ : MemLp φ 2 (γ N)) (t : EuclideanSpace ℝ (Fin N)) :
    Filter.Tendsto (fun M => ∫ x, (φ x : ℂ) * expSum t M x ∂(γ N)) Filter.atTop
      (nhds (∫ x, (φ x : ℂ) * Complex.exp ((↑(inner ℝ x t) : ℂ) * Complex.I) ∂(γ N))) := by
  haveI : IsFiniteMeasure (γ N) := isFiniteMeasure_gamma N
  refine tendsto_integral_of_dominated_convergence
    (bound := fun x => ‖φ x‖ * Real.exp (|inner ℝ x t|)) ?_ ?_ ?_ ?_
  · intro M
    exact (hφ.ofReal.aestronglyMeasurable).mul (continuous_expSum t M).aestronglyMeasurable
  · have h1 : MemLp (fun x : EuclideanSpace ℝ (Fin N) => ‖φ x‖) 2 (γ N) := hφ.norm
    have h2 : MemLp (fun x : EuclideanSpace ℝ (Fin N) => Real.exp |inner ℝ x t|) 2 (γ N) :=
      memLp_exp_abs_inner N t
    exact (memLp_one_iff_integrable).mp (h2.mul' h1)
  · intro M
    filter_upwards with x
    rw [norm_mul]
    have h1 : ‖((φ x : ℝ) : ℂ)‖ = ‖φ x‖ := by simp
    rw [h1]
    gcongr
    exact norm_expSum_le t x M
  · filter_upwards with x
    have hz := hasSum_exp_series (((inner ℝ x t : ℝ) : ℂ) * Complex.I)
    have := (hz.tendsto_sum_nat).const_mul ((φ x : ℂ))
    simpa [expSum, mul_comm, mul_left_comm, mul_assoc] using this

private lemma integral_cexp_mul_zero (N : ℕ) (φ : EuclideanSpace ℝ (Fin N) → ℝ)
    (hφ : MemLp φ 2 (γ N))
    (h : ∀ P : MvPolynomial (Fin N) ℝ,
      ∫ x, φ x * MvPolynomial.eval (fun i => x.ofLp i) P ∂(γ N) = 0)
    (t : EuclideanSpace ℝ (Fin N)) :
    ∫ x, (φ x : ℂ) * Complex.exp ((↑(inner ℝ x t) : ℂ) * Complex.I) ∂(γ N) = 0 := by
  have h0 : Filter.Tendsto (fun M => ∫ x, (φ x : ℂ) * expSum t M x ∂(γ N))
      Filter.atTop (nhds 0) := by
    simp only [integral_expSum_mul N φ hφ h t]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique (tendsto_integral_expSum N φ hφ t) h0

private lemma charFun_withDensity_ofReal (N : ℕ) (u : EuclideanSpace ℝ (Fin N) → ℝ)
    (hu : AEMeasurable u (γ N)) (hu0 : ∀ x, 0 ≤ u x) (t : EuclideanSpace ℝ (Fin N)) :
    charFun ((γ N).withDensity (fun x => ENNReal.ofReal (u x))) t
      = ∫ x, ((u x : ℝ) : ℂ) * Complex.exp ((↑(inner ℝ x t) : ℂ) * Complex.I) ∂(γ N) := by
  rw [charFun_apply]
  rw [integral_withDensity_eq_integral_toReal_smul₀ (hu.ennreal_ofReal)
      (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards with x
  rw [ENNReal.toReal_ofReal (hu0 x), Complex.real_smul]

private lemma integrable_ofReal_mul_cexp (N : ℕ) (φ u : EuclideanSpace ℝ (Fin N) → ℝ)
    (hφ : MemLp φ 2 (γ N)) (t : EuclideanSpace ℝ (Fin N))
    (hu : AEMeasurable u (γ N)) (hu0 : ∀ x, 0 ≤ u x) (hub : ∀ x, u x ≤ |φ x|) :
    Integrable (fun x => ((u x : ℝ) : ℂ) * Complex.exp ((↑(inner ℝ x t) : ℂ) * Complex.I))
      (γ N) := by
  haveI : IsFiniteMeasure (γ N) := isFiniteMeasure_gamma N
  have hb : MemLp φ 1 (γ N) := hφ.mono_exponent (by norm_num)
  have hw : AEMeasurable
      (fun x : EuclideanSpace ℝ (Fin N) => Complex.exp ((↑(inner ℝ x t) : ℂ) * Complex.I))
      (γ N) :=
    (by fun_prop : Continuous
      (fun x : EuclideanSpace ℝ (Fin N) =>
        Complex.exp ((↑(inner ℝ x t) : ℂ) * Complex.I))).aemeasurable
  have hmeas : AEStronglyMeasurable
      (fun x : EuclideanSpace ℝ (Fin N) =>
        ((u x : ℝ) : ℂ) * Complex.exp ((↑(inner ℝ x t) : ℂ) * Complex.I)) (γ N) :=
    ((Complex.continuous_ofReal.measurable.comp_aemeasurable hu).mul hw).aestronglyMeasurable
  refine (memLp_one_iff_integrable).mp (MemLp.of_le hb hmeas ?_)
  filter_upwards with x
  rw [norm_mul]
  have h1 : Complex.re ((↑(inner ℝ x t) : ℂ) * Complex.I) = 0 := by simp
  rw [Complex.norm_exp, h1, Real.exp_zero, mul_one]
  have h2 : ‖((u x : ℝ) : ℂ)‖ = u x := by
    rw [show ‖((u x : ℝ) : ℂ)‖ = |u x| from by simp]
    exact abs_of_nonneg (hu0 x)
  rw [h2]
  simpa [Real.norm_eq_abs] using hub x

/-- **The multivariate polynomials are dense in `L²` of the standard Gaussian measure on
`ℝ^N`.** If `φ ∈ L²(e^{-‖x‖²/2} dx)` is orthogonal to every (multivariate) polynomial, then `φ`
vanishes a.e.

This is the `N`-dimensional companion of
`Commons.Analysis.GaussianMeasure.hermite_basis_L2_gaussian`; the proof expands the exponential
generating function `t ↦ e^{i⟪t,x⟫}` in its Taylor series (all of whose terms integrate to zero
against `φ` by the hypothesis) and then compares the characteristic functions of the positive and
negative parts of `φ` with `Measure.ext_of_charFun`. -/
theorem ae_zero_of_forall_mvpoly_integral_eq_zero {N : ℕ}
    (φ : EuclideanSpace ℝ (Fin N) → ℝ)
    (hφ : MemLp φ 2 (volume.withDensity
      (fun x : EuclideanSpace ℝ (Fin N) => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2 / 2)))))
    (h : ∀ P : MvPolynomial (Fin N) ℝ,
      ∫ x, φ x * MvPolynomial.eval (fun i => x.ofLp i) P
        ∂(volume.withDensity
          (fun x : EuclideanSpace ℝ (Fin N) => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2 / 2)))) = 0) :
    φ =ᵐ[volume.withDensity
      (fun x : EuclideanSpace ℝ (Fin N) => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2 / 2)))] 0 := by
  haveI : IsFiniteMeasure (γ N) := isFiniteMeasure_gamma N
  have hφ1 : MemLp φ 1 (γ N) := hφ.mono_exponent (by norm_num)
  have hφm : AEMeasurable φ (γ N) := hφ.aestronglyMeasurable.aemeasurable
  have hppm : AEMeasurable (fun x : EuclideanSpace ℝ (Fin N) => max (φ x) 0) (γ N) :=
    hφm.max aemeasurable_const
  have hnnm : AEMeasurable (fun x : EuclideanSpace ℝ (Fin N) => max (-(φ x)) 0) (γ N) :=
    hφm.neg.max aemeasurable_const
  have hfin : ∫⁻ x, ENNReal.ofReal (max (φ x) 0) ∂(γ N) ≠ ⊤ := by
    have hle : ∫⁻ x, ENNReal.ofReal (max (φ x) 0) ∂(γ N) ≤ ∫⁻ x, ‖φ x‖ₑ ∂(γ N) := by
      apply lintegral_mono
      intro x
      change ENNReal.ofReal (max (φ x) 0) ≤ ‖φ x‖ₑ
      rw [Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal (max_le (le_abs_self (φ x)) (abs_nonneg (φ x)))
    have hlt : ∫⁻ x, ‖φ x‖ₑ ∂(γ N) < ⊤ := by
      rw [← eLpNorm_one_eq_lintegral_enorm]
      exact hφ1.eLpNorm_lt_top
    exact ne_of_lt (lt_of_le_of_lt hle hlt)
  have hfin' : ∫⁻ x, ENNReal.ofReal (max (-(φ x)) 0) ∂(γ N) ≠ ⊤ := by
    have hle : ∫⁻ x, ENNReal.ofReal (max (-(φ x)) 0) ∂(γ N) ≤ ∫⁻ x, ‖φ x‖ₑ ∂(γ N) := by
      apply lintegral_mono
      intro x
      change ENNReal.ofReal (max (-(φ x)) 0) ≤ ‖φ x‖ₑ
      rw [Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal (max_le (neg_le_abs (φ x)) (abs_nonneg (φ x)))
    have hlt : ∫⁻ x, ‖φ x‖ₑ ∂(γ N) < ⊤ := by
      rw [← eLpNorm_one_eq_lintegral_enorm]
      exact hφ1.eLpNorm_lt_top
    exact ne_of_lt (lt_of_le_of_lt hle hlt)
  let νp : Measure (EuclideanSpace ℝ (Fin N)) :=
    (γ N).withDensity (fun x => ENNReal.ofReal (max (φ x) 0))
  let νn : Measure (EuclideanSpace ℝ (Fin N)) :=
    (γ N).withDensity (fun x => ENNReal.ofReal (max (-(φ x)) 0))
  have hchar : charFun νp = charFun νn := by
    funext t
    have hp := charFun_withDensity_ofReal N (fun x => max (φ x) 0) hppm
      (fun x => le_max_right _ _) t
    have hn := charFun_withDensity_ofReal N (fun x => max (-(φ x)) 0) hnnm
      (fun x => le_max_right _ _) t
    rw [hp, hn]
    have hIp : Integrable
        (fun x : EuclideanSpace ℝ (Fin N) =>
          (((max (φ x) 0 : ℝ)) : ℂ) * Complex.exp ((↑(inner ℝ x t) : ℂ) * Complex.I))
        (γ N) :=
      integrable_ofReal_mul_cexp N φ (fun x => max (φ x) 0) hφ t hppm
        (fun x => le_max_right _ _) (fun x => max_le (le_abs_self _) (abs_nonneg _))
    have hIn : Integrable
        (fun x : EuclideanSpace ℝ (Fin N) =>
          (((max (-(φ x)) 0 : ℝ)) : ℂ) * Complex.exp ((↑(inner ℝ x t) : ℂ) * Complex.I))
        (γ N) :=
      integrable_ofReal_mul_cexp N φ (fun x => max (-(φ x)) 0) hφ t hnnm
        (fun x => le_max_right _ _) (fun x => max_le (neg_le_abs _) (abs_nonneg _))
    have hsub : (∫ x, (((max (φ x) 0 : ℝ)) : ℂ) *
          Complex.exp ((↑(inner ℝ x t) : ℂ) * Complex.I) ∂(γ N))
        - (∫ x, (((max (-(φ x)) 0 : ℝ)) : ℂ) *
          Complex.exp ((↑(inner ℝ x t) : ℂ) * Complex.I) ∂(γ N))
        = ∫ x, (φ x : ℂ) * Complex.exp ((↑(inner ℝ x t) : ℂ) * Complex.I) ∂(γ N) := by
      rw [← integral_sub hIp hIn]
      apply integral_congr_ae
      filter_upwards with x
      have hx : max (φ x) 0 - max (-(φ x)) 0 = φ x := by
        rcases le_total 0 (φ x) with hh | hh
        · rw [max_eq_left hh, max_eq_right (by linarith)]; ring
        · rw [max_eq_right hh, max_eq_left (by linarith)]; ring
      rw [← sub_mul, ← Complex.ofReal_sub, hx]
    exact sub_eq_zero.mp (by rw [hsub, integral_cexp_mul_zero N φ hφ h t])
  have hν : νp = νn := by
    haveI : IsFiniteMeasure νp := isFiniteMeasure_withDensity hfin
    haveI : IsFiniteMeasure νn := by
      rw [show νn = (γ N).withDensity (fun x => ENNReal.ofReal (max (-(φ x)) 0)) from rfl]
      exact isFiniteMeasure_withDensity hfin'
    exact Measure.ext_of_charFun hchar
  have hae : (fun x : EuclideanSpace ℝ (Fin N) => ENNReal.ofReal (max (φ x) 0)) =ᵐ[γ N]
      (fun x : EuclideanSpace ℝ (Fin N) => ENNReal.ofReal (max (-(φ x)) 0)) := by
    have := withDensity_eq_iff (hppm.ennreal_ofReal) (hnnm.ennreal_ofReal) hfin
    exact this.mp hν
  filter_upwards [hae] with x hx
  have hx' : max (φ x) 0 = max (-(φ x)) 0 := by
    have h1 : (ENNReal.ofReal (max (φ x) 0)).toReal
        = (ENNReal.ofReal (max (-(φ x)) 0)).toReal := congrArg ENNReal.toReal hx
    rwa [ENNReal.toReal_ofReal (le_max_right (φ x) 0),
      ENNReal.toReal_ofReal (le_max_right (-(φ x)) 0)] at h1
  have : φ x = 0 := by
    have hx'' : max (φ x) 0 - max (-(φ x)) 0 = φ x := by
      rcases le_total 0 (φ x) with hh | hh
      · rw [max_eq_left hh, max_eq_right (by linarith)]; ring
      · rw [max_eq_right hh, max_eq_left (by linarith)]; ring
    rw [← hx'', hx']; ring
  exact this

theorem hermite_product_dense_L2 {N : ℕ} (f : EuclideanSpace ℝ (Fin N) → ℝ)
    (hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume.withDensity
      (fun x : EuclideanSpace ℝ (Fin N) => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2 / 2)))))
    (h : ∀ α : Fin N → ℕ, ∫ x : EuclideanSpace ℝ (Fin N),
        f x * (∏ i, Polynomial.aeval (x.ofLp i) (Polynomial.hermite (α i)))
        ∂(MeasureTheory.volume.withDensity
          (fun x : EuclideanSpace ℝ (Fin N) => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2 / 2)))) = 0) :
    f =ᵐ[MeasureTheory.volume.withDensity
      (fun x : EuclideanSpace ℝ (Fin N) => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2 / 2)))] 0 := by
  have hint : ∀ P : MvPolynomial (Fin N) ℝ, Integrable
      (fun x : EuclideanSpace ℝ (Fin N) => f x * MvPolynomial.eval (fun i => x.ofLp i) P)
      (γ N) := by
    intro P
    exact (memLp_one_iff_integrable).mp
      ((memLp_mvpoly_withDensity_exp_neg_sq_half P).mul' hf)
  have hpoly := integral_mul_mvpoly_eq_zero_of_hermite (n := N) f hint h
  exact ae_zero_of_forall_mvpoly_integral_eq_zero f hf hpoly

end Commons.Analysis.GaussianMeasure
