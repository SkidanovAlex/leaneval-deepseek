import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.AliasAux
import Submission.Work.BoseBoxFock.aliasSupport
import Submission.Work.BoseBoxFock.combHeat
import Submission.Work.BoseBoxFock.sqrtKin_diffForm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.aliasIdentity`

The Poisson/aliasing identity of the middle-range comparison:

    `latHeat ℓ t g − contHeat g t = Σ_{m ≠ 0} ∫_u aliasKernel g u · heatK t (ℓ • latVec m − u)`

for `g` smooth with `tsupport g ⊆ ball 0 (ℓ/2)`.  The two sides are the lattice sum and the
continuum integral of the heat content, the difference being the lattice sum over the non-zero
images `ℓ • latVec m`.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 800000

/-- Moving `re` inside a Bochner integral. -/
lemma re_integral_eq {f : E3 → ℂ} (hf : Integrable f volume) :
    (∫ x, f x).re = ∫ x, (f x).re := by
  have h := ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ) Complex.reCLM hf
  have hre : ∀ z : ℂ, Complex.reCLM z = z.re := fun z => rfl
  simpa only [hre] using h.symm

lemma re_ofReal_mul (r : ℝ) (z : ℂ) : ((r : ℂ) * z).re = r * z.re := by
  simp [Complex.mul_re]

lemma re_mul_ofReal (z : ℂ) (r : ℝ) : (z * (r : ℂ)).re = z.re * r := by
  simp [Complex.mul_re]

/-- The `(p,u)`-phase `e^{−I⟪p,u⟫}` is continuous. -/
lemma continuous_phase : Continuous (fun q : E3 × E3 =>
    Complex.exp (-(Complex.I * (inner ℝ q.1 q.2 : ℂ)))) := by
  refine Complex.continuous_exp.comp ?_
  refine Continuous.neg ?_
  exact continuous_const.mul (Complex.continuous_ofReal.comp
    (continuous_inner.comp (continuous_fst.prodMk continuous_snd)))

/-! ## 0. The mode weight of the lattice heat content -/

/-- The mode weight `(ℓ³)⁻¹ e^{−t‖k_n‖²}` of the lattice heat content. -/
noncomputable def latWeight (ℓ t : ℝ) (n : Fin 3 → ℤ) : ℝ :=
  (ℓ ^ 3)⁻¹ * Real.exp (-(t * ‖kmomInt ℓ n‖ ^ 2))

lemma latWeight_apply (ℓ t : ℝ) (n : Fin 3 → ℤ) :
    latWeight ℓ t n = (ℓ ^ 3)⁻¹ * Real.exp (-(t * ‖kmomInt ℓ n‖ ^ 2)) := rfl

lemma latWeight_nonneg {ℓ : ℝ} (hℓ : 0 < ℓ) (t : ℝ) (n : Fin 3 → ℤ) :
    0 ≤ latWeight ℓ t n := by
  rw [latWeight_apply]
  exact mul_nonneg (by positivity) (Real.exp_nonneg _)

lemma summable_latWeight {ℓ t : ℝ} (hℓ : 0 < ℓ) (ht : 0 < t) :
    Summable (latWeight ℓ t : (Fin 3 → ℤ) → ℝ) :=
  (summable_exp_neg_kmomInt hℓ ht).mul_left _

/-! ## 1. The continuum heat content as the diagonal term -/

/-- `contHeat` is the `kinHeat` of the SqrtKin chapter (same definition). -/
theorem contHeat_eq_kinHeat (g : E3 → ℂ) (t : ℝ) : contHeat g t = kinHeat g t := rfl

/-- **The `m = 0` term.**  For `g` smooth with compact support and `t > 0`,
`contHeat g t = ∫_u aliasKernel g u · heatK t u`. -/
theorem contHeat_heatK_aux {g : E3 → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) {t : ℝ} (ht : 0 < t) :
    contHeat g t = ∫ u : E3, aliasKernel g u * heatK t u := by
  have hAc : Continuous (autocorr g) := autocorr_continuous hg hgc
  have hAcontr : Integrable (autocorr g) volume := autocorr_integrable hg hgc
  have hG : Integrable (fun p : E3 => Real.exp (-(t * ‖p‖ ^ 2))) :=
    integrable_exp_neg_mul_norm_sq t ht
  have hAint : ∀ p : E3, Integrable (fun u : E3 =>
      autocorr g u * Complex.exp (-(Complex.I * (inner ℝ p u : ℂ)))) := by
    intro p
    have hph : Continuous (fun u : E3 =>
        Complex.exp (-(Complex.I * (inner ℝ p u : ℂ)))) := by
      refine Complex.continuous_exp.comp ?_
      refine Continuous.neg ?_
      exact continuous_const.mul (Complex.continuous_ofReal.comp
        (continuous_inner.comp (continuous_const.prodMk continuous_id)))
    refine Integrable.mono' hAcontr.norm (hAc.mul hph).aestronglyMeasurable ?_
    · filter_upwards with u
      rw [norm_mul, norm_cexp_neg_I_inner, mul_one]
  -- the joint integrand of the Fubini step
  have hJoint : Integrable (Function.uncurry (fun p u : E3 =>
      Real.exp (-(t * ‖p‖ ^ 2)) *
        (autocorr g u * Complex.exp (-(Complex.I * (inner ℝ p u : ℂ)))).re))
      (volume.prod volume) := by
    have hE : Continuous (fun q : E3 × E3 => Real.exp (-(t * ‖q.1‖ ^ 2))) := by
      refine Real.continuous_exp.comp ?_
      exact (continuous_const.mul ((continuous_norm.comp continuous_fst).pow 2)).neg
    have hcont : Continuous (fun q : E3 × E3 => Real.exp (-(t * ‖q.1‖ ^ 2)) *
        (autocorr g q.2 * Complex.exp (-(Complex.I * (inner ℝ q.1 q.2 : ℂ)))).re) :=
      hE.mul (Complex.continuous_re.comp
        ((hAc.comp continuous_snd).mul continuous_phase))
    refine Integrable.mono' (hG.mul_prod hAcontr.norm) hcont.aestronglyMeasurable ?_
    · filter_upwards with q
      obtain ⟨p, u⟩ := q
      rw [Function.uncurry_apply_pair, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (Real.exp_nonneg _)]
      calc Real.exp (-(t * ‖p‖ ^ 2)) *
            |(autocorr g u * Complex.exp (-(Complex.I * (inner ℝ p u : ℂ)))).re|
          ≤ Real.exp (-(t * ‖p‖ ^ 2)) *
              ‖autocorr g u * Complex.exp (-(Complex.I * (inner ℝ p u : ℂ)))‖ :=
            mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (Real.exp_nonneg _)
        _ = Real.exp (-(t * ‖p‖ ^ 2)) * ‖autocorr g u‖ := by
            rw [norm_mul, norm_cexp_neg_I_inner, mul_one]
  -- integrability of the complex `p`-integrand at fixed `u`
  have hintp : ∀ u : E3, Integrable (fun p : E3 =>
      (Real.exp (-(t * ‖p‖ ^ 2)) : ℂ) *
        (autocorr g u * Complex.exp (-(Complex.I * (inner ℝ p u : ℂ))))) := by
    intro u
    have hph : Continuous (fun p : E3 =>
        Complex.exp (-(Complex.I * (inner ℝ p u : ℂ)))) := by
      refine Complex.continuous_exp.comp ?_
      refine Continuous.neg ?_
      exact continuous_const.mul (Complex.continuous_ofReal.comp
        (continuous_inner.comp (continuous_id.prodMk continuous_const)))
    have hE : Continuous (fun p : E3 => (Real.exp (-(t * ‖p‖ ^ 2)) : ℂ)) :=
      Complex.continuous_ofReal.comp (Real.continuous_exp.comp
        (continuous_const.mul (continuous_norm.pow 2)).neg)
    refine Integrable.mono' (hG.const_mul ‖autocorr g u‖) (hE.mul
      (continuous_const.mul hph)).aestronglyMeasurable ?_
    · filter_upwards with p
      rw [norm_mul, norm_mul, norm_ofReal_complex (Real.exp_nonneg _),
        norm_cexp_neg_I_inner, mul_one, mul_comm]
  have hchain : (∫ p : E3, Real.exp (-(t * ‖p‖ ^ 2)) * ‖Submission.BoseGases.kinFT g p‖ ^ 2)
      = ∫ u : E3, (autocorr g u).re * ((2 * Real.pi) ^ 3 * heatK t u) := by
    calc (∫ p : E3, Real.exp (-(t * ‖p‖ ^ 2)) * ‖Submission.BoseGases.kinFT g p‖ ^ 2)
        = ∫ p : E3, Real.exp (-(t * ‖p‖ ^ 2)) *
            (∫ u : E3, autocorr g u * Complex.exp (-(Complex.I * (inner ℝ p u : ℂ)))).re := by
          apply integral_congr_ae
          filter_upwards with p
          rw [aliasFt hg hgc p]
      _ = ∫ p : E3, Real.exp (-(t * ‖p‖ ^ 2)) *
            (∫ u : E3, (autocorr g u * Complex.exp (-(Complex.I * (inner ℝ p u : ℂ)))).re) := by
          apply integral_congr_ae
          filter_upwards with p
          rw [re_integral_eq (hAint p)]
      _ = ∫ p : E3, ∫ u : E3, Real.exp (-(t * ‖p‖ ^ 2)) *
            (autocorr g u * Complex.exp (-(Complex.I * (inner ℝ p u : ℂ)))).re := by
          apply integral_congr_ae
          filter_upwards with p
          rw [MeasureTheory.integral_const_mul]
      _ = ∫ u : E3, ∫ p : E3, Real.exp (-(t * ‖p‖ ^ 2)) *
            (autocorr g u * Complex.exp (-(Complex.I * (inner ℝ p u : ℂ)))).re :=
          MeasureTheory.integral_integral_swap hJoint
      _ = ∫ u : E3,
            (∫ p : E3, (Real.exp (-(t * ‖p‖ ^ 2)) : ℂ) *
              (autocorr g u * Complex.exp (-(Complex.I * (inner ℝ p u : ℂ))))).re := by
          apply integral_congr_ae
          filter_upwards with u
          rw [re_integral_eq (hintp u)]
          apply integral_congr_ae
          filter_upwards with p
          simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
            mul_zero, sub_zero]
      _ = ∫ u : E3, (autocorr g u * (((2 * Real.pi) ^ 3 * heatK t u : ℝ) : ℂ)).re := by
          apply integral_congr_ae
          filter_upwards with u
          congr 1
          rw [show (fun p : E3 => (Real.exp (-(t * ‖p‖ ^ 2)) : ℂ) *
                (autocorr g u * Complex.exp (-(Complex.I * (inner ℝ p u : ℂ)))))
              = fun p : E3 => autocorr g u * ((Real.exp (-(t * ‖p‖ ^ 2)) : ℂ) *
                Complex.exp (-(Complex.I * (inner ℝ p u : ℂ)))) from by
            funext p; ring]
          rw [MeasureTheory.integral_const_mul, heatK_fourier ht u]
      _ = ∫ u : E3, (autocorr g u).re * ((2 * Real.pi) ^ 3 * heatK t u) := by
          apply integral_congr_ae
          filter_upwards with u
          simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
            mul_zero, sub_zero]
  have hfactor : (∫ u : E3, (autocorr g u).re * ((2 * Real.pi) ^ 3 * heatK t u))
      = (2 * Real.pi) ^ 3 * ∫ u : E3, (autocorr g u).re * heatK t u := by
    rw [← MeasureTheory.integral_const_mul]
    apply integral_congr_ae
    filter_upwards with u
    ring
  rw [contHeat, hchain, hfactor, ← mul_assoc,
    inv_mul_cancel₀ (by positivity : ((2 : ℝ) * Real.pi) ^ 3 ≠ 0), one_mul]
  rfl

/-! ## 2. The lattice heat content as the full image sum -/

/-- **The mode sum.**  For `g` smooth with compact support and `t > 0`,
`latHeat ℓ t g = ∫_u aliasKernel g u · Σ_m heatK t (u − ℓ • latVec m)`. -/
theorem latHeat_periodisation_aux {ℓ : ℝ} (hℓ : 0 < ℓ)
    {g : E3 → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g) (hgc : HasCompactSupport g)
    {t : ℝ} (ht : 0 < t) :
    latHeat ℓ t g
      = ∫ u : E3, aliasKernel g u * (∑' m : Fin 3 → ℤ, heatK t (u - ℓ • latVec m)) := by
  have hAc : Continuous (autocorr g) := autocorr_continuous hg hgc
  have hAcontr : Integrable (autocorr g) volume := autocorr_integrable hg hgc
  have hwsum : Summable (latWeight ℓ t : (Fin 3 → ℤ) → ℝ) := summable_latWeight hℓ ht
  have hph : ∀ n : Fin 3 → ℤ, Continuous (fun u : E3 =>
      Complex.exp (-(Complex.I * (inner ℝ (kmomInt ℓ n) u : ℂ)))) := by
    intro n
    refine Complex.continuous_exp.comp ?_
    refine Continuous.neg ?_
    exact continuous_const.mul (Complex.continuous_ofReal.comp
      (continuous_inner.comp (continuous_const.prodMk continuous_id)))
  have hFint : ∀ n : Fin 3 → ℤ, Integrable (fun u : E3 =>
      autocorr g u * Complex.exp (-(Complex.I * (inner ℝ (kmomInt ℓ n) u : ℂ)))) := by
    intro n
    refine Integrable.mono' hAcontr.norm (hAc.mul (hph n)).aestronglyMeasurable ?_
    · filter_upwards with u
      rw [norm_mul, norm_cexp_neg_I_inner, mul_one]
  have hInt_n : ∀ n : Fin 3 → ℤ, Integrable (fun u : E3 => latWeight ℓ t n *
      (autocorr g u * Complex.exp (-(Complex.I * (inner ℝ (kmomInt ℓ n) u : ℂ)))).re) := by
    intro n
    have hcont : Continuous (fun u : E3 => latWeight ℓ t n *
        (autocorr g u * Complex.exp (-(Complex.I * (inner ℝ (kmomInt ℓ n) u : ℂ)))).re) :=
      continuous_const.mul (Complex.continuous_re.comp (hAc.mul (hph n)))
    refine Integrable.mono' (hAcontr.norm.const_mul (latWeight ℓ t n))
      hcont.aestronglyMeasurable ?_
    · filter_upwards with u
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (latWeight_nonneg hℓ t n)]
      calc latWeight ℓ t n *
            |(autocorr g u * Complex.exp (-(Complex.I * (inner ℝ (kmomInt ℓ n) u : ℂ)))).re|
          ≤ latWeight ℓ t n *
              ‖autocorr g u * Complex.exp (-(Complex.I * (inner ℝ (kmomInt ℓ n) u : ℂ)))‖ :=
            mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (latWeight_nonneg hℓ t n)
        _ = latWeight ℓ t n * ‖autocorr g u‖ := by
            rw [norm_mul, norm_cexp_neg_I_inner, mul_one]
  have hInt_summable : Summable (fun n : Fin 3 → ℤ => ∫ u : E3, ‖latWeight ℓ t n *
      (autocorr g u * Complex.exp (-(Complex.I * (inner ℝ (kmomInt ℓ n) u : ℂ)))).re‖) := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg (fun u => norm_nonneg _))
      (fun n => ?_) (hwsum.mul_right (∫ u : E3, ‖autocorr g u‖))
    calc ∫ u : E3, ‖latWeight ℓ t n *
          (autocorr g u * Complex.exp (-(Complex.I * (inner ℝ (kmomInt ℓ n) u : ℂ)))).re‖
        ≤ ∫ u : E3, latWeight ℓ t n * ‖autocorr g u‖ := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun u => norm_nonneg _))
            ((hAcontr.norm).const_mul (latWeight ℓ t n)) ?_
          filter_upwards with u
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (latWeight_nonneg hℓ t n)]
          calc latWeight ℓ t n *
                |(autocorr g u * Complex.exp (-(Complex.I * (inner ℝ (kmomInt ℓ n) u : ℂ)))).re|
              ≤ latWeight ℓ t n *
                  ‖autocorr g u * Complex.exp (-(Complex.I * (inner ℝ (kmomInt ℓ n) u : ℂ)))‖ :=
                mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (latWeight_nonneg hℓ t n)
            _ = latWeight ℓ t n * ‖autocorr g u‖ := by
                rw [norm_mul, norm_cexp_neg_I_inner, mul_one]
      _ = latWeight ℓ t n * ∫ u : E3, ‖autocorr g u‖ := by
          rw [MeasureTheory.integral_const_mul]
  calc latHeat ℓ t g
      = ∑' n : Fin 3 → ℤ, latWeight ℓ t n *
          (∫ u : E3, autocorr g u *
            Complex.exp (-(Complex.I * (inner ℝ (kmomInt ℓ n) u : ℂ)))).re := by
          rw [latHeat]
          apply tsum_congr
          intro n
          rw [aliasFt hg hgc (kmomInt ℓ n), latWeight_apply]
      _ = ∑' n : Fin 3 → ℤ, ∫ u : E3, latWeight ℓ t n *
          (autocorr g u * Complex.exp (-(Complex.I * (inner ℝ (kmomInt ℓ n) u : ℂ)))).re := by
          apply tsum_congr
          intro n
          rw [re_integral_eq (hFint n), ← MeasureTheory.integral_const_mul]
      _ = ∫ u : E3, ∑' n : Fin 3 → ℤ, latWeight ℓ t n *
          (autocorr g u * Complex.exp (-(Complex.I * (inner ℝ (kmomInt ℓ n) u : ℂ)))).re :=
          (integral_tsum_of_summable_integral_norm hInt_n hInt_summable)
      _ = ∫ u : E3, (autocorr g u).re *
          (∑' m : Fin 3 → ℤ, heatK t (u - ℓ • latVec m)) := by
          apply integral_congr_ae
          filter_upwards with u
          have hsum1 : Summable (fun n : Fin 3 → ℤ => (latWeight ℓ t n : ℂ) *
              Complex.exp (-(Complex.I * (inner ℝ (kmomInt ℓ n) u : ℂ)))) := by
            refine Summable.of_norm_bounded hwsum (fun n => ?_)
            rw [norm_mul, norm_ofReal_complex (latWeight_nonneg hℓ t n),
              norm_cexp_neg_I_inner, mul_one]
          have hsum2 : Summable (fun n : Fin 3 → ℤ => autocorr g u *
              ((latWeight ℓ t n : ℂ) *
                Complex.exp (-(Complex.I * (inner ℝ (kmomInt ℓ n) u : ℂ))))) :=
            hsum1.mul_left _
          have hW : (∑' n : Fin 3 → ℤ, (latWeight ℓ t n : ℂ) *
                Complex.exp (-(Complex.I * (inner ℝ (kmomInt ℓ n) u : ℂ))))
              = ((∑' m : Fin 3 → ℤ, heatK t (u - ℓ • latVec m) : ℝ) : ℂ) := by
            rw [show (∑' n : Fin 3 → ℤ, (latWeight ℓ t n : ℂ) *
                  Complex.exp (-(Complex.I * (inner ℝ (kmomInt ℓ n) u : ℂ))))
                = ∑' n : Fin 3 → ℤ, Complex.ofReal ((ℓ ^ 3)⁻¹) *
                    Complex.ofReal (Real.exp (-(t * ‖kmomInt ℓ n‖ ^ 2))) *
                    Complex.exp (-(Complex.I * (inner ℝ (kmomInt ℓ n) u : ℂ))) from by
              apply tsum_congr
              intro n
              rw [latWeight_apply, Complex.ofReal_mul]]
            rw [combHeat hℓ ht u, ← Complex.ofReal_tsum]
          rw [show (∑' n : Fin 3 → ℤ, latWeight ℓ t n *
                (autocorr g u * Complex.exp (-(Complex.I * (inner ℝ (kmomInt ℓ n) u : ℂ)))).re)
              = ∑' n : Fin 3 → ℤ, (autocorr g u * ((latWeight ℓ t n : ℂ) *
                Complex.exp (-(Complex.I * (inner ℝ (kmomInt ℓ n) u : ℂ))))).re from by
            apply tsum_congr
            intro n
            rw [← re_ofReal_mul]
            congr 1
            ring]
          rw [← Complex.re_tsum hsum2, tsum_mul_left, hW, re_mul_ofReal]

/-! ## 3. The image remainder -/

lemma aliasLatVec_zero : latVec (0 : Fin 3 → ℤ) = (0 : E3) := by
  ext i
  rw [latVec_apply]
  simp

/-- The pointwise Gaussian decay of `heatK t (u − ℓ • latVec m)` on the ball of radius `ℓ`. -/
lemma heatK_shift_le {ℓ t : ℝ} (hℓ : 0 < ℓ) (ht : 0 < t) (m : Fin 3 → ℤ) {u : E3}
    (hu : ‖u‖ ≤ ℓ) :
    heatK t (u - ℓ • latVec m)
      ≤ (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) * Real.exp (ℓ ^ 2 / (4 * t))
        * Real.exp (-(ℓ ^ 2 / (16 * t)) * ‖latVec m‖ ^ 2) := by
  have hx : ‖latVec m‖ ^ 2 / 4 - 1 ≤ (‖latVec m‖ - 1) ^ 2 := by
    nlinarith [sq_nonneg (‖latVec m‖ - 4 / 3)]
  have hkey : ℓ ^ 2 * ‖latVec m‖ ^ 2 / 4 - ℓ ^ 2 ≤ ‖u - ℓ • latVec m‖ ^ 2 := by
    rcases le_total (2 : ℝ) ‖latVec m‖ with h2 | h2
    · have h1 : ‖ℓ • latVec m‖ ≤ ‖ℓ • latVec m - u‖ + ‖u‖ := by
        have h := norm_add_le (ℓ • latVec m - u) u
        rwa [sub_add_cancel] at h
      rw [norm_smul, Real.norm_of_nonneg hℓ.le] at h1
      rw [norm_sub_rev] at h1
      have hnl : ℓ * ‖latVec m‖ - ℓ ≤ ‖u - ℓ • latVec m‖ := by linarith
      have h0 : 0 ≤ ℓ * ‖latVec m‖ - ℓ := by nlinarith
      have hs : (ℓ * ‖latVec m‖ - ℓ) ^ 2 ≤ ‖u - ℓ • latVec m‖ ^ 2 := by
        nlinarith [hnl, h0, norm_nonneg (u - ℓ • latVec m)]
      have hmul := mul_le_mul_of_nonneg_left hx (sq_nonneg ℓ)
      nlinarith [hs, hmul]
    · have h4 : ‖latVec m‖ ^ 2 ≤ 4 := by nlinarith [h2, norm_nonneg (latVec m)]
      nlinarith [h4, sq_nonneg ℓ, norm_nonneg (u - ℓ • latVec m)]
  rw [heatK]
  rw [show (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) * Real.exp (ℓ ^ 2 / (4 * t))
        * Real.exp (-(ℓ ^ 2 / (16 * t)) * ‖latVec m‖ ^ 2)
      = (4 * Real.pi * t) ^ (-(3 : ℝ) / 2)
        * Real.exp (ℓ ^ 2 / (4 * t) + -(ℓ ^ 2 / (16 * t)) * ‖latVec m‖ ^ 2) from by
    rw [mul_assoc, Real.exp_add]]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by positivity) _)
  rw [Real.exp_le_exp]
  have h4t : (0 : ℝ) < 4 * t := by positivity
  rw [show -(‖u - ℓ • latVec m‖ ^ 2 / (4 * t))
      = -(‖u - ℓ • latVec m‖ ^ 2) / (4 * t) from (neg_div _ _).symm, div_le_iff₀ h4t]
  have harith : (ℓ ^ 2 / (4 * t) + -(ℓ ^ 2 / (16 * t)) * ‖latVec m‖ ^ 2) * (4 * t)
      = ℓ ^ 2 - ℓ ^ 2 * ‖latVec m‖ ^ 2 / 4 := by
    field_simp
    ring
  rw [harith]
  linarith [hkey]

theorem aliasRemainder_aux {ℓ : ℝ} (hℓ : 0 < ℓ)
    {g : E3 → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgsupp : tsupport g ⊆ Metric.ball 0 (ℓ/2)) {t : ℝ} (ht : 0 < t) :
    (∫ u : E3, aliasKernel g u * (∑' m : Fin 3 → ℤ, heatK t (u - ℓ • latVec m)))
      - (∫ u : E3, aliasKernel g u * heatK t u)
      = ∑' m : Fin 3 → ℤ, (if m = 0 then 0 else
          ∫ u : E3, aliasKernel g u * heatK t (ℓ • latVec m - u)) := by
  have hgc : HasCompactSupport g := by
    rw [HasCompactSupport, Metric.isCompact_iff_isClosed_bounded]
    exact ⟨isClosed_tsupport g, Metric.isBounded_ball.subset hgsupp⟩
  have hAc : Continuous (autocorr g) := autocorr_continuous hg hgc
  have hB : 0 ≤ ∫ x : E3, ‖g x‖ ^ 2 := integral_nonneg (fun x => by positivity)
  have hbound : ∀ u : E3, ‖aliasKernel g u‖ ≤ ∫ x : E3, ‖g x‖ ^ 2 := fun u =>
    le_trans (Complex.abs_re_le_norm _) (autocorr_norm_le hg hgc u)
  have hzero : ∀ u : E3, ℓ ≤ ‖u‖ → aliasKernel g u = 0 := fun u hu => by
    show (autocorr g u).re = 0
    rw [autocorr_eq_zero_of_le_norm hℓ hg hgsupp hu]
    simp
  have hVfin : volume (Metric.closedBall (0 : E3) ℓ) < ⊤ :=
    (isCompact_closedBall (0 : E3) ℓ).measure_lt_top
  have hKint : ∀ m : Fin 3 → ℤ, Integrable (fun u : E3 =>
      aliasKernel g u * heatK t (u - ℓ • latVec m)) volume := by
    intro m
    have hcont : Continuous (fun u : E3 => aliasKernel g u * heatK t (u - ℓ • latVec m)) :=
      (Complex.continuous_re.comp hAc).mul
        ((heatK_continuous ht).comp (continuous_id.sub continuous_const))
    have hsh : Integrable (fun u : E3 => heatK t (u - ℓ • latVec m)) volume := by
      have h := (MeasureTheory.measurePreserving_add_right volume (-(ℓ • latVec m))).integrable_comp_of_integrable
        (integrable_heatK ht)
      simpa [Function.comp_def, sub_eq_add_neg] using h
    refine Integrable.mono' (hsh.const_mul (∫ x : E3, ‖g x‖ ^ 2))
      hcont.aestronglyMeasurable ?_
    · filter_upwards with u
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatK_nonneg ht.le _)]
      exact mul_le_mul_of_nonneg_right (hbound u) (heatK_nonneg ht.le _)
  have hImageLe : ∀ m : Fin 3 → ℤ, (∫ u : E3, ‖aliasKernel g u * heatK t (u - ℓ • latVec m)‖)
      ≤ (∫ x : E3, ‖g x‖ ^ 2) * ((volume.real (Metric.closedBall (0 : E3) ℓ)) *
          ((4 * Real.pi * t) ^ (-(3 : ℝ) / 2) * Real.exp (ℓ ^ 2 / (4 * t)) *
            Real.exp (-(ℓ ^ 2 / (16 * t)) * ‖latVec m‖ ^ 2))) := by
    intro m
    have hpt : ∀ u : E3, ‖aliasKernel g u * heatK t (u - ℓ • latVec m)‖
        ≤ (Metric.closedBall (0 : E3) ℓ).indicator
            (fun u => (∫ x : E3, ‖g x‖ ^ 2) * heatK t (u - ℓ • latVec m)) u := by
      intro u
      by_cases hu : u ∈ Metric.closedBall (0 : E3) ℓ
      · rw [Set.indicator_of_mem hu, Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (heatK_nonneg ht.le _)]
        exact mul_le_mul_of_nonneg_right (hbound u) (heatK_nonneg ht.le _)
      · rw [Set.indicator_of_notMem hu]
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hu
        rw [hzero u (le_of_lt (lt_of_not_ge hu)), zero_mul, norm_zero]
    have hmaj : Integrable ((Metric.closedBall (0 : E3) ℓ).indicator
        (fun u => (∫ x : E3, ‖g x‖ ^ 2) * heatK t (u - ℓ • latVec m))) volume := by
      have hsh : Integrable (fun u : E3 => heatK t (u - ℓ • latVec m)) volume := by
        have h := (MeasureTheory.measurePreserving_add_right volume (-(ℓ • latVec m))).integrable_comp_of_integrable
          (integrable_heatK ht)
        simpa [Function.comp_def, sub_eq_add_neg] using h
      exact (hsh.const_mul (∫ x : E3, ‖g x‖ ^ 2)).indicator measurableSet_closedBall
    have hsetint : (∫ u in Metric.closedBall (0 : E3) ℓ, heatK t (u - ℓ • latVec m))
        ≤ (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) * Real.exp (ℓ ^ 2 / (4 * t))
            * Real.exp (-(ℓ ^ 2 / (16 * t)) * ‖latVec m‖ ^ 2)
          * volume.real (Metric.closedBall (0 : E3) ℓ) := by
      have hnn : 0 ≤ ∫ u in Metric.closedBall (0 : E3) ℓ, heatK t (u - ℓ • latVec m) :=
        integral_nonneg (fun u => heatK_nonneg ht.le _)
      calc ∫ u in Metric.closedBall (0 : E3) ℓ, heatK t (u - ℓ • latVec m)
          = ‖∫ u in Metric.closedBall (0 : E3) ℓ, heatK t (u - ℓ • latVec m)‖ :=
            (Real.norm_of_nonneg hnn).symm
        _ ≤ ((4 * Real.pi * t) ^ (-(3 : ℝ) / 2) * Real.exp (ℓ ^ 2 / (4 * t))
              * Real.exp (-(ℓ ^ 2 / (16 * t)) * ‖latVec m‖ ^ 2))
              * volume.real (Metric.closedBall (0 : E3) ℓ) :=
            norm_setIntegral_le_of_norm_le_const hVfin (fun u hu => by
              rw [Real.norm_of_nonneg (heatK_nonneg ht.le _)]
              exact heatK_shift_le hℓ ht m (by
                simpa [dist_eq_norm] using Metric.mem_closedBall.mp hu))
    calc (∫ u : E3, ‖aliasKernel g u * heatK t (u - ℓ • latVec m)‖)
        ≤ ∫ u : E3, (Metric.closedBall (0 : E3) ℓ).indicator
            (fun u => (∫ x : E3, ‖g x‖ ^ 2) * heatK t (u - ℓ • latVec m)) u :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall (fun u => norm_nonneg _)) hmaj
            (Filter.Eventually.of_forall hpt)
      _ = ∫ u in Metric.closedBall (0 : E3) ℓ,
            (∫ x : E3, ‖g x‖ ^ 2) * heatK t (u - ℓ • latVec m) := by
          rw [integral_indicator measurableSet_closedBall]
      _ = (∫ x : E3, ‖g x‖ ^ 2) * ∫ u in Metric.closedBall (0 : E3) ℓ,
            heatK t (u - ℓ • latVec m) := by
          rw [MeasureTheory.integral_const_mul]
      _ ≤ (∫ x : E3, ‖g x‖ ^ 2) * (volume.real (Metric.closedBall (0 : E3) ℓ) *
            ((4 * Real.pi * t) ^ (-(3 : ℝ) / 2) * Real.exp (ℓ ^ 2 / (4 * t))
              * Real.exp (-(ℓ ^ 2 / (16 * t)) * ‖latVec m‖ ^ 2))) := by
          refine mul_le_mul_of_nonneg_left ?_ hB
          calc ∫ u in Metric.closedBall (0 : E3) ℓ, heatK t (u - ℓ • latVec m)
              ≤ ((4 * Real.pi * t) ^ (-(3 : ℝ) / 2) * Real.exp (ℓ ^ 2 / (4 * t))
                  * Real.exp (-(ℓ ^ 2 / (16 * t)) * ‖latVec m‖ ^ 2))
                * volume.real (Metric.closedBall (0 : E3) ℓ) := hsetint
            _ = volume.real (Metric.closedBall (0 : E3) ℓ)
                * ((4 * Real.pi * t) ^ (-(3 : ℝ) / 2) * Real.exp (ℓ ^ 2 / (4 * t))
                  * Real.exp (-(ℓ ^ 2 / (16 * t)) * ‖latVec m‖ ^ 2)) := by ring
  have hdecay : Summable (fun m : Fin 3 → ℤ =>
      Real.exp (-(ℓ ^ 2 / (16 * t)) * ‖latVec m‖ ^ 2)) :=
    Work.BoseFixR.LatGreen.summable_exp_neg_norm_latVec_sq (by positivity)
  have hIntSummable : Summable (fun m : Fin 3 → ℤ =>
      ∫ u : E3, ‖aliasKernel g u * heatK t (u - ℓ • latVec m)‖) := by
    refine Summable.of_nonneg_of_le (fun m => integral_nonneg (fun u => norm_nonneg _))
      hImageLe ?_
    have hcomp : Summable (fun m : Fin 3 → ℤ =>
        volume.real (Metric.closedBall (0 : E3) ℓ) *
          ((4 * Real.pi * t) ^ (-(3 : ℝ) / 2) * Real.exp (ℓ ^ 2 / (4 * t))
            * Real.exp (-(ℓ ^ 2 / (16 * t)) * ‖latVec m‖ ^ 2))) :=
      (hdecay.mul_left ((4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
        Real.exp (ℓ ^ 2 / (4 * t)))).mul_left (volume.real (Metric.closedBall (0 : E3) ℓ))
    exact hcomp.mul_left (∫ x : E3, ‖g x‖ ^ 2)
  have hSummable : Summable (fun m : Fin 3 → ℤ =>
      ∫ u : E3, aliasKernel g u * heatK t (u - ℓ • latVec m)) :=
    Summable.of_norm_bounded hIntSummable (fun m => norm_integral_le_integral_norm _)
  have hSumPt : ∀ u : E3, Summable (fun m : Fin 3 → ℤ =>
      aliasKernel g u * heatK t (u - ℓ • latVec m)) := fun u =>
    (summable_heatK_latticeShift hℓ ht u).mul_left _
  have h1 : (∫ u : E3, aliasKernel g u * (∑' m : Fin 3 → ℤ, heatK t (u - ℓ • latVec m)))
      = ∑' m : Fin 3 → ℤ, ∫ u : E3, aliasKernel g u * heatK t (u - ℓ • latVec m) := by
    rw [show (fun u : E3 => aliasKernel g u * (∑' m : Fin 3 → ℤ, heatK t (u - ℓ • latVec m)))
        = fun u : E3 => ∑' m : Fin 3 → ℤ, aliasKernel g u * heatK t (u - ℓ • latVec m) from by
      funext u
      rw [← tsum_mul_left]]
    exact (integral_tsum_of_summable_integral_norm hKint hIntSummable).symm
  have h2 : ∑' m : Fin 3 → ℤ, ∫ u : E3, aliasKernel g u * heatK t (u - ℓ • latVec m)
      = (∫ u : E3, aliasKernel g u * heatK t u)
        + ∑' m : Fin 3 → ℤ, (if m = 0 then 0 else
            ∫ u : E3, aliasKernel g u * heatK t (u - ℓ • latVec m)) := by
    rw [Summable.tsum_eq_add_tsum_ite hSummable 0]
    congr 1
    apply integral_congr_ae
    filter_upwards with u
    simp [aliasLatVec_zero]
  have h3 : ∑' m : Fin 3 → ℤ, (if m = 0 then 0 else
        ∫ u : E3, aliasKernel g u * heatK t (u - ℓ • latVec m))
      = ∑' m : Fin 3 → ℤ, (if m = 0 then 0 else
          ∫ u : E3, aliasKernel g u * heatK t (ℓ • latVec m - u)) := by
    apply tsum_congr
    intro m
    by_cases hm : m = 0
    · rw [if_pos hm, if_pos hm]
    · rw [if_neg hm, if_neg hm]
      congr 1
      funext u
      rw [show ℓ • latVec m - u = -(u - ℓ • latVec m) by abel, heatK_even]
  rw [h1, h2, h3]
  ring

/-! ## 4. The aliasing identity -/

theorem aliasIdentity {ℓ : ℝ} (hℓ : 0 < ℓ)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgsupp : tsupport g ⊆ Metric.ball 0 (ℓ/2)) {t : ℝ} (ht : 0 < t) :
    Work.BoseBoxFock.latHeat ℓ t g - Work.BoseBoxFock.contHeat g t
      = ∑' m : Fin 3 → ℤ, (if m = 0 then 0 else
          ∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseBoxFock.aliasKernel g u
            * Work.BoseBoxFock.heatK t (ℓ • Work.BoseBoxFock.latVec m - u)) := by
  have hgc : HasCompactSupport g := by
    rw [HasCompactSupport, Metric.isCompact_iff_isClosed_bounded]
    exact ⟨isClosed_tsupport g, Metric.isBounded_ball.subset hgsupp⟩
  rw [latHeat_periodisation_aux hℓ hg hgc ht, contHeat_heatK_aux hg hgc ht]
  exact aliasRemainder_aux hℓ hg hgsupp ht

end Work.BoseBoxFock
