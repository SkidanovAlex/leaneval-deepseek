import Mathlib
import Submission.Commons.Analysis.GaussianMeasure.gaussian_smoothing_lipschitz

open MeasureTheory
open scoped ENNReal

/-!
# The Mehler operator is an L² contraction of the Gaussian measure

For `|ρ| < 1` the Mehler operator
`T_ρ f x = (2 π (1-ρ²))^{-N/2} ∫ y, exp(-‖y - ρ • x‖²/(2(1-ρ²))) f y dy`
is the Ornstein–Uhlenbeck semigroup with correlation `ρ` (equivalently the conditional
expectation `E[f(ρX + √(1-ρ²) Z) | X = x]` for standard Gaussians `X, Z`).  The theorem
below proves that it is a contraction of `L²(e^{-‖x‖²/2} dx)`.

The proof is entirely elementary (no spectral/Fourier theory): the kernel `K(x,·)` is a
probability density in `y` (a Gaussian of variance `1-ρ²`), so Cauchy–Schwarz in `y` gives
`(T_ρ f x)² ≤ ∫ y, K(x,y) f(y)² dy`.  Integrating both sides against `e^{-‖x‖²/2}` and
exchanging the order of integration (Tonelli) reduces the claim to the classical identity
`∫ x, K(x,y) e^{-‖x‖²/2} dx = e^{-‖y‖²/2}`, which follows by completing the square
(`‖y-ρx‖²/(2(1-ρ²)) + ‖x‖²/2 = ‖x-ρy‖²/(2(1-ρ²)) + ‖y‖²/2`) and the Gaussian integral
`∫ z, e^{-‖z‖²/(2σ²)} dz = (2πσ²)^{N/2}`.

The identity holds for all `x` (and for all `y` in the density identity), so only the
hypothesis `f ∈ L²` in the form of the integrability of `f² e^{-‖·‖²/2}` is used, and `f`
is replaced by a measurable representative in the Tonelli step.
-/

namespace Commons.Analysis.GaussianMeasure

/-- Cauchy–Schwarz for weighted integrals over an arbitrary measure space. -/
private lemma sq_int_mul_le_sq_mul {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (a b w : α → ℝ) (hw : ∀ x, 0 ≤ w x)
    (ha : Integrable (fun x => a x ^ 2 * w x) μ)
    (hb : Integrable (fun x => b x ^ 2 * w x) μ) :
    (∫ x, a x * b x * w x ∂μ) ^ 2
      ≤ (∫ x, a x ^ 2 * w x ∂μ) * (∫ x, b x ^ 2 * w x ∂μ) := by
  by_cases hCint : Integrable (fun x => a x * b x * w x) μ
  · set A : ℝ := ∫ x, a x ^ 2 * w x ∂μ with hAdef
    set B : ℝ := ∫ x, b x ^ 2 * w x ∂μ with hBdef
    set C : ℝ := ∫ x, a x * b x * w x ∂μ with hCdef
    have hA0 : 0 ≤ A := by
      rw [hAdef]; exact integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (hw x))
    have hB0 : 0 ≤ B := by
      rw [hBdef]; exact integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (hw x))
    have hquad : ∀ t : ℝ, 0 ≤ A + 2 * t * C + t ^ 2 * B := by
      intro t
      have hg : Integrable (fun x => (2 * t) * (a x * b x * w x)) μ := hCint.const_mul (2 * t)
      have hh : Integrable (fun x => t ^ 2 * (b x ^ 2 * w x)) μ := hb.const_mul (t ^ 2)
      have hcongr : (fun x => (a x + t * b x) ^ 2 * w x)
          =ᵐ[μ] fun x => a x ^ 2 * w x + (2 * t) * (a x * b x * w x)
            + t ^ 2 * (b x ^ 2 * w x) := by
        filter_upwards with x
        ring
      have hval : (∫ x, (a x + t * b x) ^ 2 * w x ∂μ) = A + 2 * t * C + t ^ 2 * B := by
        rw [integral_congr_ae hcongr]
        rw [show (∫ x, a x ^ 2 * w x + (2 * t) * (a x * b x * w x)
              + t ^ 2 * (b x ^ 2 * w x) ∂μ)
            = ∫ x, ((fun y => a y ^ 2 * w y) + (fun y => (2 * t) * (a y * b y * w y))) x
                + (fun y => t ^ 2 * (b y ^ 2 * w y)) x ∂μ from rfl]
        rw [integral_add (ha.add hg) hh, integral_add' ha hg]
        rw [integral_const_mul, integral_const_mul, ← hAdef, ← hCdef, ← hBdef]
      have hnonneg : 0 ≤ ∫ x, (a x + t * b x) ^ 2 * w x ∂μ :=
        integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (hw x))
      rw [hval] at hnonneg
      exact hnonneg
    have hmain : C ^ 2 ≤ A * B := by
      by_cases hBzero : B = 0
      · have hC0 : C = 0 := by
          by_contra hCne
          have h2C : (2 : ℝ) * C ≠ 0 := mul_ne_zero (by norm_num) hCne
          have h := hquad (-(A + 1) / (2 * C))
          have heq : A + 2 * (-(A + 1) / (2 * C)) * C + (-(A + 1) / (2 * C)) ^ 2 * B = -1 := by
            rw [hBzero]
            field_simp
            ring
          linarith [h, eq_comm.mp heq]
        rw [hC0, hBzero]
        norm_num
      · have hBpos : 0 < B := lt_of_le_of_ne hB0 (Ne.symm hBzero)
        have h := hquad (-(C / B))
        have heq : A + 2 * (-(C / B)) * C + (-(C / B)) ^ 2 * B = A - C ^ 2 / B := by
          field_simp
          ring
        have hstep : 0 ≤ A - C ^ 2 / B := by linarith [h, heq]
        have h3 : C ^ 2 / B ≤ A := by linarith [hstep]
        exact (div_le_iff₀ hBpos).mp h3
    exact hmain
  · rw [integral_undef hCint]
    have hA0 : 0 ≤ ∫ x, a x ^ 2 * w x ∂μ :=
      integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (hw x))
    have hB0 : 0 ≤ ∫ x, b x ^ 2 * w x ∂μ :=
      integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (hw x))
    have hmul : 0 ≤ (∫ x, a x ^ 2 * w x ∂μ) * (∫ x, b x ^ 2 * w x ∂μ) := mul_nonneg hA0 hB0
    simpa using hmul

private theorem mehler_aux {N : ℕ} (ρ s2 : ℝ) (hs2 : 0 < s2) (hsum : ρ ^ 2 + s2 = 1)
    (f : EuclideanSpace ℝ (Fin N) → ℝ) (hfmeas : Measurable f)
    (hint : Integrable (fun x : EuclideanSpace ℝ (Fin N) => f x ^ 2 * Real.exp (-‖x‖ ^ 2 / 2))
      (volume : Measure (EuclideanSpace ℝ (Fin N)))) :
    (∫ x : EuclideanSpace ℝ (Fin N),
      ((2 * Real.pi * s2) ^ (-(N : ℝ) / 2) *
        ∫ y, Real.exp (-‖y - ρ • x‖ ^ 2 / (2 * s2)) * f y) ^ 2
      * Real.exp (-‖x‖ ^ 2 / 2))
    ≤ ∫ x : EuclideanSpace ℝ (Fin N), f x ^ 2 * Real.exp (-‖x‖ ^ 2 / 2) := by
  have hbase : 0 < 2 * Real.pi * s2 := by positivity
  have hs2ne : s2 ≠ 0 := ne_of_gt hs2
  have hsq : (Real.sqrt s2) ^ 2 = s2 := Real.sq_sqrt hs2.le
  have hgauss0 : (∫ z : EuclideanSpace ℝ (Fin N), Real.exp (-‖z‖ ^ 2 / (2 * s2)))
      = (2 * Real.pi * s2) ^ ((N : ℝ) / 2) := by
    have h := integral_exp_neg_norm_sq_div (m := N) (Real.sqrt s2) (Real.sqrt_pos.mpr hs2)
    rwa [hsq] at h
  have hgauss : ∀ t : EuclideanSpace ℝ (Fin N),
      (∫ z : EuclideanSpace ℝ (Fin N), Real.exp (-‖z - t‖ ^ 2 / (2 * s2)))
        = (2 * Real.pi * s2) ^ ((N : ℝ) / 2) := by
    intro t
    have h := (integral_sub_right_eq_self
      (fun z : EuclideanSpace ℝ (Fin N) => Real.exp (-‖z‖ ^ 2 / (2 * s2))) t).trans hgauss0
    simpa using h
  have hpow : (2 * Real.pi * s2) ^ (-(N : ℝ) / 2) * (2 * Real.pi * s2) ^ ((N : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add hbase, neg_div, neg_add_cancel, Real.rpow_zero]
  have hshift_int : ∀ t : EuclideanSpace ℝ (Fin N),
      Integrable (fun z : EuclideanSpace ℝ (Fin N) => Real.exp (-‖z - t‖ ^ 2 / (2 * s2)))
        volume := by
    intro t
    have h := integrable_exp_neg_norm_sq_div (m := N) (Real.sqrt s2) (Real.sqrt_pos.mpr hs2)
    rw [hsq] at h
    exact h.comp_sub_right t
  set K : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) → ℝ :=
    fun x y => (2 * Real.pi * s2) ^ (-(N : ℝ) / 2) * Real.exp (-‖y - ρ • x‖ ^ 2 / (2 * s2))
    with hKdef
  have hKnonneg : ∀ x y, 0 ≤ K x y := by
    intro x y; rw [hKdef]; positivity
  have hmassK : ∀ x, (∫ y, K x y) = 1 := by
    intro x
    have h1 : (∫ y, K x y) = (2 * Real.pi * s2) ^ (-(N : ℝ) / 2) *
        ∫ y, Real.exp (-‖y - ρ • x‖ ^ 2 / (2 * s2)) := by
      simp only [hKdef]
      rw [integral_const_mul]
    rw [h1, hgauss (ρ • x), hpow]
  have hKint : ∀ x, Integrable (fun y => K x y) volume := by
    intro x
    have h := hshift_int (ρ • x)
    simp only [hKdef]
    exact h.const_mul _
  have hsqy : ∀ x y : EuclideanSpace ℝ (Fin N),
      ‖y - ρ • x‖ ^ 2 = ‖y‖ ^ 2 - 2 * ρ * inner ℝ x y + ρ ^ 2 * ‖x‖ ^ 2 := by
    intro x y
    have h := norm_sub_sq (𝕜 := ℝ) y (ρ • x)
    rw [h, real_inner_smul_right, real_inner_comm y x, norm_smul]
    simp only [RCLike.re_to_real, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hsqx : ∀ x y : EuclideanSpace ℝ (Fin N),
      ‖x - ρ • y‖ ^ 2 = ‖x‖ ^ 2 - 2 * ρ * inner ℝ x y + ρ ^ 2 * ‖y‖ ^ 2 := by
    intro x y
    have h := norm_sub_sq (𝕜 := ℝ) x (ρ • y)
    rw [h, real_inner_smul_right, norm_smul]
    simp only [RCLike.re_to_real, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hkey : ∀ x y : EuclideanSpace ℝ (Fin N),
      ‖y - ρ • x‖ ^ 2 + s2 * ‖x‖ ^ 2 = ‖x - ρ • y‖ ^ 2 + s2 * ‖y‖ ^ 2 := by
    intro x y
    have hs2' : s2 = 1 - ρ ^ 2 := by linarith
    rw [hsqy x y, hsqx x y, hs2']; ring
  have hdiv : ∀ x y : EuclideanSpace ℝ (Fin N),
      ‖y - ρ • x‖ ^ 2 / (2 * s2) + ‖x‖ ^ 2 / 2
        = ‖x - ρ • y‖ ^ 2 / (2 * s2) + ‖y‖ ^ 2 / 2 := by
    intro x y
    have h := hkey x y
    field_simp
    linarith [h]
  have hpt : ∀ x y : EuclideanSpace ℝ (Fin N),
      Real.exp (-‖y - ρ • x‖ ^ 2 / (2 * s2)) * Real.exp (-‖x‖ ^ 2 / 2)
        = Real.exp (-‖x - ρ • y‖ ^ 2 / (2 * s2)) * Real.exp (-‖y‖ ^ 2 / 2) := by
    intro x y
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    linear_combination (-1 : ℝ) * (hdiv x y)
  have hdens_int : ∀ y, Integrable (fun x => K x y * Real.exp (-‖x‖ ^ 2 / 2)) volume := by
    intro y
    have h2 : Integrable (fun x : EuclideanSpace ℝ (Fin N) =>
        (2 * Real.pi * s2) ^ (-(N : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / 2)
          * Real.exp (-‖x - ρ • y‖ ^ 2 / (2 * s2))) volume :=
      (hshift_int (ρ • y)).const_mul _
    refine h2.congr ?_
    filter_upwards with x
    simp only [hKdef]
    conv_rhs => rw [mul_assoc, hpt x y]
    ring
  have hdens : ∀ y, (∫ x, K x y * Real.exp (-‖x‖ ^ 2 / 2)) = Real.exp (-‖y‖ ^ 2 / 2) := by
    intro y
    have h1 : (∫ x, K x y * Real.exp (-‖x‖ ^ 2 / 2))
        = (2 * Real.pi * s2) ^ (-(N : ℝ) / 2) *
            ∫ x, Real.exp (-‖y - ρ • x‖ ^ 2 / (2 * s2)) * Real.exp (-‖x‖ ^ 2 / 2) := by
      simp only [hKdef]
      rw [show (∫ x, (2 * Real.pi * s2) ^ (-(N : ℝ) / 2)
              * Real.exp (-‖y - ρ • x‖ ^ 2 / (2 * s2)) * Real.exp (-‖x‖ ^ 2 / 2))
          = ∫ x, (2 * Real.pi * s2) ^ (-(N : ℝ) / 2) *
              (Real.exp (-‖y - ρ • x‖ ^ 2 / (2 * s2)) * Real.exp (-‖x‖ ^ 2 / 2)) from by
            apply integral_congr_ae; filter_upwards with x; ring]
      rw [integral_const_mul]
    rw [h1, show (∫ x, Real.exp (-‖y - ρ • x‖ ^ 2 / (2 * s2)) * Real.exp (-‖x‖ ^ 2 / 2))
        = ∫ x, Real.exp (-‖x - ρ • y‖ ^ 2 / (2 * s2)) * Real.exp (-‖y‖ ^ 2 / 2) from by
          apply integral_congr_ae; filter_upwards with x; exact hpt x y]
    rw [integral_mul_const, hgauss (ρ • y)]
    rw [← mul_assoc, hpow, one_mul]
  -- Cauchy–Schwarz / Tonelli on the product
  have hG_meas : AEMeasurable (Function.uncurry (fun x y : EuclideanSpace ℝ (Fin N) =>
      ENNReal.ofReal (K x y * f y ^ 2 * Real.exp (-‖x‖ ^ 2 / 2)))) (volume.prod volume) := by
    have hbase' : AEStronglyMeasurable (fun p : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin N) =>
        K p.1 p.2 * f p.2 ^ 2 * Real.exp (-‖p.1‖ ^ 2 / 2)) (volume.prod volume) := by
      have hKc : Continuous (fun p : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin N) =>
          K p.1 p.2) := by simp only [hKdef]; fun_prop
      exact ((hKc.aestronglyMeasurable).mul
        (((hfmeas.comp measurable_snd).aestronglyMeasurable).pow 2)).mul
        ((Real.continuous_exp.comp (by fun_prop)).aestronglyMeasurable)
    exact hbase'.aemeasurable.ennreal_ofReal
  have hinner : ∀ y : EuclideanSpace ℝ (Fin N),
      (∫⁻ x, ENNReal.ofReal (K x y * f y ^ 2 * Real.exp (-‖x‖ ^ 2 / 2)))
        = ENNReal.ofReal (f y ^ 2 * Real.exp (-‖y‖ ^ 2 / 2)) := by
    intro y
    have h1 : (∫⁻ x, ENNReal.ofReal (K x y * Real.exp (-‖x‖ ^ 2 / 2)))
        = ENNReal.ofReal (Real.exp (-‖y‖ ^ 2 / 2)) := by
      rw [← ofReal_integral_eq_lintegral_ofReal (hdens_int y)
        (ae_of_all _ (fun x => mul_nonneg (hKnonneg x y) (Real.exp_pos _).le)), hdens y]
    have h3 : ∀ x, ENNReal.ofReal (K x y * f y ^ 2 * Real.exp (-‖x‖ ^ 2 / 2))
        = ENNReal.ofReal (K x y * Real.exp (-‖x‖ ^ 2 / 2)) * ENNReal.ofReal (f y ^ 2) := by
      intro x
      rw [show K x y * f y ^ 2 * Real.exp (-‖x‖ ^ 2 / 2)
            = (K x y * Real.exp (-‖x‖ ^ 2 / 2)) * f y ^ 2 from by ring]
      rw [ENNReal.ofReal_mul (mul_nonneg (hKnonneg x y) (Real.exp_pos _).le)]
    calc (∫⁻ x, ENNReal.ofReal (K x y * f y ^ 2 * Real.exp (-‖x‖ ^ 2 / 2)))
        = ∫⁻ x, ENNReal.ofReal (K x y * Real.exp (-‖x‖ ^ 2 / 2)) * ENNReal.ofReal (f y ^ 2) :=
          lintegral_congr h3
      _ = (∫⁻ x, ENNReal.ofReal (K x y * Real.exp (-‖x‖ ^ 2 / 2))) * ENNReal.ofReal (f y ^ 2) :=
          lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (Real.exp (-‖y‖ ^ 2 / 2)) * ENNReal.ofReal (f y ^ 2) := by rw [h1]
      _ = ENNReal.ofReal (Real.exp (-‖y‖ ^ 2 / 2) * f y ^ 2) :=
          (ENNReal.ofReal_mul (Real.exp_pos _).le).symm
      _ = ENNReal.ofReal (f y ^ 2 * Real.exp (-‖y‖ ^ 2 / 2)) := by rw [mul_comm]
  have hiter : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (K x y * f y ^ 2 * Real.exp (-‖x‖ ^ 2 / 2)))
      = ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin N), f y ^ 2 * Real.exp (-‖y‖ ^ 2 / 2)) := by
    rw [lintegral_lintegral_swap hG_meas, lintegral_congr hinner]
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all _ (fun y => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le))]
  have hGlin : (∫⁻ p : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin N),
        ENNReal.ofReal (K p.1 p.2 * f p.2 ^ 2 * Real.exp (-‖p.1‖ ^ 2 / 2)) ∂(volume.prod volume))
      = ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin N), f y ^ 2 * Real.exp (-‖y‖ ^ 2 / 2)) := by
    rw [← lintegral_lintegral (μ := volume) (ν := volume) hG_meas]
    exact hiter
  have hG_int : Integrable (fun p : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin N) =>
      K p.1 p.2 * f p.2 ^ 2 * Real.exp (-‖p.1‖ ^ 2 / 2)) (volume.prod volume) := by
    refine ⟨?_, ?_⟩
    · have hKc : Continuous (fun p : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin N) =>
          K p.1 p.2) := by simp only [hKdef]; fun_prop
      exact ((hKc.aestronglyMeasurable).mul
        (((hfmeas.comp measurable_snd).aestronglyMeasurable).pow 2)).mul
        ((Real.continuous_exp.comp (by fun_prop)).aestronglyMeasurable)
    · rw [hasFiniteIntegral_iff_norm]
      have h1 : ∀ p : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin N),
          ENNReal.ofReal ‖K p.1 p.2 * f p.2 ^ 2 * Real.exp (-‖p.1‖ ^ 2 / 2)‖
            = ENNReal.ofReal (K p.1 p.2 * f p.2 ^ 2 * Real.exp (-‖p.1‖ ^ 2 / 2)) := by
        intro p
        rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (hKnonneg p.1 p.2) (sq_nonneg _))
          (Real.exp_pos _).le)]
      simp only [h1]
      rw [hGlin]
      exact ENNReal.ofReal_lt_top
  have hslice : ∀ᵐ x ∂volume, Integrable (fun y => K x y * f y ^ 2) volume := by
    filter_upwards [hG_int.prod_right_ae] with x hx
    have hne : Real.exp (-‖x‖ ^ 2 / 2) ≠ 0 := Real.exp_ne_zero _
    refine (hx.mul_const ((Real.exp (-‖x‖ ^ 2 / 2))⁻¹)).congr ?_
    filter_upwards with y
    field_simp
  have hcs : ∀ᵐ x ∂volume, (∫ y, K x y * f y) ^ 2 ≤ ∫ y, K x y * f y ^ 2 := by
    filter_upwards [hslice] with x hx2
    have hcs := sq_int_mul_le_sq_mul (fun _ : EuclideanSpace ℝ (Fin N) => (1 : ℝ)) f
      (fun y => K x y) (fun y => hKnonneg x y) (by simpa using hKint x)
      (by refine hx2.congr ?_; filter_upwards with y; rw [mul_comm])
    have h1 : (∫ y, (1 : ℝ) * f y * K x y) = ∫ y, K x y * f y := by
      apply integral_congr_ae; filter_upwards with y; ring
    have h2 : (∫ y, (1 : ℝ) ^ 2 * K x y) = 1 := by
      simp only [one_pow, one_mul, hmassK x]
    have h3 : (∫ y, f y ^ 2 * K x y) = ∫ y, K x y * f y ^ 2 := by
      apply integral_congr_ae; filter_upwards with y; ring
    calc (∫ y, K x y * f y) ^ 2 = (∫ y, (1 : ℝ) * f y * K x y) ^ 2 := by rw [h1]
      _ ≤ (∫ y, (1 : ℝ) ^ 2 * K x y) * (∫ y, f y ^ 2 * K x y) := hcs
      _ = 1 * (∫ y, f y ^ 2 * K x y) := by rw [h2]
      _ = ∫ y, K x y * f y ^ 2 := by rw [one_mul, h3]
  have hT_aesm : AEStronglyMeasurable (fun x => ∫ y, K x y * f y) volume := by
    have huncurry : AEStronglyMeasurable
        (fun p : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin N) => K p.1 p.2 * f p.2)
        (volume.prod volume) := by
      have hKc : Continuous (fun p : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin N) =>
          K p.1 p.2) := by simp only [hKdef]; fun_prop
      exact hKc.aestronglyMeasurable.mul ((hfmeas.comp measurable_snd).aestronglyMeasurable)
    simpa only using huncurry.integral_prod_right'
  have hL_aesm : AEStronglyMeasurable
      (fun x => (∫ y, K x y * f y) ^ 2 * Real.exp (-‖x‖ ^ 2 / 2)) volume :=
    (hT_aesm.pow 2).mul (Real.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
  have hle_lin : (∫⁻ x, ENNReal.ofReal ((∫ y, K x y * f y) ^ 2 * Real.exp (-‖x‖ ^ 2 / 2)))
      ≤ ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin N), f y ^ 2 * Real.exp (-‖y‖ ^ 2 / 2)) := by
    calc (∫⁻ x, ENNReal.ofReal ((∫ y, K x y * f y) ^ 2 * Real.exp (-‖x‖ ^ 2 / 2)))
        ≤ ∫⁻ x, ENNReal.ofReal ((∫ y, K x y * f y ^ 2) * Real.exp (-‖x‖ ^ 2 / 2)) := by
          apply lintegral_mono_ae
          filter_upwards [hcs] with x hx
          exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hx (Real.exp_pos _).le)
      _ = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (K x y * f y ^ 2 * Real.exp (-‖x‖ ^ 2 / 2)) := by
          apply lintegral_congr_ae
          filter_upwards [hslice] with x hx2
          rw [ENNReal.ofReal_mul (integral_nonneg (fun y => mul_nonneg (hKnonneg x y) (sq_nonneg _))),
            ofReal_integral_eq_lintegral_ofReal hx2
              (ae_of_all _ (fun y => mul_nonneg (hKnonneg x y) (sq_nonneg _))),
            ← lintegral_mul_const' (ENNReal.ofReal (Real.exp (-‖x‖ ^ 2 / 2)))
              (fun y => ENNReal.ofReal (K x y * f y ^ 2)) ENNReal.ofReal_ne_top]
          apply lintegral_congr
          intro y
          rw [ENNReal.ofReal_mul (mul_nonneg (hKnonneg x y) (sq_nonneg _))]
      _ = ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin N), f y ^ 2 * Real.exp (-‖y‖ ^ 2 / 2)) :=
          hiter
  have hL_int : Integrable (fun x => (∫ y, K x y * f y) ^ 2 * Real.exp (-‖x‖ ^ 2 / 2)) volume := by
    refine ⟨hL_aesm, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    have h1 : ∀ x, ENNReal.ofReal ‖(∫ y, K x y * f y) ^ 2 * Real.exp (-‖x‖ ^ 2 / 2)‖
        = ENNReal.ofReal ((∫ y, K x y * f y) ^ 2 * Real.exp (-‖x‖ ^ 2 / 2)) := by
      intro x
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
    simp only [h1]
    exact lt_of_le_of_lt hle_lin ENNReal.ofReal_lt_top
  have hnn : 0 ≤ᵐ[volume] fun x =>
      (∫ y, K x y * f y) ^ 2 * Real.exp (-‖x‖ ^ 2 / 2) :=
    ae_of_all _ (fun x => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
  have hmain' : (∫ x, (∫ y, K x y * f y) ^ 2 * Real.exp (-‖x‖ ^ 2 / 2))
      ≤ ∫ x : EuclideanSpace ℝ (Fin N), f x ^ 2 * Real.exp (-‖x‖ ^ 2 / 2) := by
    have hle := hle_lin
    rw [← ofReal_integral_eq_lintegral_ofReal hL_int hnn] at hle
    have h1 : (ENNReal.ofReal (∫ x, (∫ y, K x y * f y) ^ 2 * Real.exp (-‖x‖ ^ 2 / 2)))
        ≠ ∞ := ENNReal.ofReal_ne_top
    have h2 : (ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin N),
        f y ^ 2 * Real.exp (-‖y‖ ^ 2 / 2))) ≠ ∞ := ENNReal.ofReal_ne_top
    have h3 := (ENNReal.toReal_le_toReal h1 h2).mpr hle
    rw [ENNReal.toReal_ofReal (integral_nonneg_of_ae hnn),
      ENNReal.toReal_ofReal (integral_nonneg_of_ae
        (ae_of_all _ (fun y => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)))] at h3
    exact h3
  have hKform : ∀ x : EuclideanSpace ℝ (Fin N), (∫ y, K x y * f y)
      = (2 * Real.pi * s2) ^ (-(N : ℝ) / 2)
        * ∫ y, Real.exp (-‖y - ρ • x‖ ^ 2 / (2 * s2)) * f y := by
    intro x
    simp only [hKdef]
    rw [show (∫ y, (2 * Real.pi * s2) ^ (-(N : ℝ) / 2)
            * Real.exp (-‖y - ρ • x‖ ^ 2 / (2 * s2)) * f y)
        = ∫ y, (2 * Real.pi * s2) ^ (-(N : ℝ) / 2)
            * (Real.exp (-‖y - ρ • x‖ ^ 2 / (2 * s2)) * f y) from by
          apply integral_congr_ae; filter_upwards with y; ring]
    rw [integral_const_mul]
  have hconv : (∫ x, (∫ y, K x y * f y) ^ 2 * Real.exp (-‖x‖ ^ 2 / 2))
      = (∫ x : EuclideanSpace ℝ (Fin N),
          ((2 * Real.pi * s2) ^ (-(N : ℝ) / 2)
            * ∫ y, Real.exp (-‖y - ρ • x‖ ^ 2 / (2 * s2)) * f y) ^ 2
          * Real.exp (-‖x‖ ^ 2 / 2)) := by
    apply integral_congr_ae
    filter_upwards with x
    rw [hKform x]
  rw [← hconv]
  exact hmain'

theorem mehler_operator_contraction_l2 {N : ℕ} (ρ : ℝ) (hρ : |ρ| < 1)
    (f : EuclideanSpace ℝ (Fin N) → ℝ)
    (hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume.withDensity
      (fun x : EuclideanSpace ℝ (Fin N) => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2 / 2))))) :
    (∫ x : EuclideanSpace ℝ (Fin N), ((2 * Real.pi * (1 - ρ ^ 2)) ^ (-(N : ℝ) / 2)
        * ∫ y : EuclideanSpace ℝ (Fin N),
            Real.exp (-‖y - ρ • x‖ ^ 2 / (2 * (1 - ρ ^ 2))) * f y) ^ 2
      * Real.exp (-‖x‖ ^ 2 / 2))
      ≤ ∫ x : EuclideanSpace ℝ (Fin N), (f x) ^ 2 * Real.exp (-‖x‖ ^ 2 / 2) := by

  have hs2pos : (0 : ℝ) < 1 - ρ ^ 2 := by
    have h2 : ρ ^ 2 < 1 := by nlinarith [abs_nonneg ρ, sq_abs ρ, hρ]
    linarith
  set dens : EuclideanSpace ℝ (Fin N) → ℝ≥0∞ :=
    fun x => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2 / 2)) with hdensdef
  have hdens_meas : Measurable dens := by
    rw [hdensdef]
    exact ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp (by fun_prop))
  have hdens_ne : ∀ x, dens x ≠ 0 := by
    intro x
    rw [hdensdef, ENNReal.ofReal_ne_zero_iff]
    exact Real.exp_pos _
  have hfsq : Integrable (fun x : EuclideanSpace ℝ (Fin N) =>
      f x ^ 2 * Real.exp (-‖x‖ ^ 2 / 2)) volume := by
    have h1 : Integrable (fun x => f x ^ 2) (volume.withDensity dens) := by
      have hf' : MemLp f 2 (volume.withDensity dens) := by rw [hdensdef]; exact hf
      exact (memLp_two_iff_integrable_sq hf'.1).mp hf'
    rw [integrable_withDensity_iff hdens_meas (ae_of_all _ (fun x => ENNReal.ofReal_lt_top))] at h1
    refine h1.congr ?_
    filter_upwards with x
    simp only [hdensdef, ENNReal.toReal_ofReal (Real.exp_pos _).le]
  obtain ⟨g, hg_sm, hg_eq⟩ := hf.1
  have hg_meas : Measurable g := hg_sm.measurable
  have hg_eq_vol : f =ᵐ[volume] g := by
    have h := (ae_withDensity_iff (μ := volume) hdens_meas).mp hg_eq
    filter_upwards [h] with x hx
    exact hx (hdens_ne x)
  have hgint : Integrable (fun x : EuclideanSpace ℝ (Fin N) =>
      g x ^ 2 * Real.exp (-‖x‖ ^ 2 / 2)) volume := by
    refine hfsq.congr ?_
    filter_upwards [hg_eq_vol] with x hx
    rw [hx]
  have haux := mehler_aux ρ (1 - ρ ^ 2) hs2pos (by ring) g hg_meas hgint
  have htransfer : (∫ x : EuclideanSpace ℝ (Fin N),
        ((2 * Real.pi * (1 - ρ ^ 2)) ^ (-(N : ℝ) / 2)
          * ∫ y, Real.exp (-‖y - ρ • x‖ ^ 2 / (2 * (1 - ρ ^ 2))) * f y) ^ 2
        * Real.exp (-‖x‖ ^ 2 / 2))
      = (∫ x : EuclideanSpace ℝ (Fin N),
        ((2 * Real.pi * (1 - ρ ^ 2)) ^ (-(N : ℝ) / 2)
          * ∫ y, Real.exp (-‖y - ρ • x‖ ^ 2 / (2 * (1 - ρ ^ 2))) * g y) ^ 2
        * Real.exp (-‖x‖ ^ 2 / 2)) := by
    apply integral_congr_ae
    filter_upwards with x
    have hthis : (fun y : EuclideanSpace ℝ (Fin N) =>
          Real.exp (-‖y - ρ • x‖ ^ 2 / (2 * (1 - ρ ^ 2))) * f y)
        =ᵐ[volume] fun y => Real.exp (-‖y - ρ • x‖ ^ 2 / (2 * (1 - ρ ^ 2))) * g y :=
      (Filter.EventuallyEq.refl (ae volume) (fun y : EuclideanSpace ℝ (Fin N) =>
        Real.exp (-‖y - ρ • x‖ ^ 2 / (2 * (1 - ρ ^ 2))))).mul hg_eq_vol
    rw [integral_congr_ae hthis]
  have hrhs : (∫ x : EuclideanSpace ℝ (Fin N), (g x) ^ 2 * Real.exp (-‖x‖ ^ 2 / 2))
      = (∫ x : EuclideanSpace ℝ (Fin N), (f x) ^ 2 * Real.exp (-‖x‖ ^ 2 / 2)) := by
    apply integral_congr_ae
    filter_upwards [hg_eq_vol] with x hx
    rw [hx]
  rw [htransfer, ← hrhs]
  exact haux


end Commons.Analysis.GaussianMeasure
