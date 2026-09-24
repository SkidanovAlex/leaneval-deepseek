import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Commons.Analysis.Fourier.triangle_kernel_fourier_inversion
import Submission.Commons.Analysis.Fourier.triangle_kernel_fourier_transform

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Real
open scoped FourierTransform

namespace Commons.Analysis.Fourier

/-- The norm of a nonnegative real, viewed as a complex number. -/
lemma norm_ofReal_of_nonneg {a : ℝ} (ha : 0 ≤ a) : ‖((a : ℝ) : ℂ)‖ = a := by
  rw [show ‖((a : ℝ) : ℂ)‖ = |a| from RCLike.norm_ofReal a, abs_of_nonneg ha]

/-! ## The triangle (Fejér) kernel and its Fourier transform -/

/-- `sinc (π x)^2 ≥ 1/2` for `|x| ≤ 1/4`. -/
theorem sinc_pi_sq_lower_bound {x : ℝ} (hx : |x| ≤ 1 / 4) :
    1 / 2 ≤ Real.sinc (Real.pi * x) ^ 2 := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [mul_zero, Real.sinc_zero]; norm_num
  · have hxpos : 0 < |x| := abs_pos.mpr hx0
    have ht0 : 0 ≤ Real.pi * |x| := by positivity
    have ht1 : Real.pi * |x| ≤ 1 := by
      calc Real.pi * |x| ≤ 4 * (1 / 4) :=
            mul_le_mul Real.pi_lt_four.le hx (abs_nonneg x) (by norm_num)
        _ = 1 := by norm_num
    have ht2 : (Real.pi * |x|) ^ 2 ≤ 1 := by nlinarith [ht0, ht1]
    have hsin : (5 / 6) * (Real.pi * |x|) ≤ Real.sin (Real.pi * |x|) := by
      have h := Real.sin_ge_sub_cube ht0
      have h3 : (Real.pi * |x|) ^ 3 / 6 ≤ (Real.pi * |x|) / 6 := by nlinarith
      linarith
    have hle4 : |x| ≤ 1 / 4 := hx
    have hsin_nonneg : ∀ {u : ℝ}, 0 ≤ u → u ≤ 1 / 4 → 0 ≤ Real.sin (Real.pi * u) := by
      intro u hu0 hu1
      exact Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by
        calc Real.pi * u ≤ Real.pi * (1 / 4) := mul_le_mul_of_nonneg_left hu1 Real.pi_pos.le
          _ ≤ Real.pi := by nlinarith [Real.pi_pos])
    have habs_sin : |Real.sin (Real.pi * x)| = Real.sin (Real.pi * |x|) := by
      rcases lt_or_ge x 0 with hneg | hnonneg
      · have h1 : |x| = -x := abs_of_neg hneg
        rw [h1, show Real.pi * x = -(Real.pi * -x) by ring, Real.sin_neg, abs_neg,
          abs_of_nonneg (hsin_nonneg (by linarith) (by linarith [hle4, abs_of_neg hneg]))]
      · rw [abs_of_nonneg hnonneg,
          abs_of_nonneg (hsin_nonneg hnonneg (by linarith [abs_of_nonneg hnonneg ▸ hle4]))]
    have hbound : (5 / 6 : ℝ) ≤ |Real.sinc (Real.pi * x)| := by
      rw [Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hx0), abs_div, habs_sin,
        abs_mul, abs_of_pos Real.pi_pos, le_div_iff₀ (by positivity)]
      linarith [hsin]
    have hone : (1 : ℝ) / 2 ≤ (5 / 6 : ℝ) ^ 2 := by norm_num
    have hsq : (5 / 6 : ℝ) ^ 2 ≤ (Real.sinc (Real.pi * x)) ^ 2 := by
      rw [← sq_abs (Real.sinc (Real.pi * x))]
      exact pow_le_pow_left₀ (by norm_num) hbound 2
    linarith

/-- The cosine integral of `sinc (π ·)^2`. -/
theorem integral_sinc_pi_sq_mul_cos (ξ : ℝ) :
    ∫ y : ℝ, Real.sinc (Real.pi * y) ^ 2 * Real.cos (2 * Real.pi * ξ * y) = tri ξ := by
  have hpt : ∀ y, Real.sinc (Real.pi * y) ^ 2
      = (if y = 0 then 1 else (Real.sin (Real.pi * y) / (Real.pi * y)) ^ 2) := by
    intro y
    rcases eq_or_ne y 0 with rfl | hy
    · simp [Real.sinc_zero]
    · rw [if_neg hy, Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hy)]
  change ∫ y : ℝ, Real.sinc (Real.pi * y) ^ 2 * Real.cos (2 * Real.pi * ξ * y)
      = max (1 - |ξ|) 0
  rw [← triangle_kernel_fourier_inversion ξ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show Real.sinc (Real.pi * y) ^ 2 * Real.cos (2 * Real.pi * ξ * y)
      = (if y = 0 then 1 else (Real.sin (Real.pi * y) / (Real.pi * y)) ^ 2)
          * Real.cos (2 * Real.pi * ξ * y)
  rw [hpt y]

/-- For an even integrable real function, the complex exponential integral equals the
cosine integral. -/
theorem integral_mul_exp_eq {g : ℝ → ℝ} (hg : Integrable g) (heven : Function.Even g) (s : ℝ) :
    ∫ y : ℝ, (g y : ℂ) * Complex.exp (↑(-(2 * Real.pi * y * s)) * Complex.I)
      = Complex.ofReal (∫ y : ℝ, g y * Real.cos (2 * Real.pi * s * y)) := by
  have h1 := Real.fourier_real_eq_integral_exp_smul (fun t : ℝ => (g t : ℂ)) s
  have h2 := fourier_ofReal_of_even hg heven s
  rw [h2] at h1
  rw [h1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [smul_eq_mul]
  ring_nf

/-- Fourier transform pair: `∫ tri(y) e^{-2π i y s} dy = sinc (π s)^2`. -/
theorem integral_tri_mul_exp (s : ℝ) :
    ∫ y : ℝ, (tri y : ℂ) * Complex.exp (↑(-(2 * Real.pi * y * s)) * Complex.I)
      = ((Real.sinc (Real.pi * s) ^ 2 : ℝ) : ℂ) := by
  rw [integral_mul_exp_eq tri_integrable tri_even s, integral_tri_cos s]

/-- Fourier transform pair: `∫ sinc (π y)^2 e^{-2π i y s} dy = tri s`. -/
theorem integral_sinc_pi_sq_mul_exp (s : ℝ) :
    ∫ y : ℝ, ((Real.sinc (Real.pi * y) ^ 2 : ℝ) : ℂ)
        * Complex.exp (↑(-(2 * Real.pi * y * s)) * Complex.I)
      = (tri s : ℂ) := by
  rw [integral_mul_exp_eq integrable_sinc_pi_sq even_sinc_pi_sq s,
      integral_sinc_pi_sq_mul_cos s]

/-! ## The expansion identity -/

lemma star_exp_ofReal_mul_I (r : ℝ) :
    (starRingEnd ℂ) (Complex.exp (↑r * Complex.I)) = Complex.exp (↑(-r) * Complex.I) := by
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- Pointwise algebra: the squared modulus of a sum of modulated phases, times a scalar. -/
lemma mul_normSq_sum_exp {R : ℕ} (gv : ℂ) (T : ℝ) (t : Fin R → ℝ) (x : Fin R → ℂ) (y : ℝ) :
    gv * ((‖∑ i : Fin R,
        x i * Complex.exp (↑(-(2 * Real.pi * y * (t i) / T)) * Complex.I)‖ ^ 2 : ℝ) : ℂ)
      = ∑ i : Fin R, ∑ j : Fin R, (x i * (starRingEnd ℂ) (x j)) *
          (gv * Complex.exp (↑(-(2 * Real.pi * y * ((t i - t j) / T))) * Complex.I)) := by
  have hconj : (starRingEnd ℂ) (∑ i : Fin R,
        x i * Complex.exp (↑(-(2 * Real.pi * y * (t i) / T)) * Complex.I))
      = ∑ j : Fin R, (starRingEnd ℂ) (x j)
          * Complex.exp (↑(2 * Real.pi * y * (t j) / T) * Complex.I) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, star_exp_ofReal_mul_I]
    congr 2
    push_cast
    ring
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, hconj, Finset.sum_mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hexp : Complex.exp (↑(-(2 * Real.pi * y * (t i) / T)) * Complex.I)
        * Complex.exp (↑(2 * Real.pi * y * (t j) / T) * Complex.I)
      = Complex.exp (↑(-(2 * Real.pi * y * ((t i - t j) / T))) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc gv * ((x i * Complex.exp (↑(-(2 * Real.pi * y * (t i) / T)) * Complex.I))
        * ((starRingEnd ℂ) (x j) * Complex.exp (↑(2 * Real.pi * y * (t j) / T) * Complex.I)))
      = (x i * (starRingEnd ℂ) (x j)) * (gv *
          (Complex.exp (↑(-(2 * Real.pi * y * (t i) / T)) * Complex.I)
            * Complex.exp (↑(2 * Real.pi * y * (t j) / T) * Complex.I))) := by ring
    _ = (x i * (starRingEnd ℂ) (x j)) *
          (gv * Complex.exp (↑(-(2 * Real.pi * y * ((t i - t j) / T))) * Complex.I)) := by
        rw [hexp]

/-- Expansion identity for Fejér-type kernels: a double sum of the Fourier transform of `g`
over differences of the sampling points equals the integral of `g` against the squared
modulus of an exponential sum. -/
theorem fejer_expansion_identity {g : ℝ → ℝ} (hg : Integrable g) {Ĝ : ℝ → ℂ}
    (hĜ : ∀ s : ℝ,
      (∫ y : ℝ, (g y : ℂ) * Complex.exp (↑(-(2 * Real.pi * y * s)) * Complex.I)) = Ĝ s)
    (T : ℝ) {R : ℕ} (t : Fin R → ℝ) (x : Fin R → ℂ) :
    (∑ i : Fin R, ∑ j : Fin R, Ĝ ((t i - t j) / T) * (x i * (starRingEnd ℂ) (x j)))
      = ∫ y : ℝ, (g y : ℂ) *
          ((‖∑ i : Fin R,
            x i * Complex.exp (↑(-(2 * Real.pi * y * (t i) / T)) * Complex.I)‖ ^ 2 : ℝ) : ℂ) := by
  classical
  let F : Fin R → Fin R → ℝ → ℂ := fun i j y => (x i * (starRingEnd ℂ) (x j)) *
      ((g y : ℂ) * Complex.exp (↑(-(2 * Real.pi * y * ((t i - t j) / T))) * Complex.I))
  have hpoint : ∀ y : ℝ, (g y : ℂ) *
        ((‖∑ i : Fin R,
          x i * Complex.exp (↑(-(2 * Real.pi * y * (t i) / T)) * Complex.I)‖ ^ 2 : ℝ) : ℂ)
      = ∑ i : Fin R, ∑ j : Fin R, F i j y :=
    fun y => mul_normSq_sum_exp (g y : ℂ) T t x y
  rw [show (∫ y : ℝ, (g y : ℂ) *
        ((‖∑ i : Fin R,
          x i * Complex.exp (↑(-(2 * Real.pi * y * (t i) / T)) * Complex.I)‖ ^ 2 : ℝ) : ℂ))
      = ∫ y : ℝ, ∑ i : Fin R, ∑ j : Fin R, F i j y
      from integral_congr_ae (Filter.Eventually.of_forall hpoint)]
  have hIntF : ∀ i j : Fin R, Integrable (F i j) := by
    intro i j
    refine Integrable.const_mul ?_ _
    exact (Integrable.ofReal (𝕜 := ℂ) hg).mul_bdd (by fun_prop) (by
      filter_upwards with y
      rw [Complex.norm_exp_ofReal_mul_I])
  have hprod : (∫ y : ℝ, ∑ i : Fin R, ∑ j : Fin R, F i j y)
      = ∫ y : ℝ, ∑ p : Fin R × Fin R, F p.1 p.2 y := by
    apply integral_congr_ae
    filter_upwards with y
    rw [← Finset.univ_product_univ]
    exact (Finset.sum_product Finset.univ Finset.univ (fun p : Fin R × Fin R => F p.1 p.2 y)).symm
  rw [hprod, integral_finsetSum Finset.univ (fun p _ => hIntF p.1 p.2)]
  have hprod2 : (∑ p : Fin R × Fin R, ∫ y : ℝ, F p.1 p.2 y)
      = ∑ i : Fin R, ∑ j : Fin R, ∫ y : ℝ, F i j y := by
    rw [← Finset.univ_product_univ]
    exact Finset.sum_product Finset.univ Finset.univ
      (fun p : Fin R × Fin R => ∫ y : ℝ, F p.1 p.2 y)
  rw [hprod2]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  show Ĝ ((t i - t j) / T) * (x i * (starRingEnd ℂ) (x j))
      = ∫ y : ℝ, (x i * (starRingEnd ℂ) (x j)) *
          ((g y : ℂ) * Complex.exp (↑(-(2 * Real.pi * y * ((t i - t j) / T))) * Complex.I))
  rw [integral_const_mul, hĜ]
  ring


/-! ## Real form of the expansion identity -/

/-- Real form: the integral of `g` against a squared modulus equals the double sum of the
(real) transform of `g` against the real parts of `x i * conj (x j)`. -/
theorem fejer_expansion_identity_re {g : ℝ → ℝ} (hg : Integrable g) {ĝ : ℝ → ℝ}
    (hĜ : ∀ s : ℝ,
      (∫ y : ℝ, (g y : ℂ) * Complex.exp (↑(-(2 * Real.pi * y * s)) * Complex.I)) = (ĝ s : ℂ))
    (T : ℝ) {R : ℕ} (t : Fin R → ℝ) (x : Fin R → ℂ) :
    (∑ i : Fin R, ∑ j : Fin R, ĝ ((t i - t j) / T) * (x i * (starRingEnd ℂ) (x j)).re)
      = ∫ y : ℝ, g y * ‖∑ i : Fin R,
          x i * Complex.exp (↑(-(2 * Real.pi * y * (t i) / T)) * Complex.I)‖ ^ 2 := by
  have h := fejer_expansion_identity hg (Ĝ := fun s => (ĝ s : ℂ)) (fun s => hĜ s) T t x
  have hre := congrArg Complex.re h
  have hleft : (∑ i : Fin R, ∑ j : Fin R,
        (ĝ ((t i - t j) / T) : ℂ) * (x i * (starRingEnd ℂ) (x j))).re
      = ∑ i : Fin R, ∑ j : Fin R, ĝ ((t i - t j) / T) * (x i * (starRingEnd ℂ) (x j)).re := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hbnd : ∀ y : ℝ, ‖((‖∑ i : Fin R,
        x i * Complex.exp (↑(-(2 * Real.pi * y * (t i) / T)) * Complex.I)‖ ^ 2 : ℝ) : ℂ)‖
      ≤ (∑ i : Fin R, ‖x i‖) ^ 2 := by
    intro y
    have h1 : ‖∑ i : Fin R,
        x i * Complex.exp (↑(-(2 * Real.pi * y * (t i) / T)) * Complex.I)‖ ≤ ∑ i : Fin R, ‖x i‖ := by
      calc ‖∑ i : Fin R, x i * Complex.exp (↑(-(2 * Real.pi * y * (t i) / T)) * Complex.I)‖
          ≤ ∑ i : Fin R, ‖x i * Complex.exp (↑(-(2 * Real.pi * y * (t i) / T)) * Complex.I)‖ :=
            norm_sum_le _ _
        _ = ∑ i : Fin R, ‖x i‖ := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    have h2 : ‖∑ i : Fin R,
        x i * Complex.exp (↑(-(2 * Real.pi * y * (t i) / T)) * Complex.I)‖ ^ 2
        ≤ (∑ i : Fin R, ‖x i‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    calc ‖((‖∑ i : Fin R,
          x i * Complex.exp (↑(-(2 * Real.pi * y * (t i) / T)) * Complex.I)‖ ^ 2 : ℝ) : ℂ)‖
        = ‖∑ i : Fin R,
          x i * Complex.exp (↑(-(2 * Real.pi * y * (t i) / T)) * Complex.I)‖ ^ 2 :=
            norm_ofReal_of_nonneg (sq_nonneg _)
      _ ≤ (∑ i : Fin R, ‖x i‖) ^ 2 := h2
  have hint : Integrable (fun y : ℝ => (g y : ℂ) *
      ((‖∑ i : Fin R,
        x i * Complex.exp (↑(-(2 * Real.pi * y * (t i) / T)) * Complex.I)‖ ^ 2 : ℝ) : ℂ)) :=
    (Integrable.ofReal (𝕜 := ℂ) hg).mul_bdd (by fun_prop)
      (Filter.Eventually.of_forall hbnd)
  have hright : (∫ y : ℝ, (g y : ℂ) *
        ((‖∑ i : Fin R,
          x i * Complex.exp (↑(-(2 * Real.pi * y * (t i) / T)) * Complex.I)‖ ^ 2 : ℝ) : ℂ)).re
      = ∫ y : ℝ, g y * ‖∑ i : Fin R,
          x i * Complex.exp (↑(-(2 * Real.pi * y * (t i) / T)) * Complex.I)‖ ^ 2 := by
    have hf' : (∫ y : ℝ, (g y : ℂ) *
        ((‖∑ i : Fin R,
          x i * Complex.exp (↑(-(2 * Real.pi * y * (t i) / T)) * Complex.I)‖ ^ 2 : ℝ) : ℂ)).re
        = ∫ y : ℝ, ((g y : ℂ) *
        ((‖∑ i : Fin R,
          x i * Complex.exp (↑(-(2 * Real.pi * y * (t i) / T)) * Complex.I)‖ ^ 2 : ℝ) : ℂ)).re :=
      (integral_re hint).symm
    rw [hf']
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show ((g y : ℂ) * ((‖∑ i : Fin R,
        x i * Complex.exp (↑(-(2 * Real.pi * y * (t i) / T)) * Complex.I)‖ ^ 2 : ℝ) : ℂ)).re
      = g y * ‖∑ i : Fin R,
        x i * Complex.exp (↑(-(2 * Real.pi * y * (t i) / T)) * Complex.I)‖ ^ 2
    rw [Complex.re_ofReal_mul, Complex.ofReal_re]
  rw [← hleft, ← hright]
  exact hre

/-- A finite sum of integrable functions is integrable. -/
lemma integrable_finset_sum {ι : Type*} {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (S : Finset ι) {f : ι → ℝ → G} (h : ∀ i ∈ S, Integrable (f i)) :
    Integrable (fun y : ℝ => ∑ i ∈ S, f i y) := by
  classical
  induction S using Finset.induction with
  | empty => simpa using integrable_zero ℝ G volume
  | insert a s has ih =>
      have h1 : (fun y : ℝ => ∑ i ∈ insert a s, f i y) = fun y => f a y + ∑ i ∈ s, f i y := by
        funext y
        rw [Finset.sum_insert has]
      rw [h1]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- Pulling sums of constants times integrals out of an integral. -/
lemma sum_mul_integral_eq_integral_sum {ι κ : Type*}
    (w : ι → κ → ℂ) (f : ι → κ → ℝ → ℂ) (S : Finset ι) (S' : Finset κ) {g : ℝ → ℂ}
    (hg : Integrable g) (hf : ∀ n ∈ S, ∀ m ∈ S', Integrable (fun y : ℝ => g y * f n m y)) :
    (∑ n ∈ S, ∑ m ∈ S', w n m * ∫ y : ℝ, g y * f n m y)
      = ∫ y : ℝ, g y * ∑ n ∈ S, ∑ m ∈ S', w n m * f n m y := by
  classical
  have hG : ∀ n ∈ S, ∀ m ∈ S', Integrable (fun y : ℝ => g y * (w n m * f n m y)) := by
    intro n hn m hm
    have h2 : (fun y : ℝ => g y * (w n m * f n m y))
        = fun y => w n m * (g y * f n m y) := by funext y; ring
    rw [h2]
    exact (hf n hn m hm).const_mul _
  calc ∑ n ∈ S, ∑ m ∈ S', w n m * ∫ y : ℝ, g y * f n m y
      = ∑ n ∈ S, ∑ m ∈ S', ∫ y : ℝ, g y * (w n m * f n m y) := by
        refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
        have h2 : (fun y : ℝ => g y * (w n m * f n m y))
            = fun y => w n m * (g y * f n m y) := by funext y; ring
        rw [h2, integral_const_mul]
    _ = ∑ n ∈ S, ∫ y : ℝ, ∑ m ∈ S', g y * (w n m * f n m y) := by
        refine Finset.sum_congr rfl fun n hn =>
          (integral_finsetSum S' (fun m hm => hG n hn m hm)).symm
    _ = ∫ y : ℝ, ∑ n ∈ S, ∑ m ∈ S', g y * (w n m * f n m y) :=
        (integral_finsetSum (s := S) (f := fun n y => ∑ m ∈ S', g y * (w n m * f n m y))
          (fun n hn => integrable_finset_sum (S := S')
            (f := fun m y => g y * (w n m * f n m y)) (fun m hm => hG n hn m hm))).symm
    _ = ∫ y : ℝ, g y * ∑ n ∈ S, ∑ m ∈ S', w n m * f n m y := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        show (∑ n ∈ S, ∑ m ∈ S', g y * (w n m * f n m y))
            = g y * ∑ n ∈ S, ∑ m ∈ S', w n m * f n m y
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Finset.mul_sum]

/-- The complex power `n ^ (I * τ)` written as an exponential of a real phase. -/
lemma cpow_I_mul_of_one_le {n : ℕ} (hn : 1 ≤ n) (τ : ℝ) :
    (n : ℂ) ^ (Complex.I * (τ : ℂ)) = Complex.exp (↑(τ * Real.log n) * Complex.I) := by
  have hn0 : (n : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : n ≠ 0)
  rw [Complex.cpow_def_of_ne_zero hn0, ← Complex.ofReal_natCast n,
    ← Complex.ofReal_log (by positivity : (0 : ℝ) ≤ n)]
  congr 1
  push_cast
  ring

/-- Real analogue of `sum_mul_integral_eq_integral_sum`. -/
lemma sum_mul_integral_eq_integral_sum_real {ι κ : Type*}
    (w : ι → κ → ℝ) (f : ι → κ → ℝ → ℝ) (S : Finset ι) (S' : Finset κ) {g : ℝ → ℝ}
    (hg : Integrable g) (hf : ∀ n ∈ S, ∀ m ∈ S', Integrable (fun y : ℝ => g y * f n m y)) :
    (∑ n ∈ S, ∑ m ∈ S', w n m * ∫ y : ℝ, g y * f n m y)
      = ∫ y : ℝ, g y * ∑ n ∈ S, ∑ m ∈ S', w n m * f n m y := by
  classical
  have hG : ∀ n ∈ S, ∀ m ∈ S', Integrable (fun y : ℝ => g y * (w n m * f n m y)) := by
    intro n hn m hm
    have h2 : (fun y : ℝ => g y * (w n m * f n m y))
        = fun y => w n m * (g y * f n m y) := by funext y; ring
    rw [h2]
    exact (hf n hn m hm).const_mul _
  calc ∑ n ∈ S, ∑ m ∈ S', w n m * ∫ y : ℝ, g y * f n m y
      = ∑ n ∈ S, ∑ m ∈ S', ∫ y : ℝ, g y * (w n m * f n m y) := by
        refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
        have h2 : (fun y : ℝ => g y * (w n m * f n m y))
            = fun y => w n m * (g y * f n m y) := by funext y; ring
        rw [h2, integral_const_mul]
    _ = ∑ n ∈ S, ∫ y : ℝ, ∑ m ∈ S', g y * (w n m * f n m y) := by
        refine Finset.sum_congr rfl fun n hn =>
          (integral_finsetSum S' (fun m hm => hG n hn m hm)).symm
    _ = ∫ y : ℝ, ∑ n ∈ S, ∑ m ∈ S', g y * (w n m * f n m y) :=
        (integral_finsetSum (s := S) (f := fun n y => ∑ m ∈ S', g y * (w n m * f n m y))
          (fun n hn => integrable_finset_sum (S := S')
            (f := fun m y => g y * (w n m * f n m y)) (fun m hm => hG n hn m hm))).symm
    _ = ∫ y : ℝ, g y * ∑ n ∈ S, ∑ m ∈ S', w n m * f n m y := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        show (∑ n ∈ S, ∑ m ∈ S', g y * (w n m * f n m y))
            = g y * ∑ n ∈ S, ∑ m ∈ S', w n m * f n m y
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Finset.mul_sum]

lemma sum4_comm {ι₁ ι₂ ι₃ ι₄ M : Type*} [Fintype ι₁] [Fintype ι₂] [AddCommMonoid M]
    (S : Finset ι₃) (S' : Finset ι₄) (f : ι₁ → ι₂ → ι₃ → ι₄ → M) :
    (∑ i, ∑ j, ∑ n ∈ S, ∑ m ∈ S', f i j n m) = ∑ n ∈ S, ∑ m ∈ S', ∑ i, ∑ j, f i j n m := by
  have h1 : (∑ i, ∑ j, ∑ n ∈ S, ∑ m ∈ S', f i j n m)
      = ∑ i, ∑ n ∈ S, ∑ j, ∑ m ∈ S', f i j n m := by
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Finset.sum_comm (s := Finset.univ) (t := S) (f := fun j n => ∑ m ∈ S', f i j n m)
  have h2 : (∑ i, ∑ n ∈ S, ∑ j, ∑ m ∈ S', f i j n m)
      = ∑ n ∈ S, ∑ i, ∑ j, ∑ m ∈ S', f i j n m :=
    Finset.sum_comm (s := Finset.univ) (t := S) (f := fun i n => ∑ j, ∑ m ∈ S', f i j n m)
  have h3 : (∑ n ∈ S, ∑ i, ∑ j, ∑ m ∈ S', f i j n m)
      = ∑ n ∈ S, ∑ i, ∑ m ∈ S', ∑ j, f i j n m := by
    refine Finset.sum_congr rfl fun n _ => ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Finset.sum_comm (s := Finset.univ) (t := S') (f := fun j m => f i j n m)
  have h4 : (∑ n ∈ S, ∑ i, ∑ m ∈ S', ∑ j, f i j n m)
      = ∑ n ∈ S, ∑ m ∈ S', ∑ i, ∑ j, f i j n m := by
    refine Finset.sum_congr rfl fun n _ => ?_
    exact Finset.sum_comm (s := Finset.univ) (t := S') (f := fun i m => ∑ j, f i j n m)
  rw [h1, h2, h3, h4]

theorem fejer_window_localization_majorant :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ), 0 < ε → ε ≤ 1 / 4 → ∀ (Δ : ℝ), 0 < Δ →
    ∀ (N : ℕ), 1 ≤ N → ∀ (c : ℕ → ℝ), ∀ (a : ℕ → ℂ), (∀ n, ‖a n‖ ≤ c n) →
    ∀ (R : ℕ) (t : Fin R → ℝ), (∀ i j, i ≠ j → 1 ≤ |t i - t j|) →
    (∑ i : Fin R, ∑ j : Fin R,
      (if |t i - t j| ≤ Δ then
        ‖∑ n ∈ Finset.Icc N (2 * N),
          a n * (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2
       else 0))
    ≤ C / ε * (∑ i : Fin R, ∑ j : Fin R,
      (if |t i - t j| ≤ 4 * ε * Δ then
        ‖∑ n ∈ Finset.Icc N (2 * N),
          (c n : ℂ) * (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2
       else 0)) := by
  refine ⟨8, by norm_num, ?_⟩
  intro ε hε hε4 Δ hΔ N hN c a ha R t hsep
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hTpos : (0:ℝ) < 4 * Δ := by positivity
  have hc_nonneg : ∀ n, 0 ≤ c n := fun n => (norm_nonneg (a n)).trans (ha n)
  set S : Finset ℕ := Finset.Icc N (2 * N) with hS
  set L : ℕ → ℝ := fun n => Real.log n with hL
  set ph : ℕ → ℕ → Fin R → ℂ := fun n m i => Complex.exp (↑((L n - L m) * (t i)) * Complex.I) with hph
  set q : ℕ → Fin R → Fin R → ℂ := fun n i j => Complex.exp (↑(L n * (t i - t j)) * Complex.I) with hq
  set zp : ℕ → Fin R → Fin R → ℂ := fun n i j => q n i j / (Real.sqrt (n:ℝ):ℂ) with hzp
  set A : Fin R → Fin R → ℂ := fun i j => ∑ n ∈ S, a n * zp n i j with hA
  set B : Fin R → Fin R → ℂ := fun i j => ∑ n ∈ S, (c n : ℂ) * zp n i j with hB
  set Zf : ℕ → ℕ → ℝ → ℂ := fun n m y => ∑ i : Fin R,
      ph n m i * Complex.exp (↑(-(2 * Real.pi * y * (t i) / (4 * Δ))) * Complex.I) with hZf
  set Vf : ℝ → ℝ := fun y => ∑ n ∈ S, ∑ m ∈ S,
      (c n * c m) / (Real.sqrt (n:ℝ) * Real.sqrt (m:ℝ)) * ‖Zf n m y‖ ^ 2 with hVf
  set wf : ℕ → ℕ → ℂ := fun n m =>
      (a n * (starRingEnd ℂ) (a m)) / ((Real.sqrt (n:ℝ):ℂ) * (Real.sqrt (m:ℝ):ℂ)) with hwf
  set wc : ℕ → ℕ → ℝ := fun n m =>
      (c n * c m) / (Real.sqrt (n:ℝ) * Real.sqrt (m:ℝ)) with hwc
  set Uf : ℝ → ℂ := fun y => ∑ n ∈ S, ∑ m ∈ S,
      wf n m * ((‖Zf n m y‖ ^ 2 : ℝ) : ℂ) with hUf
  set Qr : ℝ := ∑ i : Fin R, ∑ j : Fin R,
      (Real.sinc (Real.pi * ((t i - t j) / (4 * Δ)))) ^ 2 * ‖A i j‖ ^ 2 with hQ
  have hQnn : 0 ≤ Qr := by
    rw [hQ]
    refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
    exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have htri_nonneg : ∀ y : ℝ, 0 ≤ tri y := by
    intro y; rw [show tri y = max (1 - |y|) 0 from rfl]; exact le_max_right _ _
  have hph1 : ∀ (n m : ℕ) (i : Fin R), ‖ph n m i‖ = 1 := by
    intro n m i
    rw [hph]
    exact Complex.norm_exp_ofReal_mul_I _
  have hexp1 : ∀ (y : ℝ) (i : Fin R),
      ‖Complex.exp (↑(-(2 * Real.pi * y * (t i) / (4 * Δ))) * Complex.I)‖ = 1 :=
    fun y i => Complex.norm_exp_ofReal_mul_I _
  have hZbdd : ∀ (n m : ℕ) (y : ℝ), ‖Zf n m y‖ ≤ R := by
    intro n m y
    rw [hZf]
    calc ‖∑ i : Fin R, ph n m i * Complex.exp (↑(-(2 * Real.pi * y * (t i) / (4 * Δ))) * Complex.I)‖
        ≤ ∑ i : Fin R, ‖ph n m i * Complex.exp (↑(-(2 * Real.pi * y * (t i) / (4 * Δ))) * Complex.I)‖ :=
          norm_sum_le _ _
      _ = ∑ i : Fin R, (1:ℝ) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [norm_mul, hph1 n m i, hexp1 y i, one_mul]
      _ = R := by simp
  have hZcont : ∀ n m : ℕ, Continuous (fun y : ℝ => Zf n m y) := by
    intro n m
    show Continuous (fun y : ℝ => ∑ i : Fin R,
      ph n m i * Complex.exp (↑(-(2 * Real.pi * y * (t i) / (4 * Δ))) * Complex.I))
    refine continuous_finset_sum _ fun i _ => ?_
    exact continuous_const.mul (by fun_prop)
  have hVcont : Continuous (fun y : ℝ => Vf y) := by
    show Continuous (fun y : ℝ => ∑ n ∈ S, ∑ m ∈ S,
      (c n * c m) / (Real.sqrt (n:ℝ) * Real.sqrt (m:ℝ)) * ‖Zf n m y‖ ^ 2)
    refine continuous_finset_sum _ fun n hn => continuous_finset_sum _ fun m hm => ?_
    exact ((hZcont n m).norm.pow 2).const_mul _
  have hUcont : Continuous (fun y : ℝ => Uf y) := by
    show Continuous (fun y : ℝ => ∑ n ∈ S, ∑ m ∈ S,
      wf n m * ((‖Zf n m y‖ ^ 2 : ℝ) : ℂ))
    refine continuous_finset_sum _ fun n hn => continuous_finset_sum _ fun m hm => ?_
    exact ((Complex.continuous_ofReal.comp ((hZcont n m).norm.pow 2))).const_mul _
  have hVnn : ∀ y : ℝ, 0 ≤ Vf y := by
    intro y
    rw [hVf]
    refine Finset.sum_nonneg fun n _ => Finset.sum_nonneg fun m _ => ?_
    exact mul_nonneg (div_nonneg (mul_nonneg (hc_nonneg n) (hc_nonneg m))
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))) (sq_nonneg _)
  set M : ℝ := (R:ℝ) ^ 2 * (∑ n ∈ S, c n / Real.sqrt (n:ℝ)) ^ 2 with hMdef
  have hMnn : 0 ≤ M := by
    rw [hMdef]; positivity
  have hVbdd : ∀ y : ℝ, Vf y ≤ M := by
    intro y
    rw [hVf, hMdef]
    have hterm : ∀ n ∈ S, ∀ m ∈ S,
        (c n * c m) / (Real.sqrt (n:ℝ) * Real.sqrt (m:ℝ)) * ‖Zf n m y‖ ^ 2
        ≤ (R:ℝ) ^ 2 * ((c n / Real.sqrt (n:ℝ)) * (c m / Real.sqrt (m:ℝ))) := by
      intro n hn m hm
      have hs1 : 0 ≤ Real.sqrt (n:ℝ) := Real.sqrt_nonneg _
      have hs2 : 0 ≤ Real.sqrt (m:ℝ) := Real.sqrt_nonneg _
      have h1 : ‖Zf n m y‖ ^ 2 ≤ (R:ℝ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hZbdd n m y) 2
      have h2 : (c n * c m) / (Real.sqrt (n:ℝ) * Real.sqrt (m:ℝ))
          = (c n / Real.sqrt (n:ℝ)) * (c m / Real.sqrt (m:ℝ)) := by ring
      have h3 : 0 ≤ (c n / Real.sqrt (n:ℝ)) * (c m / Real.sqrt (m:ℝ)) :=
        mul_nonneg (div_nonneg (hc_nonneg n) hs1) (div_nonneg (hc_nonneg m) hs2)
      rw [h2]
      nlinarith [h1, h3, mul_nonneg h3 (sq_nonneg ‖Zf n m y‖)]
    calc ∑ n ∈ S, ∑ m ∈ S,
          (c n * c m) / (Real.sqrt (n:ℝ) * Real.sqrt (m:ℝ)) * ‖Zf n m y‖ ^ 2
        ≤ ∑ n ∈ S, ∑ m ∈ S, (R:ℝ) ^ 2 * ((c n / Real.sqrt (n:ℝ)) * (c m / Real.sqrt (m:ℝ))) :=
          Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun m hm => hterm n hn m hm
      _ = (R:ℝ) ^ 2 * (∑ n ∈ S, c n / Real.sqrt (n:ℝ)) ^ 2 := by
          have h1 : (∑ n ∈ S, ∑ m ∈ S, (c n / Real.sqrt (n:ℝ)) * (c m / Real.sqrt (m:ℝ)))
              = (∑ n ∈ S, c n / Real.sqrt (n:ℝ)) ^ 2 := by
            rw [pow_two, Finset.sum_mul_sum]
          rw [← h1, Finset.mul_sum]
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [Finset.mul_sum]
  have hsinc_le_one : ∀ u : ℝ, Real.sinc u ^ 2 ≤ 1 := by
    intro u
    have h1 : |Real.sinc u| ≤ 1 := abs_sinc_le_one u
    have h2 : Real.sinc u ^ 2 = |Real.sinc u| ^ 2 := (sq_abs _).symm
    rw [h2]
    nlinarith [h1, abs_nonneg (Real.sinc u)]
  have hexp_eq : ∀ (n : ℕ) (τ : ℝ),
      Complex.exp (↑(τ * Real.log n) * Complex.I) = Complex.exp (↑(L n * τ) * Complex.I) := by
    intro n τ
    rw [hL]
    congr 1
    push_cast
    ring
  have hAeq : ∀ i j : Fin R,
      (∑ n ∈ S, a n * (n:ℂ) ^ (Complex.I * ((t i - t j : ℝ):ℂ)) / (Real.sqrt (n:ℝ):ℂ)) = A i j := by
    intro i j
    rw [hA]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := hN.trans (Finset.mem_Icc.mp hn).1
    rw [mul_div_assoc, cpow_I_mul_of_one_le hn1 (t i - t j),
      hexp_eq n (t i - t j), hzp, hq]
  have hBeq : ∀ i j : Fin R,
      (∑ n ∈ S, (c n : ℂ) * (n:ℂ) ^ (Complex.I * ((t i - t j : ℝ):ℂ)) / (Real.sqrt (n:ℝ):ℂ)) = B i j := by
    intro i j
    rw [hB]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := hN.trans (Finset.mem_Icc.mp hn).1
    rw [mul_div_assoc, cpow_I_mul_of_one_le hn1 (t i - t j),
      hexp_eq n (t i - t j), hzp, hq]
  have hstepA : (∑ i : Fin R, ∑ j : Fin R,
      (if |t i - t j| ≤ Δ then
        ‖∑ n ∈ S, a n * (n:ℂ) ^ (Complex.I * ((t i - t j : ℝ):ℂ)) / (Real.sqrt (n:ℝ):ℂ)‖ ^ 2
       else 0)) ≤ 2 * Qr := by
    have h1 : (∑ i : Fin R, ∑ j : Fin R,
        (if |t i - t j| ≤ Δ then
          ‖∑ n ∈ S, a n * (n:ℂ) ^ (Complex.I * ((t i - t j : ℝ):ℂ)) / (Real.sqrt (n:ℝ):ℂ)‖ ^ 2
         else 0))
        = ∑ i : Fin R, ∑ j : Fin R, (if |t i - t j| ≤ Δ then ‖A i j‖ ^ 2 else 0) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hAeq i j]
    rw [h1, hQ]
    calc ∑ i : Fin R, ∑ j : Fin R, (if |t i - t j| ≤ Δ then ‖A i j‖ ^ 2 else 0)
        ≤ ∑ i : Fin R, ∑ j : Fin R,
            2 * ((Real.sinc (Real.pi * ((t i - t j) / (4 * Δ)))) ^ 2 * ‖A i j‖ ^ 2) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          by_cases h : |t i - t j| ≤ Δ
          · rw [if_pos h]
            have habs : |(t i - t j) / (4 * Δ)| ≤ 1 / 4 := by
              rw [abs_div, abs_of_pos hTpos, div_le_iff₀ hTpos]
              nlinarith
            have hs := sinc_pi_sq_lower_bound habs
            nlinarith [sq_nonneg ‖A i j‖]
          · rw [if_neg h]
            positivity
      _ = 2 * ∑ i : Fin R, ∑ j : Fin R,
            (Real.sinc (Real.pi * ((t i - t j) / (4 * Δ)))) ^ 2 * ‖A i j‖ ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
  have hczp : ∀ (m : ℕ) (i j : Fin R),
      (starRingEnd ℂ) (zp m i j) = (starRingEnd ℂ) (q m i j) / (Real.sqrt (m:ℝ):ℂ) := by
    intro m i j
    rw [hzp, map_div₀]
    congr 1
    exact Complex.conj_ofReal _
  have hkey : ∀ (n m : ℕ) (i j : Fin R),
      q n i j * (starRingEnd ℂ) (q m i j) = ph n m i * (starRingEnd ℂ) (ph n m j) := by
    intro n m i j
    simp only [hq, hph, star_exp_ofReal_mul_I, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hAA : ∀ i j : Fin R, A i j * (starRingEnd ℂ) (A i j)
      = ∑ n ∈ S, ∑ m ∈ S, wf n m * (ph n m i * (starRingEnd ℂ) (ph n m j)) := by
    intro i j
    simp only [hA]
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    rw [map_mul, hczp m i j, hzp]
    rw [show (a n * (q n i j / (Real.sqrt (n:ℝ):ℂ)))
          * ((starRingEnd ℂ) (a m) * ((starRingEnd ℂ) (q m i j) / (Real.sqrt (m:ℝ):ℂ)))
        = ((a n * (starRingEnd ℂ) (a m)) / ((Real.sqrt (n:ℝ):ℂ) * (Real.sqrt (m:ℝ):ℂ)))
          * (q n i j * (starRingEnd ℂ) (q m i j)) from by ring,
      hkey n m i j]
  have hnormA : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := by
    intro z
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  have hQc : (Qr : ℂ) = ∑ i : Fin R, ∑ j : Fin R,
      ((Real.sinc (Real.pi * ((t i - t j) / (4 * Δ))) ^ 2 : ℝ) : ℂ)
        * (A i j * (starRingEnd ℂ) (A i j)) := by
    rw [hQ, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.ofReal_mul, hnormA]
  have hQ2 : (Qr : ℂ) = ∑ n ∈ S, ∑ m ∈ S, wf n m *
      (∑ i : Fin R, ∑ j : Fin R, ((Real.sinc (Real.pi * ((t i - t j) / (4 * Δ))) ^ 2 : ℝ) : ℂ)
        * (ph n m i * (starRingEnd ℂ) (ph n m j))) := by
    rw [hQc]
    have hnorm : (∑ i : Fin R, ∑ j : Fin R,
          ((Real.sinc (Real.pi * ((t i - t j) / (4 * Δ))) ^ 2 : ℝ) : ℂ)
            * (A i j * (starRingEnd ℂ) (A i j)))
        = ∑ i : Fin R, ∑ j : Fin R, ∑ n ∈ S, ∑ m ∈ S, wf n m *
            (((Real.sinc (Real.pi * ((t i - t j) / (4 * Δ))) ^ 2 : ℝ) : ℂ)
              * (ph n m i * (starRingEnd ℂ) (ph n m j))) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hAA i j, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring
    rw [hnorm, sum4_comm]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  have hident : ∀ n m : ℕ,
      (∑ i : Fin R, ∑ j : Fin R, ((Real.sinc (Real.pi * ((t i - t j) / (4 * Δ))) ^ 2 : ℝ) : ℂ)
          * (ph n m i * (starRingEnd ℂ) (ph n m j)))
        = ∫ y : ℝ, (tri y : ℂ) * ((‖Zf n m y‖ ^ 2 : ℝ) : ℂ) :=
    fun n m => fejer_expansion_identity tri_integrable
      (Ĝ := fun s : ℝ => ((Real.sinc (Real.pi * s) ^ 2 : ℝ) : ℂ))
      (fun s => integral_tri_mul_exp s) (4 * Δ) t (ph n m)
  have hQ3 : (Qr : ℂ) = ∑ n ∈ S, ∑ m ∈ S, wf n m *
      ∫ y : ℝ, (tri y : ℂ) * ((‖Zf n m y‖ ^ 2 : ℝ) : ℂ) := by
    rw [hQ2]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    rw [hident n m]
  have hstepB : (Qr : ℂ) = ∫ y : ℝ, (tri y : ℂ) * Uf y := by
    rw [hQ3]
    refine sum_mul_integral_eq_integral_sum wf (fun n m y => ((‖Zf n m y‖ ^ 2 : ℝ) : ℂ)) S S
      (g := fun y : ℝ => (tri y : ℂ)) tri_integrable.ofReal ?_
    intro n hn m hm
    refine Integrable.mono' (tri_integrable.const_mul ((R:ℝ)^2))
      (((Complex.continuous_ofReal.comp tri_continuous).aestronglyMeasurable).mul
        ((Complex.continuous_ofReal.comp ((hZcont n m).norm.pow 2)).aestronglyMeasurable)) ?_
    filter_upwards with y
    rw [norm_mul, norm_ofReal_of_nonneg (htri_nonneg y), norm_ofReal_of_nonneg (sq_nonneg _)]
    have hb := hZbdd n m y
    have hb2 : ‖Zf n m y‖ ^ 2 ≤ (R:ℝ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    nlinarith [htri_nonneg y, norm_nonneg (Zf n m y)]
  have hUnorm : ∀ y : ℝ, ‖Uf y‖ ≤ Vf y := by
    intro y
    rw [hUf, hVf]
    calc ‖∑ n ∈ S, ∑ m ∈ S, wf n m * ((‖Zf n m y‖ ^ 2 : ℝ) : ℂ)‖
        ≤ ∑ n ∈ S, ‖∑ m ∈ S, wf n m * ((‖Zf n m y‖ ^ 2 : ℝ) : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ S, ∑ m ∈ S, ‖wf n m * ((‖Zf n m y‖ ^ 2 : ℝ) : ℂ)‖ :=
          Finset.sum_le_sum fun n _ => norm_sum_le _ _
      _ ≤ ∑ n ∈ S, ∑ m ∈ S,
            (c n * c m) / (Real.sqrt (n:ℝ) * Real.sqrt (m:ℝ)) * ‖Zf n m y‖ ^ 2 := by
          refine Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun m hm => ?_
          rw [norm_mul, norm_ofReal_of_nonneg (sq_nonneg _)]
          have hn1 : 1 ≤ n := hN.trans (Finset.mem_Icc.mp hn).1
          have hm1 : 1 ≤ m := hN.trans (Finset.mem_Icc.mp hm).1
          have hsn : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos_of_pos (by exact_mod_cast hn1)
          have hsm : 0 < Real.sqrt (m:ℝ) := Real.sqrt_pos_of_pos (by exact_mod_cast hm1)
          have hwn : ‖wf n m‖ = (‖a n‖ * ‖a m‖) / (Real.sqrt (n:ℝ) * Real.sqrt (m:ℝ)) := by
            rw [hwf, norm_div, norm_mul, Complex.norm_conj]
            congr 1
            rw [norm_mul, norm_ofReal_of_nonneg (Real.sqrt_nonneg _),
              norm_ofReal_of_nonneg (Real.sqrt_nonneg _)]
          rw [hwn]
          have h1 : ‖a n‖ * ‖a m‖ ≤ c n * c m :=
            mul_le_mul (ha n) (ha m) (norm_nonneg _) (hc_nonneg n)
          have h2 : (0:ℝ) < Real.sqrt (n:ℝ) * Real.sqrt (m:ℝ) := mul_pos hsn hsm
          have h3 : ‖a n‖ * ‖a m‖ / (Real.sqrt (n:ℝ) * Real.sqrt (m:ℝ))
              ≤ c n * c m / (Real.sqrt (n:ℝ) * Real.sqrt (m:ℝ)) :=
            div_le_div_of_nonneg_right h1 h2.le
          nlinarith [h3, sq_nonneg ‖Zf n m y‖]
  have hstepC : Qr ≤ ∫ y : ℝ, tri y * Vf y := by
    have h1 : Qr = ‖(Qr : ℂ)‖ := by
      rw [show ‖(Qr : ℂ)‖ = |Qr| from RCLike.norm_ofReal Qr, abs_of_nonneg hQnn]
    rw [h1, hstepB]
    have hint1 : Integrable (fun y : ℝ => tri y * ‖Uf y‖) := by
      refine Integrable.mono' (tri_integrable.const_mul M)
        (tri_continuous.aestronglyMeasurable.mul hUcont.norm.aestronglyMeasurable) ?_
      filter_upwards with y
      show ‖tri y * ‖Uf y‖‖ ≤ M * tri y
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (htri_nonneg y) (norm_nonneg _))]
      nlinarith [htri_nonneg y, hUnorm y, hVbdd y, hMnn]
    have hint2 : Integrable (fun y : ℝ => tri y * Vf y) := by
      refine Integrable.mono' (tri_integrable.const_mul M)
        (tri_continuous.aestronglyMeasurable.mul hVcont.aestronglyMeasurable) ?_
      filter_upwards with y
      show ‖tri y * Vf y‖ ≤ M * tri y
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (htri_nonneg y) (hVnn y))]
      nlinarith [htri_nonneg y, hVbdd y, hMnn]
    calc ‖∫ y : ℝ, (tri y : ℂ) * Uf y‖
        ≤ ∫ y : ℝ, ‖(tri y : ℂ) * Uf y‖ := norm_integral_le_integral_norm _
      _ = ∫ y : ℝ, tri y * ‖Uf y‖ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          show ‖(tri y : ℂ) * Uf y‖ = tri y * ‖Uf y‖
          rw [norm_mul, norm_ofReal_of_nonneg (htri_nonneg y)]
      _ ≤ ∫ y : ℝ, tri y * Vf y := by
          refine integral_mono hint1 hint2 ?_
          intro y
          exact mul_le_mul_of_nonneg_left (hUnorm y) (htri_nonneg y)
  have hstepD : (∫ y : ℝ, tri y * Vf y) ≤ 2 * ∫ y : ℝ, Real.sinc (Real.pi * (ε * y)) ^ 2 * Vf y := by
    have hpoint : ∀ y : ℝ, tri y ≤ 2 * Real.sinc (Real.pi * (ε * y)) ^ 2 := by
      intro y
      rcases le_or_gt |y| 1 with hy | hy
      · have h1 : |ε * y| ≤ 1 / 4 := by
          rw [abs_mul, abs_of_pos hε]
          calc ε * |y| ≤ (1 / 4) * 1 := mul_le_mul hε4 hy (abs_nonneg y) (by norm_num)
            _ = 1 / 4 := by norm_num
        have hs := sinc_pi_sq_lower_bound h1
        have ht := tri_eq_one_sub hy
        rw [ht]
        linarith [abs_nonneg y, hs]
      · rw [tri_eq_zero_of_one_le_abs hy.le]
        positivity
    have hint1 : Integrable (fun y : ℝ => tri y * Vf y) := by
      refine Integrable.mono' (tri_integrable.const_mul M)
        (tri_continuous.aestronglyMeasurable.mul hVcont.aestronglyMeasurable) ?_
      filter_upwards with y
      show ‖tri y * Vf y‖ ≤ M * tri y
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (htri_nonneg y) (hVnn y))]
      nlinarith [htri_nonneg y, hVbdd y, hMnn]
    have hint2 : Integrable (fun y : ℝ => (2 * Real.sinc (Real.pi * (ε * y)) ^ 2) * Vf y) := by
      have h2 : Integrable (fun y : ℝ =>
          2 * Real.sinc (Real.pi * (ε * y)) ^ 2 * M) :=
        ((integrable_sinc_pi_sq.comp_mul_left' hε.ne').const_mul 2).mul_const M
      refine Integrable.mono' h2 ((by fun_prop : Continuous (fun y : ℝ =>
          Real.sinc (Real.pi * (ε * y)) ^ 2)).const_mul _ |>.mul hVcont).aestronglyMeasurable ?_
      filter_upwards with y
      show ‖(2 * Real.sinc (Real.pi * (ε * y)) ^ 2) * Vf y‖ ≤ 2 * Real.sinc (Real.pi * (ε * y)) ^ 2 * M
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
        (mul_nonneg (by norm_num) (sq_nonneg _)) (hVnn y))]
      have hs := hsinc_le_one (Real.pi * (ε * y))
      have hsnn : 0 ≤ Real.sinc (Real.pi * (ε * y)) ^ 2 := sq_nonneg _
      nlinarith [hVbdd y, hVnn y, hs, hMnn]
    calc ∫ y : ℝ, tri y * Vf y
        ≤ ∫ y : ℝ, (2 * Real.sinc (Real.pi * (ε * y)) ^ 2) * Vf y := by
          refine integral_mono hint1 hint2 ?_
          intro y
          have h := hpoint y
          nlinarith [hVnn y]
      _ = 2 * ∫ y : ℝ, Real.sinc (Real.pi * (ε * y)) ^ 2 * Vf y := by
          rw [← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          show (2 * Real.sinc (Real.pi * (ε * y)) ^ 2) * Vf y
            = 2 * (Real.sinc (Real.pi * (ε * y)) ^ 2 * Vf y)
          ring
  have hstepE : (∫ y : ℝ, Real.sinc (Real.pi * (ε * y)) ^ 2 * Vf y)
      = (1 / ε) * ∫ y : ℝ, Real.sinc (Real.pi * y) ^ 2 * Vf (y / ε) := by
    have h := Measure.integral_comp_mul_left (fun u : ℝ => Real.sinc (Real.pi * u) ^ 2 * Vf (u / ε)) ε
    have hL : (∫ x : ℝ, Real.sinc (Real.pi * (ε * x)) ^ 2 * Vf ((ε * x) / ε))
        = (∫ x : ℝ, Real.sinc (Real.pi * (ε * x)) ^ 2 * Vf x) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show Real.sinc (Real.pi * (ε * x)) ^ 2 * Vf ((ε * x) / ε)
        = Real.sinc (Real.pi * (ε * x)) ^ 2 * Vf x
      rw [mul_div_cancel_left₀ x hεne]
    rw [hL] at h
    rw [h, abs_of_pos (inv_pos.mpr hε), smul_eq_mul, inv_eq_one_div]
  have hstepF : (∫ y : ℝ, Real.sinc (Real.pi * y) ^ 2 * Vf (y / ε))
      ≤ ∑ i : Fin R, ∑ j : Fin R, (if |t i - t j| ≤ 4 * ε * Δ then ‖B i j‖ ^ 2 else 0) := by
    have harg : ∀ (y : ℝ) (i : Fin R),
        -(2 * Real.pi * (y / ε) * (t i) / (4 * Δ))
          = -(2 * Real.pi * y * (t i) / (ε * (4 * Δ))) := by
      intro y i
      ring_nf
    have hZdiv : ∀ (n m : ℕ) (y : ℝ), Zf n m (y / ε)
        = ∑ i : Fin R, ph n m i * Complex.exp (↑(-(2 * Real.pi * y * (t i) / (ε * (4 * Δ)))) * Complex.I) := by
      intro n m y
      show (∑ i : Fin R, ph n m i * Complex.exp (↑(-(2 * Real.pi * (y / ε) * (t i) / (4 * Δ))) * Complex.I))
          = ∑ i : Fin R, ph n m i * Complex.exp (↑(-(2 * Real.pi * y * (t i) / (ε * (4 * Δ)))) * Complex.I)
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [harg y i]
    have hintF : ∀ n ∈ S, ∀ m ∈ S,
        Integrable (fun y : ℝ => Real.sinc (Real.pi * y) ^ 2 * ‖Zf n m (y / ε)‖ ^ 2) := by
      intro n hn m hm
      refine Integrable.mono' (integrable_sinc_pi_sq.const_mul ((R:ℝ) ^ 2))
        (((by fun_prop : Continuous (fun y : ℝ => Real.sinc (Real.pi * y) ^ 2)).mul
          (((hZcont n m).comp (by fun_prop : Continuous fun y : ℝ => y / ε)).norm.pow 2)).aestronglyMeasurable) ?_
      filter_upwards with y
      show ‖Real.sinc (Real.pi * y) ^ 2 * ‖Zf n m (y / ε)‖ ^ 2‖ ≤ (R:ℝ) ^ 2 * Real.sinc (Real.pi * y) ^ 2
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      have hb := hZbdd n m (y / ε)
      have hb2 : ‖Zf n m (y / ε)‖ ^ 2 ≤ (R:ℝ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
      have hs := hsinc_le_one (Real.pi * y)
      nlinarith [sq_nonneg (Real.sinc (Real.pi * y)), sq_nonneg ‖Zf n m (y / ε)‖]
    have ha := sum_mul_integral_eq_integral_sum_real wc (fun n m y => ‖Zf n m (y / ε)‖ ^ 2) S S
      (g := fun y : ℝ => Real.sinc (Real.pi * y) ^ 2) integrable_sinc_pi_sq hintF
    rw [← ha]
    have hident2 : ∀ n m : ℕ,
        (∫ y : ℝ, Real.sinc (Real.pi * y) ^ 2 * ‖Zf n m (y / ε)‖ ^ 2)
          = ∑ i : Fin R, ∑ j : Fin R, tri ((t i - t j) / (ε * (4 * Δ)))
              * (ph n m i * (starRingEnd ℂ) (ph n m j)).re := by
      intro n m
      have h := fejer_expansion_identity_re integrable_sinc_pi_sq
        (ĝ := tri) (fun s => integral_sinc_pi_sq_mul_exp s) (ε * (4 * Δ)) t (ph n m)
      rw [h]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      show Real.sinc (Real.pi * y) ^ 2 * ‖Zf n m (y / ε)‖ ^ 2
        = Real.sinc (Real.pi * y) ^ 2 * ‖∑ i : Fin R, ph n m i
            * Complex.exp (↑(-(2 * Real.pi * y * (t i) / (ε * (4 * Δ)))) * Complex.I)‖ ^ 2
      rw [hZdiv n m y]
    have hG : ∀ i j : Fin R,
        (∑ n ∈ S, ∑ m ∈ S, wc n m * (ph n m i * (starRingEnd ℂ) (ph n m j)).re) = ‖B i j‖ ^ 2 := by
      intro i j
      have h1 : (B i j * (starRingEnd ℂ) (B i j)).re
          = ∑ n ∈ S, ∑ m ∈ S, wc n m * (ph n m i * (starRingEnd ℂ) (ph n m j)).re := by
        simp only [hB]
        rw [map_sum, Finset.sum_mul_sum]
        rw [Complex.re_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Complex.re_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [map_mul, hczp m i j, hzp, Complex.conj_ofReal]
        rw [show ((c n : ℂ) * (q n i j / (Real.sqrt (n:ℝ):ℂ))
              * ((c m : ℂ) * ((starRingEnd ℂ) (q m i j) / (Real.sqrt (m:ℝ):ℂ))))
            = (((c n * c m) / (Real.sqrt (n:ℝ) * Real.sqrt (m:ℝ)) : ℝ) : ℂ)
              * (q n i j * (starRingEnd ℂ) (q m i j)) from by push_cast; ring,
          hkey n m i j, Complex.re_ofReal_mul]
      have h2 : (B i j * (starRingEnd ℂ) (B i j)).re = ‖B i j‖ ^ 2 := by
        rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
      rw [← h2, h1]
    have hswap3 : (∑ n ∈ S, ∑ m ∈ S, wc n m * (∑ i : Fin R, ∑ j : Fin R,
          tri ((t i - t j) / (ε * (4 * Δ))) * (ph n m i * (starRingEnd ℂ) (ph n m j)).re))
        = ∑ i : Fin R, ∑ j : Fin R, tri ((t i - t j) / (ε * (4 * Δ))) *
            (∑ n ∈ S, ∑ m ∈ S, wc n m * (ph n m i * (starRingEnd ℂ) (ph n m j)).re) := by
      have e1 : (∑ n ∈ S, ∑ m ∈ S, wc n m * (∑ i : Fin R, ∑ j : Fin R,
            tri ((t i - t j) / (ε * (4 * Δ))) * (ph n m i * (starRingEnd ℂ) (ph n m j)).re))
          = ∑ n ∈ S, ∑ m ∈ S, ∑ i : Fin R, ∑ j : Fin R,
              wc n m * (tri ((t i - t j) / (ε * (4 * Δ)))
                * (ph n m i * (starRingEnd ℂ) (ph n m j)).re) := by
        refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
      rw [e1, ← sum4_comm S S (fun (i : Fin R) (j : Fin R) (n : ℕ) (m : ℕ) =>
        wc n m * (tri ((t i - t j) / (ε * (4 * Δ)))
          * (ph n m i * (starRingEnd ℂ) (ph n m j)).re))]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring
    have hmid : (∑ n ∈ S, ∑ m ∈ S, wc n m *
          ∫ y : ℝ, Real.sinc (Real.pi * y) ^ 2 * ‖Zf n m (y / ε)‖ ^ 2)
        = ∑ i : Fin R, ∑ j : Fin R, tri ((t i - t j) / (ε * (4 * Δ))) * ‖B i j‖ ^ 2 := by
      calc ∑ n ∈ S, ∑ m ∈ S, wc n m * ∫ y : ℝ, Real.sinc (Real.pi * y) ^ 2 * ‖Zf n m (y / ε)‖ ^ 2
          = ∑ n ∈ S, ∑ m ∈ S, wc n m * (∑ i : Fin R, ∑ j : Fin R,
              tri ((t i - t j) / (ε * (4 * Δ))) * (ph n m i * (starRingEnd ℂ) (ph n m j)).re) := by
            refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
            rw [hident2 n m]
        _ = ∑ i : Fin R, ∑ j : Fin R, tri ((t i - t j) / (ε * (4 * Δ))) *
              (∑ n ∈ S, ∑ m ∈ S, wc n m * (ph n m i * (starRingEnd ℂ) (ph n m j)).re) := hswap3
        _ = ∑ i : Fin R, ∑ j : Fin R, tri ((t i - t j) / (ε * (4 * Δ))) * ‖B i j‖ ^ 2 := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            rw [hG i j]
    rw [hmid]
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    by_cases h : |t i - t j| ≤ 4 * ε * Δ
    · rw [if_pos h]
      have h1 : tri ((t i - t j) / (ε * (4 * Δ))) ≤ 1 := by
        rw [show tri ((t i - t j) / (ε * (4 * Δ)))
            = max (1 - |(t i - t j) / (ε * (4 * Δ))|) 0 from rfl]
        exact max_le (by linarith [abs_nonneg ((t i - t j) / (ε * (4 * Δ)))]) (by norm_num)
      nlinarith [sq_nonneg ‖B i j‖]
    · rw [if_neg h]
      have h1 : tri ((t i - t j) / (ε * (4 * Δ))) = 0 := by
        apply tri_eq_zero_of_one_le_abs
        rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < ε * (4 * Δ)), le_div_iff₀ (by positivity)]
        nlinarith [not_le.mp h]
      rw [h1, zero_mul]
  have hRHSeq : (∑ i : Fin R, ∑ j : Fin R,
      (if |t i - t j| ≤ 4 * ε * Δ then
        ‖∑ n ∈ S, (c n : ℂ) * (n:ℂ) ^ (Complex.I * ((t i - t j : ℝ):ℂ)) / (Real.sqrt (n:ℝ):ℂ)‖ ^ 2
       else 0))
      = ∑ i : Fin R, ∑ j : Fin R, (if |t i - t j| ≤ 4 * ε * Δ then ‖B i j‖ ^ 2 else 0) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hBeq i j]
  have hRHSnn : 0 ≤ ∑ i : Fin R, ∑ j : Fin R,
      (if |t i - t j| ≤ 4 * ε * Δ then ‖B i j‖ ^ 2 else 0) := by
    refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
    split_ifs
    · exact sq_nonneg _
    · exact le_refl 0
  rw [hRHSeq]
  calc (∑ i : Fin R, ∑ j : Fin R,
      (if |t i - t j| ≤ Δ then
        ‖∑ n ∈ S, a n * (n:ℂ) ^ (Complex.I * ((t i - t j : ℝ):ℂ)) / (Real.sqrt (n:ℝ):ℂ)‖ ^ 2
       else 0))
      ≤ 2 * Qr := hstepA
    _ ≤ 2 * (∫ y : ℝ, tri y * Vf y) := by linarith
    _ ≤ 2 * (2 * ∫ y : ℝ, Real.sinc (Real.pi * (ε * y)) ^ 2 * Vf y) := by linarith
    _ = 4 * (∫ y : ℝ, Real.sinc (Real.pi * (ε * y)) ^ 2 * Vf y) := by ring
    _ = 4 * ((1 / ε) * ∫ y : ℝ, Real.sinc (Real.pi * y) ^ 2 * Vf (y / ε)) := by rw [hstepE]
    _ = (4 / ε) * (∫ y : ℝ, Real.sinc (Real.pi * y) ^ 2 * Vf (y / ε)) := by ring
    _ ≤ (4 / ε) * (∑ i : Fin R, ∑ j : Fin R,
          (if |t i - t j| ≤ 4 * ε * Δ then ‖B i j‖ ^ 2 else 0)) :=
        mul_le_mul_of_nonneg_left hstepF (by positivity)
    _ ≤ (8 / ε) * (∑ i : Fin R, ∑ j : Fin R,
          (if |t i - t j| ≤ 4 * ε * Δ then ‖B i j‖ ^ 2 else 0)) := by
        refine mul_le_mul_of_nonneg_right ?_ hRHSnn
        exact div_le_div_of_nonneg_right (by norm_num) hε.le

end Commons.Analysis.Fourier