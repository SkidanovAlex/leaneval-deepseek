import Mathlib.Algebra.Order.Star.Real
import Submission.Commons.NumberTheory.Linnik.tentF1_laplace

open Complex
open scoped Interval

namespace Commons.NumberTheory.Linnik

/-! # `tentF1_boundary`

Boundary identity for the Laplace-transform comparison used in Lemma 4.1 /
(13.2) of Heath-Brown 1992 (§13): with `z = i·t` purely imaginary,

`Re ∫₀^K e^(−i·t·u)·sinh((K−u)·x) du = (x/2)·e^(xK)·|F₂|²`,

where `F₂ = (1 − e^(−K·(x+i·t)))/(x + i·t)` is the analytic factor of
§13.  We prove it by evaluating the integral through `tentF1_laplace` and
computing the real part of the resulting closed form in elementary terms.
-/

private lemma exp_real_mul (a K : ℝ) : Complex.exp (a * (K : ℂ)) = (Real.exp (a * K) : ℂ) := by
  have harg : (a : ℂ) * (K : ℂ) = ((a * K : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul]
  rw [harg]
  exact (Complex.ofReal_exp (a * K)).symm

private lemma exp_real_mul_neg (a K : ℝ) :
    Complex.exp (-(a * (K : ℂ))) = (Real.exp (-(a * K)) : ℂ) := by
  have harg : -((a : ℂ) * (K : ℂ)) = ((-a : ℝ) : ℂ) * (K : ℂ) := by
    rw [Complex.ofReal_neg]
    ring
  rw [harg]
  rw [show Real.exp (-(a * K)) = Real.exp ((-(a : ℝ)) * K) by
    congr 1
    ring]
  exact exp_real_mul (-a) K

private lemma denom_sq (x t : ℝ) :
    (x : ℂ) ^ 2 - (Complex.I * (t : ℂ)) ^ 2 = ((x ^ 2 + t ^ 2 : ℝ) : ℂ) := by
  calc
    (x : ℂ) ^ 2 - (Complex.I * (t : ℂ)) ^ 2
        = (x : ℂ) ^ 2 + (t : ℂ) ^ 2 := by
          rw [mul_pow, Complex.I_sq]
          ring
    _ = ((x ^ 2 : ℝ) : ℂ) + ((t ^ 2 : ℝ) : ℂ) := by
          rw [← Complex.ofReal_pow]
          rw [← Complex.ofReal_pow]
    _ = ((x ^ 2 + t ^ 2 : ℝ) : ℂ) := by
          rw [Complex.ofReal_add]

private lemma exp_pure_im_re (t K : ℝ) :
    (Complex.exp (-(Complex.I * (t : ℂ) * (K : ℂ)))).re = Real.cos (t * K) := by
  rw [Complex.exp_re]
  simp

private lemma re_half (w : ℂ) : (((1 / 2 : ℂ) * w)).re = w.re / 2 := by
  rw [Complex.mul_re]
  simp
  ring

private lemma re_div_add_I (a x t : ℝ) :
    (((a : ℂ) / ((x : ℂ) + Complex.I * (t : ℂ)))).re = a * x / (x ^ 2 + t ^ 2) := by
  rw [Complex.div_re]
  have hnorm : Complex.normSq ((x : ℂ) + Complex.I * (t : ℂ)) = x ^ 2 + t ^ 2 := by
    rw [Complex.normSq_apply]
    simp
    ring
  simp [hnorm]

private lemma re_div_sub_I (a x t : ℝ) :
    (((a : ℂ) / ((x : ℂ) - Complex.I * (t : ℂ)))).re = a * x / (x ^ 2 + t ^ 2) := by
  rw [Complex.div_re]
  have hnorm : Complex.normSq ((x : ℂ) - Complex.I * (t : ℂ)) = x ^ 2 + t ^ 2 := by
    rw [Complex.normSq_apply]
    simp
    ring
  simp [hnorm]

private lemma termA_re (x K t : ℝ) :
    (Complex.exp (x * (K : ℂ)) / ((x : ℂ) + Complex.I * (t : ℂ))).re =
      Real.exp (x * K) * x / (x ^ 2 + t ^ 2) := by
  rw [exp_real_mul x K]
  exact re_div_add_I (Real.exp (x * K)) x t

private lemma termB_re (x K t : ℝ) :
    (Complex.exp (-(x * (K : ℂ))) / ((x : ℂ) - Complex.I * (t : ℂ))).re =
      Real.exp (-(x * K)) * x / (x ^ 2 + t ^ 2) := by
  rw [exp_real_mul_neg x K]
  exact re_div_sub_I (Real.exp (-(x * K))) x t

private lemma termC_re (x t K : ℝ) (hx : 0 < x) :
    (2 * (x : ℂ) * Complex.exp (-(Complex.I * (t : ℂ) * (K : ℂ))) /
        ((x : ℂ) ^ 2 - (Complex.I * (t : ℂ)) ^ 2)).re =
      (2 * x * Real.cos (t * K)) / (x ^ 2 + t ^ 2) := by
  rw [denom_sq x t]
  rw [Complex.div_re]
  have hzre : (2 * (x : ℂ) * Complex.exp (-(Complex.I * (t : ℂ) * (K : ℂ)))).re =
      2 * x * Real.cos (t * K) := by
    rw [Complex.mul_re]
    rw [exp_pure_im_re]
    simp
  rw [hzre]
  rw [Complex.ofReal_re]
  rw [Complex.ofReal_im]
  rw [Complex.normSq_ofReal]
  rw [mul_zero]
  have hS : x ^ 2 + t ^ 2 ≠ 0 := by
    have hx2 : 0 < x ^ 2 := sq_pos_of_pos hx
    nlinarith
  field_simp [hS]
  ring

/-- The real part of the closed Laplace form of `f₁(t) = sinh((K−t)·x)` at `z = i·t`. -/
private lemma laplace_re (x : ℝ) (hx : 0 < x) (K t : ℝ) :
    (((1 / 2 : ℂ) * (Complex.exp (x * (K : ℂ)) / ((x : ℂ) + Complex.I * (t : ℂ)) +
        Complex.exp (-(x * (K : ℂ))) / ((x : ℂ) - Complex.I * (t : ℂ)) -
        2 * (x : ℂ) * Complex.exp (-(Complex.I * (t : ℂ) * (K : ℂ))) /
          ((x : ℂ) ^ 2 - (Complex.I * (t : ℂ)) ^ 2)))).re =
      (x / 2) * (Real.exp (x * K) + Real.exp (-(x * K)) - 2 * Real.cos (t * K)) /
        (x ^ 2 + t ^ 2) := by
  rw [re_half]
  simp only [Complex.add_re, Complex.sub_re]
  rw [termA_re x K t, termB_re x K t, termC_re x t K hx]
  have hS : x ^ 2 + t ^ 2 ≠ 0 := by
    have hx2 : 0 < x ^ 2 := sq_pos_of_pos hx
    nlinarith
  field_simp [hS]

/-- Real part of `e^(−K·(x+i·t))`. -/
private lemma exp_neg_sum_re (K x t : ℝ) :
    (Complex.exp (-((K : ℂ) * ((x : ℂ) + Complex.I * (t : ℂ))))).re =
      Real.exp (-(x * K)) * Real.cos (t * K) := by
  rw [Complex.exp_re]
  simp
  rw [mul_comm K x, mul_comm K t]

/-- Imaginary part of `e^(−K·(x+i·t))`. -/
private lemma exp_neg_sum_im (K x t : ℝ) :
    (Complex.exp (-((K : ℂ) * ((x : ℂ) + Complex.I * (t : ℂ))))).im =
      -(Real.exp (-(x * K)) * Real.sin (t * K)) := by
  rw [Complex.exp_im]
  simp
  rw [mul_comm K x, mul_comm K t]

/-- `|1 − e^(−K·(x+i·t))|² = 1 − 2·e^(−xK)·cos(tK) + e^(−2xK)`. -/
private lemma normSq_num (K x t : ℝ) :
    Complex.normSq (1 - Complex.exp (-((K : ℂ) * ((x : ℂ) + Complex.I * (t : ℂ))))) =
      1 - 2 * Real.exp (-(x * K)) * Real.cos (t * K) + Real.exp (-(x * K)) ^ 2 := by
  have hre : (1 - Complex.exp (-((K : ℂ) * ((x : ℂ) + Complex.I * (t : ℂ))))).re =
      1 - Real.exp (-(x * K)) * Real.cos (t * K) := by
    simp [exp_neg_sum_re]
  have him : (1 - Complex.exp (-((K : ℂ) * ((x : ℂ) + Complex.I * (t : ℂ))))).im =
      Real.exp (-(x * K)) * Real.sin (t * K) := by
    simp [exp_neg_sum_im]
  rw [Complex.normSq_apply, hre, him]
  rw [← sq, ← sq]
  calc
    (1 - Real.exp (-(x * K)) * Real.cos (t * K)) ^ 2 +
        (Real.exp (-(x * K)) * Real.sin (t * K)) ^ 2
        = 1 - 2 * Real.exp (-(x * K)) * Real.cos (t * K) +
            Real.exp (-(x * K)) ^ 2 * (Real.cos (t * K) ^ 2 + Real.sin (t * K) ^ 2) := by ring
    _ = 1 - 2 * Real.exp (-(x * K)) * Real.cos (t * K) +
          Real.exp (-(x * K)) ^ 2 := by
          have htrig : Real.cos (t * K) ^ 2 + Real.sin (t * K) ^ 2 = 1 := by
            rw [add_comm, Real.sin_sq_add_cos_sq (t * K)]
          rw [htrig]
          ring

/-- `|(1 − e^(−K·(x+i·t)))/(x + i·t)|²`, expanded. -/
private lemma normSq_quot (K x t : ℝ) :
    ‖(1 - Complex.exp (-((K : ℂ) * ((x : ℂ) + Complex.I * (t : ℂ))))) /
        ((x : ℂ) + Complex.I * (t : ℂ))‖ ^ 2 =
      (1 - 2 * Real.exp (-(x * K)) * Real.cos (t * K) + Real.exp (-(x * K)) ^ 2) /
        (x ^ 2 + t ^ 2) := by
  rw [← Complex.normSq_eq_norm_sq]
  rw [map_div₀]
  rw [normSq_num]
  congr 1
  rw [Complex.normSq_apply]
  simp
  ring

private lemma exp_mul_exp_neg (x K : ℝ) : Real.exp (x * K) * Real.exp (-(x * K)) = 1 := by
  rw [← Real.exp_add]
  norm_num

private lemma exp_mul_exp_neg_sq (x K : ℝ) :
    Real.exp (x * K) * (Real.exp (-(x * K))) ^ 2 = Real.exp (-(x * K)) := by
  have hsq : (Real.exp (-(x * K))) ^ 2 = Real.exp (-(2 * (x * K))) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hsq, ← Real.exp_add]
  congr 1
  ring

private lemma exp_factor (x K t : ℝ) :
    Real.exp (x * K) * (1 - 2 * Real.exp (-(x * K)) * Real.cos (t * K) +
        Real.exp (-(x * K)) ^ 2) =
      Real.exp (x * K) + Real.exp (-(x * K)) - 2 * Real.cos (t * K) := by
  calc
    Real.exp (x * K) * (1 - 2 * Real.exp (-(x * K)) * Real.cos (t * K) +
          Real.exp (-(x * K)) ^ 2)
        = Real.exp (x * K) - 2 * (Real.exp (x * K) * Real.exp (-(x * K))) *
            Real.cos (t * K) + Real.exp (x * K) * (Real.exp (-(x * K)) ^ 2) := by ring
    _ = Real.exp (x * K) - 2 * Real.cos (t * K) + Real.exp (-(x * K)) := by
          rw [exp_mul_exp_neg x K, exp_mul_exp_neg_sq x K]
          ring
    _ = Real.exp (x * K) + Real.exp (-(x * K)) - 2 * Real.cos (t * K) := by ring

theorem tentF1_boundary {K : ℝ} (hK : 0 < K) (x : ℝ) (hx : 0 < x) (t : ℝ) :
    (∫ u in (0 : ℝ)..(K : ℝ),
        Complex.exp (-((Complex.I * (t : ℂ)) * (u : ℂ))) *
          ((Real.sinh ((K - u) * x) : ℝ) : ℂ)).re =
      (x / 2) * Real.exp (x * K) *
        ‖(1 - Complex.exp (-((K : ℂ) * ((x : ℂ) + Complex.I * (t : ℂ))))) /
            ((x : ℂ) + Complex.I * (t : ℂ))‖ ^ 2 := by
  let z : ℂ := Complex.I * (t : ℂ)
  have hz1 : z ≠ (x : ℂ) := by
    dsimp [z]
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hz2 : z ≠ -(x : ℂ) := by
    dsimp [z]
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hI := tentF1_laplace hK x hx z hz1 hz2
  dsimp [z] at hI
  rw [hI]
  rw [laplace_re x hx K t]
  rw [normSq_quot K x t]
  rw [show (x / 2) * Real.exp (x * K) *
        ((1 - 2 * Real.exp (-(x * K)) * Real.cos (t * K) + Real.exp (-(x * K)) ^ 2) /
          (x ^ 2 + t ^ 2)) =
      (x / 2) * (Real.exp (x * K) * (1 - 2 * Real.exp (-(x * K)) * Real.cos (t * K) +
        Real.exp (-(x * K)) ^ 2)) / (x ^ 2 + t ^ 2) by ring]
  rw [exp_factor x K t]

end Commons.NumberTheory.Linnik