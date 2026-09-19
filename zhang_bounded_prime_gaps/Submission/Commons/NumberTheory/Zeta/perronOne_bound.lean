import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section

open scoped Real

namespace Commons.NumberTheory.Zeta

/-! # The Perron step at z = 1 stays bounded for all truncations T
Claim: for 0 < σ and 0 ≤ T,
    ‖(1/(2π)) ∫_{-T}^{T} 1/(σ + it) dt‖ ≤ 1/2.
PROOF IDEA: 1/(σ + it) = (σ - it)/(σ^2 + t^2); the imaginary part integrates to 0 (odd),
the real part gives 2·∫₀ᵀ σ/(σ²+t²) dt = 2·arctan(T/σ), so the whole integral equals
2·arctan(T/σ) (a real number), and |2 arctan(T/σ)|/(2π) ≤ (2·(π/2))/(2π) = 1/2.
Formally: use intervalIntegral.integral_congr to rewrite the integrand, split real and
imaginary parts (Complex.ext), use intervalIntegral.integral_deriv_eq_sub with the derivative
of (fun t => Real.arctan (t/σ)) being σ/(σ²+t²) (Mathlib has deriv_arctan / hasDerivAt_arctan),
and the odd-function integral ∫_{-T}^{T} t/(σ²+t²) dt = 0 (by integral_comp_neg or symmetry).
Noncomputable, no imports beyond Mathlib. -/

/-- Real part of `1 / (σ + I * t)`. -/
private lemma integrand_re (σ : ℝ) (t : ℝ) :
    ((1 : ℂ) / (((σ : ℂ) + Complex.I * (t : ℂ)))).re = σ / (σ ^ 2 + t ^ 2) := by
  have hnorm : Complex.normSq ((σ : ℂ) + Complex.I * (t : ℂ)) = σ ^ 2 + t ^ 2 := by
    rw [Complex.normSq_apply]
    simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  rw [Complex.div_re]
  simp [Complex.one_re, Complex.one_im, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, hnorm]

/-- `conj (1/(σ + I t)) = 1/(σ - I t) = f(-t)`. -/
private lemma conj_integrand (σ t : ℝ) :
    (starRingEnd ℂ) ((1 : ℂ) / (((σ : ℂ) + Complex.I * (t : ℂ)))) =
      (1 : ℂ) / (((σ : ℂ) + Complex.I * (-(t : ℂ)))) := by
  simp [Complex.conj_ofReal, Complex.conj_I, map_add, map_mul]

/-- derivative of `t ↦ arctan(t/σ)`. -/
private lemma hasDerivAt_arctan_div (σ : ℝ) (hσ : 0 < σ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => Real.arctan (t / σ)) (σ / (σ ^ 2 + x ^ 2)) x := by
  have hder : HasDerivAt (fun t : ℝ => Real.arctan (t / σ))
      (1 / (1 + (x / σ) ^ 2) * (1 / σ)) x := by
    exact (Real.hasDerivAt_arctan (x / σ)).comp x ((hasDerivAt_id x).div_const σ)
  have hval : 1 / (1 + (x / σ) ^ 2) * (1 / σ) = σ / (σ ^ 2 + x ^ 2) := by
    field_simp [ne_of_gt hσ]
  rw [← hval]
  exact hder

private lemma cont_r (σ : ℝ) (hσ : 0 < σ) : Continuous (fun t : ℝ => σ / (σ ^ 2 + t ^ 2)) := by
  apply Continuous.div
  · exact continuous_const
  · fun_prop
  · intro t ht
    nlinarith [sq_pos_of_ne_zero (ne_of_gt hσ)]

/-- continuity of the complex integrand `t ↦ 1/(σ + I t)`. -/
private lemma cont_f (σ : ℝ) (hσ : 0 < σ) :
    Continuous (fun t : ℝ => (1 : ℂ) / (((σ : ℂ) + Complex.I * (t : ℂ)))) := by
  refine Continuous.div₀ ?_ ?_ ?_
  · exact continuous_const
  · fun_prop
  · intro t ht
    have hre := congrArg Complex.re ht
    simp at hre
    linarith

/-- `∫_{-T}^{T} σ/(σ²+t²) = 2 arctan(T/σ)`. -/
private lemma symm_integral_r (σ T : ℝ) (hσ : 0 < σ) :
    (∫ t in -T..T, σ / (σ ^ 2 + t ^ 2)) = 2 * Real.arctan (T / σ) := by
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ => Real.arctan (t / σ))
      (f' := fun t : ℝ => σ / (σ ^ 2 + t ^ 2))
      (a := -T) (b := T)
      (hderiv := fun x hx => hasDerivAt_arctan_div σ hσ x)
      (hint := (cont_r σ hσ).intervalIntegrable (-T) T)
  rw [hftc]
  rw [neg_div, Real.arctan_neg]
  ring

theorem perronOne_bound (σ T : ℝ) (hσ : 0 < σ) (hT : 0 ≤ T) :
    ‖(1 / (2 * Real.pi)) * (∫ (t : ℝ) in -T..T,
        (1 : ℂ) / (((σ : ℂ) + Complex.I * (t : ℂ))))‖ ≤ 1 / 2 := by
  have hf_int : IntervalIntegrable (fun t : ℝ => (1 : ℂ) / (((σ : ℂ) + Complex.I * (t : ℂ))))
      MeasureTheory.volume (-T) T := by
    apply Continuous.intervalIntegrable
    exact cont_f σ hσ
  -- the integral equals `(2 * arctan (T/σ) : ℂ)` (a real number)
  have hJ : (∫ (t : ℝ) in -T..T, (1 : ℂ) / (((σ : ℂ) + Complex.I * (t : ℂ)))) =
      ((2 * Real.arctan (T / σ) : ℝ) : ℂ) := by
    apply Complex.ext
    · -- real part: `re (∫ f) = ∫ re f = 2 arctan(T/σ)`
      calc
        (∫ (t : ℝ) in -T..T, (1 : ℂ) / (((σ : ℂ) + Complex.I * (t : ℂ)))).re =
            ∫ (t : ℝ) in -T..T,
              RCLike.re ((1 : ℂ) / (((σ : ℂ) + Complex.I * (t : ℂ)))) :=
          (intervalIntegral.intervalIntegral_re hf_int).symm
        _ = ∫ (t : ℝ) in -T..T, σ / (σ ^ 2 + t ^ 2) := by
          apply intervalIntegral.integral_congr
          intro t ht
          exact integrand_re σ t
        _ = 2 * Real.arctan (T / σ) := symm_integral_r σ T hσ
        _ = (((2 * Real.arctan (T / σ) : ℝ) : ℂ)).re := by
          rw [Complex.ofReal_re]
    · -- imaginary part: the conjugate equals itself, so it vanishes
      have hconj : (starRingEnd ℂ) (∫ (t : ℝ) in -T..T,
          (1 : ℂ) / (((σ : ℂ) + Complex.I * (t : ℂ)))) =
          (∫ (t : ℝ) in -T..T, (1 : ℂ) / (((σ : ℂ) + Complex.I * (t : ℂ)))) := by
        calc
          (starRingEnd ℂ) (∫ (t : ℝ) in -T..T, (1 : ℂ) / (((σ : ℂ) + Complex.I * (t : ℂ)))) =
              ∫ (t : ℝ) in -T..T, (starRingEnd ℂ) ((1 : ℂ) / (((σ : ℂ) + Complex.I * (t : ℂ)))) := by
            rw [intervalIntegral.intervalIntegral_conj]
          _ = ∫ (t : ℝ) in -T..T, (1 : ℂ) / (((σ : ℂ) + Complex.I * (-(t : ℂ)))) := by
            apply intervalIntegral.integral_congr
            intro t ht
            exact conj_integrand σ t
          _ = ∫ (t : ℝ) in -T..T, (1 : ℂ) / (((σ : ℂ) + Complex.I * (t : ℂ))) := by
            simpa using (intervalIntegral.integral_comp_neg (a := -T) (b := T)
              (f := fun t : ℝ => (1 : ℂ) / (((σ : ℂ) + Complex.I * (t : ℂ)))))
      have him : (∫ (t : ℝ) in -T..T, (1 : ℂ) / (((σ : ℂ) + Complex.I * (t : ℂ)))).im = 0 :=
        (Complex.conj_eq_iff_im).1 hconj
      rw [him, Complex.ofReal_im]
  rw [hJ]
  -- now bound ‖↑(1/(2π)) * ↑(2 arctan(T/σ))‖ ; first rewrite the ℂ-coerced scalar
  have hscalar : (1 : ℂ) / (2 * (Real.pi : ℂ)) = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by
    rw [Complex.ofReal_div]
    norm_num [Complex.ofReal_mul]
  rw [hscalar]
  rw [← Complex.ofReal_mul]
  rw [Complex.norm_real]
  simp only [Real.norm_eq_abs]
  have hprod : (1 / (2 * Real.pi)) * (2 * Real.arctan (T / σ)) =
      Real.arctan (T / σ) / Real.pi := by
    field_simp [Real.pi_ne_zero]
  rw [hprod]
  have hTσ : 0 ≤ T / σ := div_nonneg hT (le_of_lt hσ)
  have har0 : 0 ≤ Real.arctan (T / σ) := (Real.arctan_nonneg).2 hTσ
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [abs_of_nonneg (div_nonneg har0 (le_of_lt hpi))]
  rw [div_le_iff₀ hpi]
  have harp : Real.arctan (T / σ) < Real.pi / 2 := Real.arctan_lt_pi_div_two (T / σ)
  nlinarith

end Commons.NumberTheory.Zeta