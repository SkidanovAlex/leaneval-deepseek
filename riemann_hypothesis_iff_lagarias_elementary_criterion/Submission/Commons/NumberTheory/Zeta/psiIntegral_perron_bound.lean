import Mathlib
import Submission.Commons.Analysis.Perron.riesz_perron_bound_pos
import Submission.Commons.NumberTheory.Chebyshev.psi_integral_eq_sum
import Submission.Commons.NumberTheory.Zeta.summable_vonMangoldt_div_rpow
import Submission.Commons.NumberTheory.Zeta.vonMangoldt_rpow_five_fourths_tsum_le

open Complex MeasureTheory intervalIntegral Filter
open scoped Topology BigOperators

noncomputable section

namespace Commons.NumberTheory.Zeta

/-- The Dirichlet series of `Λ` at `s = 2 + it` equals the (negated) logarithmic derivative
of `ζ`, in the exact `tsum` form used by the Riesz–Perron expansion. -/
lemma tsum_vonMangoldt_eq_neg_logDeriv (y : ℝ) :
    (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        (n : ℂ) ^ (-(((2 : ℂ) + (y : ℂ) * Complex.I)))) =
      -(deriv riemannZeta ((2 : ℂ) + (y : ℂ) * Complex.I)) /
        riemannZeta ((2 : ℂ) + (y : ℂ) * Complex.I) := by
  have hs : 1 < (((2 : ℂ) + (y : ℂ) * Complex.I)).re := by
    simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
  have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
    (s := ((2 : ℂ) + (y : ℂ) * Complex.I)) hs
  have hf : (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) 0 = 0 := by simp
  rw [← hL]
  rw [LSeries]
  apply tsum_congr
  intro n
  rw [LSeries.term_def₀ hf]

/-- The pointwise equality of the two integrands: replacing `-ζ'/ζ` by its Dirichlet series. -/
lemma perronIntegrand_eq (X y : ℝ) :
    (-(deriv riemannZeta ((2:ℂ)+Complex.I*(y:ℂ)))/riemannZeta ((2:ℂ)+Complex.I*(y:ℂ)))
      * (X:ℂ)^((2:ℂ)+Complex.I*(y:ℂ)+1) / (((2:ℂ)+Complex.I*(y:ℂ))*((2:ℂ)+Complex.I*(y:ℂ)+1))
    = (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (n:ℂ)^(-((2:ℂ)+(y:ℂ)*Complex.I)))
        * (X:ℂ)^((2:ℂ)+(y:ℂ)*Complex.I+1)
        / (((2:ℂ)+(y:ℂ)*Complex.I) * (((2+1:ℝ):ℂ)+(y:ℂ)*Complex.I)) := by
  have e1 : ((2:ℂ)+Complex.I*(y:ℂ)) = ((2:ℂ)+(y:ℂ)*Complex.I) := by ring
  have e2 : ((2:ℂ)+Complex.I*(y:ℂ)+1) = ((2:ℂ)+(y:ℂ)*Complex.I+1) := by ring
  have e4 : (((2+1:ℝ):ℂ)+(y:ℂ)*Complex.I) = ((2:ℂ)+(y:ℂ)*Complex.I+1) := by push_cast; ring
  rw [e2, e1, e4, ← tsum_vonMangoldt_eq_neg_logDeriv y]

/-- The von Mangoldt series at `2` is at most `27`
(it is dominated termwise by the series at `5/4`, bounded by `27`). -/
lemma vonMangoldt_div_sq_tsum_le :
    (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ (2:ℝ)) ≤ 27 := by
  have h2 : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) / (n:ℝ)^(2:ℝ)) :=
    summable_vonMangoldt_div_rpow (by norm_num)
  have h54 : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) / (n:ℝ)^((5:ℝ)/4)) :=
    summable_vonMangoldt_div_rpow (by norm_num)
  refine le_trans (Summable.tsum_le_tsum (fun n => ?_) h2 h54)
    vonMangoldt_rpow_five_fourths_tsum_le
  by_cases hn : n = 0
  · subst hn; simp
  · have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hle : (n:ℝ) ^ ((5:ℝ)/4) ≤ (n:ℝ) ^ (2:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
    exact div_le_div_of_nonneg_left (ArithmeticFunction.vonMangoldt_nonneg)
      (Real.rpow_pos_of_pos hnpos _) hle

theorem psiIntegral_perron_bound (X : ℝ) (hX : 1 ≤ X) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      ‖(∫ t in (0 : ℝ)..X, (Chebyshev.psi t : ℂ)) -
        (1 / (2 * Real.pi)) * (∫ y in -T..T,
          (-(deriv riemannZeta ((2 : ℂ) + Complex.I * (y : ℂ))) /
            riemannZeta ((2 : ℂ) + Complex.I * (y : ℂ)))
          * (X : ℂ) ^ ((2 : ℂ) + Complex.I * (y : ℂ) + 1)
          / (((2 : ℂ) + Complex.I * (y : ℂ)) *
              ((2 : ℂ) + Complex.I * (y : ℂ) + 1)))‖
        ≤ C * X * (Real.log (X + T + 2)) ^ 3 / T := by
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hlog4 : 0 < Real.log (X + 4) := Real.log_pos (by linarith)
  have hsum2 : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) / (n:ℝ)^(2:ℝ)) :=
    summable_vonMangoldt_div_rpow (by norm_num)
  have hK := vonMangoldt_div_sq_tsum_le
  refine ⟨X ^ ((2:ℝ)+1) * 27 / (X * (Real.log (X+4))^3) + 1, ?_, ?_⟩
  · have h1 : 0 < X ^ ((2:ℝ)+1) := Real.rpow_pos_of_pos hX0 _
    have h2 : 0 < (Real.log (X+4))^3 := pow_pos hlog4 3
    have h3 : 0 < X * (Real.log (X+4))^3 := mul_pos hX0 h2
    have h4 : 0 < X ^ ((2:ℝ)+1) * 27 / (X * (Real.log (X+4))^3) :=
      div_pos (mul_pos h1 (by norm_num)) h3
    linarith
  intro T hT
  have hTpos : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  -- the integrated `ψ` identity
  have hpsi : (∫ t in (0 : ℝ)..X, (Chebyshev.psi t : ℂ))
      = ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (((X - (n : ℝ)) : ℝ) : ℂ) :=
    Commons.NumberTheory.Chebyshev.psi_integral_eq_sum X hX0.le
  -- rewrite the target integral into the Riesz–Perron shape
  have hint : (∫ y in -T..T,
          (-(deriv riemannZeta ((2 : ℂ) + Complex.I * (y : ℂ))) /
            riemannZeta ((2 : ℂ) + Complex.I * (y : ℂ)))
          * (X : ℂ) ^ ((2 : ℂ) + Complex.I * (y : ℂ) + 1)
          / (((2 : ℂ) + Complex.I * (y : ℂ)) *
              ((2 : ℂ) + Complex.I * (y : ℂ) + 1)))
      = (∫ y in -T..T,
          (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            (n:ℂ)^(-((2:ℂ)+(y:ℂ)*Complex.I)))
          * (X:ℂ)^((2:ℂ)+(y:ℂ)*Complex.I+1)
          / (((2:ℂ)+(y:ℂ)*Complex.I) * (((2+1:ℝ):ℂ)+(y:ℂ)*Complex.I))) := by
    apply intervalIntegral.integral_congr
    intro y _
    exact perronIntegrand_eq X y
  have hrz := Commons.Analysis.Perron.riesz_perron_bound_pos
    (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ))
    (fun n => ArithmeticFunction.vonMangoldt_nonneg) 2 X T (by norm_num) hX0 hT1 hsum2
  have hmain : ‖(∫ t in (0 : ℝ)..X, (Chebyshev.psi t : ℂ)) -
        (1 / (2 * Real.pi)) * (∫ y in -T..T,
          (-(deriv riemannZeta ((2 : ℂ) + Complex.I * (y : ℂ))) /
            riemannZeta ((2 : ℂ) + Complex.I * (y : ℂ)))
          * (X : ℂ) ^ ((2 : ℂ) + Complex.I * (y : ℂ) + 1)
          / (((2 : ℂ) + Complex.I * (y : ℂ)) *
              ((2 : ℂ) + Complex.I * (y : ℂ) + 1)))‖ ≤
        X ^ ((2:ℝ)+1) * 27 / T := by
    rw [hpsi, hint]
    refine le_trans hrz ?_
    calc X ^ ((2:ℝ)+1) / T * (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / (n:ℝ)^(2:ℝ))
        ≤ X ^ ((2:ℝ)+1) / T * 27 := mul_le_mul_of_nonneg_left hK (by positivity)
      _ = X ^ ((2:ℝ)+1) * 27 / T := by ring
  refine le_trans hmain ?_
  have hl4pos : 0 < (Real.log (X+4))^3 := pow_pos hlog4 3
  have hlge : (Real.log (X+4))^3 ≤ (Real.log (X+T+2))^3 :=
    pow_le_pow_left₀ hlog4.le (Real.log_le_log (by linarith) (by linarith)) 3
  have hfin : X ^ ((2:ℝ)+1) * 27 ≤
      (X ^ ((2:ℝ)+1) * 27 / (X * (Real.log (X+4))^3) + 1) * X * (Real.log (X+T+2))^3 := by
    have hratio : 1 ≤ (Real.log (X+T+2))^3 / (Real.log (X+4))^3 := by
      rw [one_le_div hl4pos]; exact hlge
    have h1 : X ^ ((2:ℝ)+1) * 27 ≤
        X ^ ((2:ℝ)+1) * 27 * ((Real.log (X+T+2))^3/(Real.log (X+4))^3) := by
      have hXp : (0:ℝ) ≤ X ^ ((2:ℝ)+1) := le_of_lt (Real.rpow_pos_of_pos hX0 ((2:ℝ)+1))
      have := mul_le_mul_of_nonneg_left hratio (mul_nonneg hXp (by norm_num : (0:ℝ) ≤ 27))
      simpa using this
    have h2 : (X ^ ((2:ℝ)+1) * 27 / (X * (Real.log (X+4))^3) + 1) * X * (Real.log (X+T+2))^3
        = X ^ ((2:ℝ)+1) * 27 * ((Real.log (X+T+2))^3/(Real.log (X+4))^3)
          + X*(Real.log (X+T+2))^3 := by
      field_simp
    have h3 : 0 ≤ X*(Real.log (X+T+2))^3 :=
      mul_nonneg hX0.le (pow_nonneg (Real.log_nonneg (by linarith)) 3)
    linarith [h1, h3, h2]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hfin (inv_nonneg.mpr hTpos.le)

end Commons.NumberTheory.Zeta
