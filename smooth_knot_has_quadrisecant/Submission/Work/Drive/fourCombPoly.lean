import Mathlib
import Submission.Work.Drive.fourCombDefs

/-!
# The polynomial model of the degree-`≤ 4` trigonometric family, part 2

Evaluation and derivation identities for `fcPoly` / `fcGamma`
(`Submission.Work.Drive.fourCombDefs`), and the injectivity of `fcGamma`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 800000

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

noncomputable section

/-- `(2 * I)⁻¹ = -I / 2`. -/
lemma fc_inv_two_I : ((2 : ℂ) * Complex.I)⁻¹ = -(Complex.I) / 2 := by
  have h : (2 : ℂ) * Complex.I ≠ 0 := by
    simp [Complex.I_ne_zero]
  field_simp
  rw [pow_two, Complex.I_mul_I]
  ring

/-! ## de Moivre in the forms used below -/

lemma fc_jetExp_pow_eq (t : ℝ) (k : ℕ) :
    (jetExp t) ^ k
      = (Real.cos ((k : ℝ) * t) : ℂ) + (Real.sin ((k : ℝ) * t) : ℂ) * Complex.I := by
  simpa using jetExp_zpow t (k : ℤ)

lemma fc_jetExp_pow_inv_eq (t : ℝ) (k : ℕ) :
    ((jetExp t) ^ k)⁻¹
      = (Real.cos ((k : ℝ) * t) : ℂ) - (Real.sin ((k : ℝ) * t) : ℂ) * Complex.I := by
  have h := jetExp_zpow t (-(k : ℤ))
  rw [zpow_neg, zpow_natCast] at h
  rw [h]
  have hc : ((-(k : ℤ) : ℤ) : ℝ) = -(k : ℝ) := by push_cast; ring
  rw [hc, neg_mul, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

lemma fc_cos_eq_pow (t : ℝ) (k : ℕ) :
    (Real.cos ((k : ℝ) * t) : ℂ) = ((jetExp t) ^ k + ((jetExp t) ^ k)⁻¹) / 2 := by
  have h : (jetExp t) ^ k + ((jetExp t) ^ k)⁻¹ = 2 * (Real.cos ((k : ℝ) * t) : ℂ) := by
    rw [fc_jetExp_pow_inv_eq, fc_jetExp_pow_eq]
    ring
  rw [eq_div_iff (by norm_num : (2 : ℂ) ≠ 0), mul_comm]
  exact h.symm

lemma fc_sin_eq_pow (t : ℝ) (k : ℕ) :
    (Real.sin ((k : ℝ) * t) : ℂ) = ((jetExp t) ^ k - ((jetExp t) ^ k)⁻¹) / (2 * Complex.I) := by
  have h : (jetExp t) ^ k - ((jetExp t) ^ k)⁻¹
      = 2 * Complex.I * (Real.sin ((k : ℝ) * t) : ℂ) := by
    rw [fc_jetExp_pow_inv_eq, fc_jetExp_pow_eq]
    ring
  rw [eq_div_iff (by simp [Complex.I_ne_zero] : (2 * Complex.I : ℂ) ≠ 0), mul_comm]
  exact h.symm

/-! ## The evaluation identity -/

theorem fcPoly_eval (j : Fin 9) (t : ℝ) :
    (fcPoly j).eval (jetExp t) = (jetExp t) ^ 4 * (trigBasis j t : ℂ) := by
  have hz : jetExp t ≠ 0 := jetExp_ne_zero t
  fin_cases j
  · show (fcPoly 0).eval (jetExp t) = (jetExp t) ^ 4 * (trigBasis 0 t : ℂ)
    simp only [fcPoly, trigBasis, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
      Complex.ofReal_one]
    ring
  · show (fcPoly 1).eval (jetExp t) = (jetExp t) ^ 4 * (trigBasis 1 t : ℂ)
    simp only [fcPoly, trigBasis, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one]
    have h : (Real.cos t : ℂ) = ((jetExp t) + (jetExp t)⁻¹) / 2 := by
      simpa using fc_cos_eq_pow t 1
    rw [h]
    field_simp <;> simp [pow_two, Complex.I_mul_I] <;> ring
  · show (fcPoly 2).eval (jetExp t) = (jetExp t) ^ 4 * (trigBasis 2 t : ℂ)
    simp only [fcPoly, trigBasis, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one]
    have h2 : (Real.sin t : ℂ) = ((jetExp t) - (jetExp t)⁻¹) / (2 * Complex.I) := by
      simpa using fc_sin_eq_pow t 1
    rw [h2]
    field_simp <;> simp [pow_two, Complex.I_mul_I] <;> ring
  · show (fcPoly 3).eval (jetExp t) = (jetExp t) ^ 4 * (trigBasis 3 t : ℂ)
    simp only [fcPoly, trigBasis, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one]
    have h : (Real.cos (2 * t) : ℂ) = ((jetExp t) ^ 2 + ((jetExp t) ^ 2)⁻¹) / 2 := by
      simpa using fc_cos_eq_pow t 2
    rw [h]
    field_simp <;> simp [pow_two, Complex.I_mul_I] <;> ring
  · show (fcPoly 4).eval (jetExp t) = (jetExp t) ^ 4 * (trigBasis 4 t : ℂ)
    simp only [fcPoly, trigBasis, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one]
    have h2 : (Real.sin (2 * t) : ℂ) = ((jetExp t) ^ 2 - ((jetExp t) ^ 2)⁻¹) / (2 * Complex.I) := by
      simpa using fc_sin_eq_pow t 2
    rw [h2]
    field_simp <;> simp [pow_two, Complex.I_mul_I] <;> ring
  · show (fcPoly 5).eval (jetExp t) = (jetExp t) ^ 4 * (trigBasis 5 t : ℂ)
    simp only [fcPoly, trigBasis, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one]
    have h : (Real.cos (3 * t) : ℂ) = ((jetExp t) ^ 3 + ((jetExp t) ^ 3)⁻¹) / 2 := by
      simpa using fc_cos_eq_pow t 3
    rw [h]
    field_simp <;> simp [pow_two, Complex.I_mul_I] <;> ring
  · show (fcPoly 6).eval (jetExp t) = (jetExp t) ^ 4 * (trigBasis 6 t : ℂ)
    simp only [fcPoly, trigBasis, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one]
    have h2 : (Real.sin (3 * t) : ℂ) = ((jetExp t) ^ 3 - ((jetExp t) ^ 3)⁻¹) / (2 * Complex.I) := by
      simpa using fc_sin_eq_pow t 3
    rw [h2]
    field_simp <;> simp [pow_two, Complex.I_mul_I] <;> ring
  · show (fcPoly 7).eval (jetExp t) = (jetExp t) ^ 4 * (trigBasis 7 t : ℂ)
    simp only [fcPoly, trigBasis, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one]
    have h : (Real.cos (4 * t) : ℂ) = ((jetExp t) ^ 4 + ((jetExp t) ^ 4)⁻¹) / 2 := by
      simpa using fc_cos_eq_pow t 4
    rw [h]
    field_simp <;> simp [pow_two, Complex.I_mul_I] <;> ring
  · show (fcPoly 8).eval (jetExp t) = (jetExp t) ^ 4 * (trigBasis 8 t : ℂ)
    simp only [fcPoly, trigBasis, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one]
    have h2 : (Real.sin (4 * t) : ℂ) = ((jetExp t) ^ 4 - ((jetExp t) ^ 4)⁻¹) / (2 * Complex.I) := by
      simpa using fc_sin_eq_pow t 4
    rw [h2]
    field_simp <;> simp [pow_two, Complex.I_mul_I] <;> ring

theorem fcPoly_derivative_eval (j : Fin 9) (t : ℝ) :
    (fcPoly j).derivative.eval (jetExp t)
      = (jetExp t) ^ 3 * (4 * (trigBasis j t : ℂ) - Complex.I * (trigBasisD j t : ℂ)) := by
  have hz : jetExp t ≠ 0 := jetExp_ne_zero t
  fin_cases j
  · show (fcPoly 0).derivative.eval (jetExp t)
      = (jetExp t) ^ 3 * (4 * (trigBasis 0 t : ℂ) - Complex.I * (trigBasisD 0 t : ℂ))
    simp only [fcPoly, trigBasis, trigBasisD, Polynomial.derivative_C_mul,
      Polynomial.derivative_pow, Polynomial.derivative_X, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one, Complex.ofReal_one,
      Complex.ofReal_zero, Polynomial.C_1]
    ring
  · show (fcPoly 1).derivative.eval (jetExp t)
      = (jetExp t) ^ 3 * (4 * (trigBasis 1 t : ℂ) - Complex.I * (trigBasisD 1 t : ℂ))
    simp only [fcPoly, trigBasis, trigBasisD, Polynomial.derivative_C_mul, Polynomial.derivative_add, Polynomial.derivative_sub,
      Polynomial.derivative_pow, Polynomial.derivative_X, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.eval_one, Polynomial.derivative_one, neg_mul, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_ofNat,
      Complex.ofReal_natCast, Complex.ofReal_one, Complex.ofReal_zero, pow_two,
      Complex.I_mul_I, Polynomial.C_1]
    have h : (Real.cos t : ℂ) = ((jetExp t) + (jetExp t)⁻¹) / 2 := by
      simpa using fc_cos_eq_pow t 1
    have h2 : (Real.sin t : ℂ) = ((jetExp t) - (jetExp t)⁻¹) / (2 * Complex.I) := by
      simpa using fc_sin_eq_pow t 1
    rw [h, h2]
    field_simp <;> simp [pow_two, Complex.I_mul_I] <;> ring
  · show (fcPoly 2).derivative.eval (jetExp t)
      = (jetExp t) ^ 3 * (4 * (trigBasis 2 t : ℂ) - Complex.I * (trigBasisD 2 t : ℂ))
    simp only [fcPoly, trigBasis, trigBasisD, Polynomial.derivative_C_mul, Polynomial.derivative_add, Polynomial.derivative_sub,
      Polynomial.derivative_pow, Polynomial.derivative_X, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.eval_one, Polynomial.derivative_one, neg_mul, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_ofNat,
      Complex.ofReal_natCast, Complex.ofReal_one, Complex.ofReal_zero, pow_two,
      Complex.I_mul_I, Polynomial.C_1]
    have h : (Real.cos t : ℂ) = ((jetExp t) + (jetExp t)⁻¹) / 2 := by
      simpa using fc_cos_eq_pow t 1
    have h2 : (Real.sin t : ℂ) = ((jetExp t) - (jetExp t)⁻¹) / (2 * Complex.I) := by
      simpa using fc_sin_eq_pow t 1
    rw [h, h2]
    field_simp <;> simp [pow_two, Complex.I_mul_I] <;> ring
  · show (fcPoly 3).derivative.eval (jetExp t)
      = (jetExp t) ^ 3 * (4 * (trigBasis 3 t : ℂ) - Complex.I * (trigBasisD 3 t : ℂ))
    simp only [fcPoly, trigBasis, trigBasisD, Polynomial.derivative_C_mul, Polynomial.derivative_add, Polynomial.derivative_sub,
      Polynomial.derivative_pow, Polynomial.derivative_X, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.eval_one, Polynomial.derivative_one, neg_mul, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_ofNat,
      Complex.ofReal_natCast, Complex.ofReal_one, Complex.ofReal_zero, pow_two,
      Complex.I_mul_I, Polynomial.C_1]
    have h : (Real.cos (2 * t) : ℂ) = ((jetExp t) ^ 2 + ((jetExp t) ^ 2)⁻¹) / 2 := by
      simpa using fc_cos_eq_pow t 2
    have h2 : (Real.sin (2 * t) : ℂ) = ((jetExp t) ^ 2 - ((jetExp t) ^ 2)⁻¹) / (2 * Complex.I) := by
      simpa using fc_sin_eq_pow t 2
    rw [h, h2]
    field_simp <;> simp [pow_two, Complex.I_mul_I] <;> ring
  · show (fcPoly 4).derivative.eval (jetExp t)
      = (jetExp t) ^ 3 * (4 * (trigBasis 4 t : ℂ) - Complex.I * (trigBasisD 4 t : ℂ))
    simp only [fcPoly, trigBasis, trigBasisD, Polynomial.derivative_C_mul, Polynomial.derivative_add, Polynomial.derivative_sub,
      Polynomial.derivative_pow, Polynomial.derivative_X, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.eval_one, Polynomial.derivative_one, neg_mul, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_ofNat,
      Complex.ofReal_natCast, Complex.ofReal_one, Complex.ofReal_zero, pow_two,
      Complex.I_mul_I, Polynomial.C_1]
    have h : (Real.cos (2 * t) : ℂ) = ((jetExp t) ^ 2 + ((jetExp t) ^ 2)⁻¹) / 2 := by
      simpa using fc_cos_eq_pow t 2
    have h2 : (Real.sin (2 * t) : ℂ) = ((jetExp t) ^ 2 - ((jetExp t) ^ 2)⁻¹) / (2 * Complex.I) := by
      simpa using fc_sin_eq_pow t 2
    rw [h, h2]
    field_simp <;> simp [pow_two, Complex.I_mul_I] <;> ring
  · show (fcPoly 5).derivative.eval (jetExp t)
      = (jetExp t) ^ 3 * (4 * (trigBasis 5 t : ℂ) - Complex.I * (trigBasisD 5 t : ℂ))
    simp only [fcPoly, trigBasis, trigBasisD, Polynomial.derivative_C_mul, Polynomial.derivative_add, Polynomial.derivative_sub,
      Polynomial.derivative_pow, Polynomial.derivative_X, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.eval_one, Polynomial.derivative_one, neg_mul, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_ofNat,
      Complex.ofReal_natCast, Complex.ofReal_one, Complex.ofReal_zero, pow_two,
      Complex.I_mul_I, Polynomial.C_1]
    have h : (Real.cos (3 * t) : ℂ) = ((jetExp t) ^ 3 + ((jetExp t) ^ 3)⁻¹) / 2 := by
      simpa using fc_cos_eq_pow t 3
    have h2 : (Real.sin (3 * t) : ℂ) = ((jetExp t) ^ 3 - ((jetExp t) ^ 3)⁻¹) / (2 * Complex.I) := by
      simpa using fc_sin_eq_pow t 3
    rw [h, h2]
    field_simp <;> simp [pow_two, Complex.I_mul_I] <;> ring
  · show (fcPoly 6).derivative.eval (jetExp t)
      = (jetExp t) ^ 3 * (4 * (trigBasis 6 t : ℂ) - Complex.I * (trigBasisD 6 t : ℂ))
    simp only [fcPoly, trigBasis, trigBasisD, Polynomial.derivative_C_mul, Polynomial.derivative_add, Polynomial.derivative_sub,
      Polynomial.derivative_pow, Polynomial.derivative_X, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.eval_one, Polynomial.derivative_one, neg_mul, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_ofNat,
      Complex.ofReal_natCast, Complex.ofReal_one, Complex.ofReal_zero, pow_two,
      Complex.I_mul_I, Polynomial.C_1]
    have h : (Real.cos (3 * t) : ℂ) = ((jetExp t) ^ 3 + ((jetExp t) ^ 3)⁻¹) / 2 := by
      simpa using fc_cos_eq_pow t 3
    have h2 : (Real.sin (3 * t) : ℂ) = ((jetExp t) ^ 3 - ((jetExp t) ^ 3)⁻¹) / (2 * Complex.I) := by
      simpa using fc_sin_eq_pow t 3
    rw [h, h2]
    field_simp <;> simp [pow_two, Complex.I_mul_I] <;> ring
  · show (fcPoly 7).derivative.eval (jetExp t)
      = (jetExp t) ^ 3 * (4 * (trigBasis 7 t : ℂ) - Complex.I * (trigBasisD 7 t : ℂ))
    simp only [fcPoly, trigBasis, trigBasisD, Polynomial.derivative_C_mul, Polynomial.derivative_add, Polynomial.derivative_sub,
      Polynomial.derivative_pow, Polynomial.derivative_X, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.eval_one, Polynomial.derivative_one, neg_mul, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_ofNat,
      Complex.ofReal_natCast, Complex.ofReal_one, Complex.ofReal_zero, pow_two,
      Complex.I_mul_I, Polynomial.C_1]
    have h : (Real.cos (4 * t) : ℂ) = ((jetExp t) ^ 4 + ((jetExp t) ^ 4)⁻¹) / 2 := by
      simpa using fc_cos_eq_pow t 4
    have h2 : (Real.sin (4 * t) : ℂ) = ((jetExp t) ^ 4 - ((jetExp t) ^ 4)⁻¹) / (2 * Complex.I) := by
      simpa using fc_sin_eq_pow t 4
    rw [h, h2]
    field_simp <;> simp [pow_two, Complex.I_mul_I] <;> ring
  · show (fcPoly 8).derivative.eval (jetExp t)
      = (jetExp t) ^ 3 * (4 * (trigBasis 8 t : ℂ) - Complex.I * (trigBasisD 8 t : ℂ))
    simp only [fcPoly, trigBasis, trigBasisD, Polynomial.derivative_C_mul, Polynomial.derivative_add, Polynomial.derivative_sub,
      Polynomial.derivative_pow, Polynomial.derivative_X, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.eval_one, Polynomial.derivative_one, neg_mul, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_ofNat,
      Complex.ofReal_natCast, Complex.ofReal_one, Complex.ofReal_zero, pow_two,
      Complex.I_mul_I, Polynomial.C_1]
    have h : (Real.cos (4 * t) : ℂ) = ((jetExp t) ^ 4 + ((jetExp t) ^ 4)⁻¹) / 2 := by
      simpa using fc_cos_eq_pow t 4
    have h2 : (Real.sin (4 * t) : ℂ) = ((jetExp t) ^ 4 - ((jetExp t) ^ 4)⁻¹) / (2 * Complex.I) := by
      simpa using fc_sin_eq_pow t 4
    rw [h, h2]
    field_simp <;> simp [pow_two, Complex.I_mul_I] <;> ring

/-! ## The linear-map versions -/

lemma fcGamma_single (j : Fin 9) :
    fcGamma (Pi.single j (1 : ℂ)) = fcPoly j := by
  rw [trigGamma_apply, Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro hj; exact absurd (Finset.mem_univ j) hj

theorem fcGamma_eval (y : Fin 9 → ℂ) (t : ℝ) :
    (fcGamma y).eval (jetExp t)
      = (jetExp t) ^ 4 * ∑ j : Fin 9, y j * (trigBasis j t : ℂ) := by
  rw [trigGamma_apply, Polynomial.eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.smul_eq_C_mul, Polynomial.eval_mul, Polynomial.eval_C, fcPoly_eval j t]
  ring

theorem fcGamma_derivative_eval (y : Fin 9 → ℂ) (t : ℝ) :
    (fcGamma y).derivative.eval (jetExp t)
      = ∑ j : Fin 9, y j * ((jetExp t) ^ 3 * (4 * (trigBasis j t : ℂ)
          - Complex.I * (trigBasisD j t : ℂ))) := by
  have hder : (fcGamma y).derivative
      = ∑ j : Fin 9, y j • (fcPoly j).derivative := by
    rw [trigGamma_apply, Polynomial.derivative_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Polynomial.smul_eq_C_mul, Polynomial.derivative_C_mul]
  rw [hder, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.smul_eq_C_mul, Polynomial.eval_mul, Polynomial.eval_C,
    fcPoly_derivative_eval j t]

/-! ## Injectivity -/

lemma fcGamma_coeff (y : Fin 9 → ℂ) (m : ℕ) :
    (fcGamma y).coeff m = ∑ j : Fin 9, y j * (fcPoly j).coeff m := by
  rw [← Polynomial.lcoeff_apply, trigGamma_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_eq_mul, ← Polynomial.lcoeff_apply]

lemma fc_sum_univ_nine (f : Fin 9 → ℂ) :
    (∑ j : Fin 9, f j) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 := by
  simp [Fin.sum_univ_succ, add_assoc]

private lemma coeff_four (y : Fin 9 → ℂ) : (fcGamma y).coeff 4 = y 0 := by
  rw [fcGamma_coeff, fc_sum_univ_nine]
  simp only [fcPoly, Polynomial.coeff_C_mul, Polynomial.coeff_add, Polynomial.coeff_sub,
    Polynomial.coeff_X_pow, Polynomial.coeff_one, Polynomial.coeff_X]
  norm_num

private lemma coeff_five (y : Fin 9 → ℂ) :
    (fcGamma y).coeff 5 = y 1 * (1 / 2) + y 2 * ((2 * Complex.I)⁻¹) := by
  rw [fcGamma_coeff, fc_sum_univ_nine]
  simp only [fcPoly, Polynomial.coeff_C_mul, Polynomial.coeff_add, Polynomial.coeff_sub,
    Polynomial.coeff_X_pow, Polynomial.coeff_one, Polynomial.coeff_X]
  norm_num

private lemma coeff_three (y : Fin 9 → ℂ) :
    (fcGamma y).coeff 3 = y 1 * (1 / 2) - y 2 * ((2 * Complex.I)⁻¹) := by
  rw [fcGamma_coeff, fc_sum_univ_nine]
  simp only [fcPoly, Polynomial.coeff_C_mul, Polynomial.coeff_add, Polynomial.coeff_sub,
    Polynomial.coeff_X_pow, Polynomial.coeff_one, Polynomial.coeff_X]
  norm_num

private lemma coeff_six (y : Fin 9 → ℂ) :
    (fcGamma y).coeff 6 = y 3 * (1 / 2) + y 4 * ((2 * Complex.I)⁻¹) := by
  rw [fcGamma_coeff, fc_sum_univ_nine]
  simp only [fcPoly, Polynomial.coeff_C_mul, Polynomial.coeff_add, Polynomial.coeff_sub,
    Polynomial.coeff_X_pow, Polynomial.coeff_one, Polynomial.coeff_X]
  norm_num

private lemma coeff_two (y : Fin 9 → ℂ) :
    (fcGamma y).coeff 2 = y 3 * (1 / 2) - y 4 * ((2 * Complex.I)⁻¹) := by
  rw [fcGamma_coeff, fc_sum_univ_nine]
  simp only [fcPoly, Polynomial.coeff_C_mul, Polynomial.coeff_add, Polynomial.coeff_sub,
    Polynomial.coeff_X_pow, Polynomial.coeff_one, Polynomial.coeff_X]
  norm_num

private lemma coeff_seven (y : Fin 9 → ℂ) :
    (fcGamma y).coeff 7 = y 5 * (1 / 2) + y 6 * ((2 * Complex.I)⁻¹) := by
  rw [fcGamma_coeff, fc_sum_univ_nine]
  simp only [fcPoly, Polynomial.coeff_C_mul, Polynomial.coeff_add, Polynomial.coeff_sub,
    Polynomial.coeff_X_pow, Polynomial.coeff_one, Polynomial.coeff_X]
  norm_num

private lemma coeff_one (y : Fin 9 → ℂ) :
    (fcGamma y).coeff 1 = y 5 * (1 / 2) - y 6 * ((2 * Complex.I)⁻¹) := by
  rw [fcGamma_coeff, fc_sum_univ_nine]
  simp only [fcPoly, Polynomial.coeff_C_mul, Polynomial.coeff_add, Polynomial.coeff_sub,
    Polynomial.coeff_X_pow, Polynomial.coeff_one, Polynomial.coeff_X]
  norm_num

private lemma coeff_eight (y : Fin 9 → ℂ) :
    (fcGamma y).coeff 8 = y 7 * (1 / 2) + y 8 * ((2 * Complex.I)⁻¹) := by
  rw [fcGamma_coeff, fc_sum_univ_nine]
  simp only [fcPoly, Polynomial.coeff_C_mul, Polynomial.coeff_add, Polynomial.coeff_sub,
    Polynomial.coeff_X_pow, Polynomial.coeff_one, Polynomial.coeff_X]
  norm_num

private lemma coeff_zero (y : Fin 9 → ℂ) :
    (fcGamma y).coeff 0 = y 7 * (1 / 2) - y 8 * ((2 * Complex.I)⁻¹) := by
  rw [fcGamma_coeff, fc_sum_univ_nine]
  simp only [fcPoly, Polynomial.coeff_C_mul, Polynomial.coeff_add, Polynomial.coeff_sub,
    Polynomial.coeff_X_pow, Polynomial.coeff_one, Polynomial.coeff_X]
  norm_num

/-- A pair of equations `p / 2 ± q / (2i) = 0` forces `p = q = 0`. -/
private lemma pair_zero {p q : ℂ} (h1 : p * (1 / 2) + q * ((2 * Complex.I)⁻¹) = 0)
    (h2 : p * (1 / 2) - q * ((2 * Complex.I)⁻¹) = 0) : p = 0 ∧ q = 0 := by
  have hne : ((2 * Complex.I)⁻¹ : ℂ) ≠ 0 := inv_ne_zero (by simp [Complex.I_ne_zero])
  have hq : q = 0 := by
    have hd : 2 * (q * ((2 * Complex.I)⁻¹)) = 0 := by linear_combination h1 - h2
    rcases mul_eq_zero.mp hd with h | h
    · exact absurd h (by norm_num)
    · exact (mul_eq_zero.mp h).resolve_right hne
  subst hq
  have hp : p * (1 / 2) = 0 := by simpa using h1
  exact ⟨(mul_eq_zero.mp hp).resolve_right (by norm_num), rfl⟩

theorem fcGamma_injective : Function.Injective fcGamma := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro y hy
  have hy0 : fcGamma y = 0 := hy
  have e : ∀ m : ℕ, (fcGamma y).coeff m = 0 := fun m => by rw [hy0, Polynomial.coeff_zero]
  have h0 : y 0 = 0 := by rw [← coeff_four y]; exact e 4
  have h12 : y 1 = 0 ∧ y 2 = 0 := by
    refine pair_zero ?_ ?_
    · rw [← coeff_five y]; exact e 5
    · rw [← coeff_three y]; exact e 3
  have h34 : y 3 = 0 ∧ y 4 = 0 := by
    refine pair_zero ?_ ?_
    · rw [← coeff_six y]; exact e 6
    · rw [← coeff_two y]; exact e 2
  have h56 : y 5 = 0 ∧ y 6 = 0 := by
    refine pair_zero ?_ ?_
    · rw [← coeff_seven y]; exact e 7
    · rw [← coeff_one y]; exact e 1
  have h78 : y 7 = 0 ∧ y 8 = 0 := by
    refine pair_zero ?_ ?_
    · rw [← coeff_eight y]; exact e 8
    · rw [← coeff_zero y]; exact e 0
  funext j
  fin_cases j
  · exact h0
  · exact h12.1
  · exact h12.2
  · exact h34.1
  · exact h34.2
  · exact h56.1
  · exact h56.2
  · exact h78.1
  · exact h78.2

end

end Work.Drive
