import Mathlib
import Submission.Work.ZeroFreeTables.P10.Defs14
import Submission.Work.ZeroFreeTables.P3.Pointwise91
import Submission.Work.ZeroFreeTables.P3.WLBase

open DirichletCharacter Complex
open scoped Classical BigOperators ComplexConjugate

namespace Work.ZeroFreeTables.HB103

open Work.ZeroFreeTables.P3 (hbE hbE_add hbE_sub_div hbE_norm hbE_zero hbWL_nonneg)
open Work.ZeroFreeTables.P10 (coef14 chi14 dl14 comb14Raw hbRawG hbTermG hbRawG_eq_hbTermG
  prod_three_re_expand conj_char hbE_conj hbE_inv chi123_inv_eq_one chi13_inv2_eq_one
  chi23_inv1_eq_one)

noncomputable section

/-- **Complex form of the fourteen-term pointwise identity.**  For a unit `n` modulo `N`, the
coefficient-weighted sum of the fourteen characters times the exponential factors collapses to the
"hermitian" expansion of `(1 + Re z₁)(1 + Re z₂)(1 + Re z₃)`, `z_j = χ_j(n) n^{-iγ_j}`. -/
private lemma comb14_complex {N : ℕ} [NeZero N] (chi1 chi2 chi3 : DirichletCharacter ℂ N)
    (γ1 γ2 γ3 : ℝ) (n : ℕ) (hunit : IsUnit (n : ZMod N))
    (hsq1 : chi1 ^ 2 = 1) (hsq2 : chi2 ^ 2 = 1) (hsq3 : chi3 ^ 2 = 1)
    (hprod : chi1 * chi2 * chi3 = 1) :
    (∑ i : Fin 14, ((coef14 i : ℂ) *
        ((chi14 N chi1 chi2 chi3 i) (n : ZMod N) * hbE (dl14 γ1 γ2 γ3 i) n)))
      = 1 + (chi1 ↑n * hbE γ1 n)
          + (chi2 ↑n * hbE γ2 n)
          + (chi3 ↑n * hbE γ3 n)
        + ((1/2 : ℝ) : ℂ) * (
            (chi1 ↑n * hbE γ1 n) * (chi2 ↑n * hbE γ2 n)
          + (chi1 ↑n * hbE γ1 n) * conj (chi2 ↑n * hbE γ2 n)
          + (chi1 ↑n * hbE γ1 n) * (chi3 ↑n * hbE γ3 n)
          + (chi1 ↑n * hbE γ1 n) * conj (chi3 ↑n * hbE γ3 n)
          + (chi2 ↑n * hbE γ2 n) * (chi3 ↑n * hbE γ3 n)
          + (chi2 ↑n * hbE γ2 n) * conj (chi3 ↑n * hbE γ3 n))
        + ((1/4 : ℝ) : ℂ) * (
            (chi1 ↑n * hbE γ1 n) * (chi2 ↑n * hbE γ2 n) * (chi3 ↑n * hbE γ3 n)
          + (chi1 ↑n * hbE γ1 n) * (chi2 ↑n * hbE γ2 n) * conj (chi3 ↑n * hbE γ3 n)
          + (chi1 ↑n * hbE γ1 n) * conj (chi2 ↑n * hbE γ2 n) * (chi3 ↑n * hbE γ3 n)
          + conj (chi1 ↑n * hbE γ1 n) * (chi2 ↑n * hbE γ2 n) * (chi3 ↑n * hbE γ3 n)) := by
  have hC123 : chi1 ↑n * chi2 ↑n * chi3 ↑n = 1 := by
    have hh := congrArg (fun ψ : DirichletCharacter ℂ N => ψ (n : ZMod N)) hprod
    simpa [MulChar.mul_apply, MulChar.one_apply hunit] using hh
  have hC12D3 : chi1 ↑n * chi2 ↑n * chi3⁻¹ ↑n = 1 := by
    have hh := congrArg (fun ψ : DirichletCharacter ℂ N => ψ (n : ZMod N))
      (chi123_inv_eq_one hsq3 hprod)
    simpa [MulChar.mul_apply, MulChar.one_apply hunit] using hh
  have hC1D2C3 : chi1 ↑n * chi2⁻¹ ↑n * chi3 ↑n = 1 := by
    have hh := congrArg (fun ψ : DirichletCharacter ℂ N => ψ (n : ZMod N))
      (chi13_inv2_eq_one hsq2 hprod)
    have hh' : chi1 ↑n * chi3 ↑n * chi2⁻¹ ↑n = 1 := by
      simpa [MulChar.mul_apply, MulChar.one_apply hunit] using hh
    rw [← hh']; ring
  have hD1C23 : chi1⁻¹ ↑n * chi2 ↑n * chi3 ↑n = 1 := by
    have hh := congrArg (fun ψ : DirichletCharacter ℂ N => ψ (n : ZMod N))
      (chi23_inv1_eq_one hsq1 hprod)
    have hh' : chi2 ↑n * chi3 ↑n * chi1⁻¹ ↑n = 1 := by
      simpa [MulChar.mul_apply, MulChar.one_apply hunit] using hh
    rw [← hh']; ring
  have h1 : chi1⁻¹ ↑n * hbE (-γ1) n = conj (chi1 ↑n * hbE γ1 n) := by
    rw [map_mul, conj_char, hbE_conj]
  have h2 : chi2⁻¹ ↑n * hbE (-γ2) n = conj (chi2 ↑n * hbE γ2 n) := by
    rw [map_mul, conj_char, hbE_conj]
  have h3 : chi3⁻¹ ↑n * hbE (-γ3) n = conj (chi3 ↑n * hbE γ3 n) := by
    rw [map_mul, conj_char, hbE_conj]
  have e12 : hbE (γ1 + γ2) n = hbE γ1 n * hbE γ2 n := by rw [← hbE_add γ1 γ2 n]
  have e13 : hbE (γ1 + γ3) n = hbE γ1 n * hbE γ3 n := by rw [← hbE_add γ1 γ3 n]
  have e23 : hbE (γ2 + γ3) n = hbE γ2 n * hbE γ3 n := by rw [← hbE_add γ2 γ3 n]
  have e12' : hbE (γ1 - γ2) n = hbE γ1 n * hbE (-γ2) n := by
    rw [hbE_sub_div, div_eq_mul_inv, hbE_inv]
  have e13' : hbE (γ1 - γ3) n = hbE γ1 n * hbE (-γ3) n := by
    rw [hbE_sub_div, div_eq_mul_inv, hbE_inv]
  have e23' : hbE (γ2 - γ3) n = hbE γ2 n * hbE (-γ3) n := by
    rw [hbE_sub_div, div_eq_mul_inv, hbE_inv]
  have hA : hbE (γ1 + γ2 + γ3) n = hbE γ1 n * hbE γ2 n * hbE γ3 n := by
    rw [show γ1 + γ2 + γ3 = (γ1 + γ2) + γ3 by ring, ← hbE_add (γ1 + γ2) γ3 n,
      ← hbE_add γ1 γ2 n]
  have hB : hbE (γ1 + γ2 - γ3) n = hbE γ1 n * hbE γ2 n * hbE (-γ3) n := by
    rw [show γ1 + γ2 - γ3 = (γ1 + γ2) + (-γ3) by ring, ← hbE_add (γ1 + γ2) (-γ3) n,
      ← hbE_add γ1 γ2 n]
  have hC : hbE (γ1 - γ2 + γ3) n = hbE γ1 n * hbE (-γ2) n * hbE γ3 n := by
    rw [show γ1 - γ2 + γ3 = (γ1 - γ2) + γ3 by ring, ← hbE_add (γ1 - γ2) γ3 n,
      hbE_sub_div, div_eq_mul_inv, hbE_inv]
  have hD : hbE (-γ1 + γ2 + γ3) n = hbE (-γ1) n * hbE γ2 n * hbE γ3 n := by
    rw [show -γ1 + γ2 + γ3 = (-γ1) + (γ2 + γ3) by ring, ← hbE_add (-γ1) (γ2 + γ3) n,
      ← hbE_add γ2 γ3 n]
    ring
  have t10 : (1 : DirichletCharacter ℂ N) (n : ZMod N) * hbE (γ1 + γ2 + γ3) n
      = (chi1 ↑n * hbE γ1 n) * (chi2 ↑n * hbE γ2 n) * (chi3 ↑n * hbE γ3 n) := by
    rw [MulChar.one_apply hunit, hA, ← hC123]; ring
  have t11 : (1 : DirichletCharacter ℂ N) (n : ZMod N) * hbE (γ1 + γ2 - γ3) n
      = (chi1 ↑n * hbE γ1 n) * (chi2 ↑n * hbE γ2 n) * conj (chi3 ↑n * hbE γ3 n) := by
    rw [MulChar.one_apply hunit, hB, ← h3, ← hC12D3]; ring
  have t12 : (1 : DirichletCharacter ℂ N) (n : ZMod N) * hbE (γ1 - γ2 + γ3) n
      = (chi1 ↑n * hbE γ1 n) * conj (chi2 ↑n * hbE γ2 n) * (chi3 ↑n * hbE γ3 n) := by
    rw [MulChar.one_apply hunit, hC, ← h2, ← hC1D2C3]; ring
  have t13 : (1 : DirichletCharacter ℂ N) (n : ZMod N) * hbE (-γ1 + γ2 + γ3) n
      = conj (chi1 ↑n * hbE γ1 n) * (chi2 ↑n * hbE γ2 n) * (chi3 ↑n * hbE γ3 n) := by
    rw [MulChar.one_apply hunit, hD, ← h1, ← hD1C23]; ring
  simp only [coef14, chi14, dl14, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, MulChar.mul_apply, hbE_zero,
    e12, e13, e23, e12', e13', e23']
  rw [t10, t11, t12, t13]
  simp only [MulChar.one_apply hunit]
  rw [← h1, ← h2, ← h3]
  push_cast
  ring

/-- **Real form of the fourteen-term pointwise identity.**  The `.re` of the complex identity is
`(1 + Re z₁)(1 + Re z₂)(1 + Re z₃)`. -/
private lemma comb14_re {N : ℕ} [NeZero N] (chi1 chi2 chi3 : DirichletCharacter ℂ N)
    (γ1 γ2 γ3 : ℝ) (n : ℕ) (hunit : IsUnit (n : ZMod N))
    (hsq1 : chi1 ^ 2 = 1) (hsq2 : chi2 ^ 2 = 1) (hsq3 : chi3 ^ 2 = 1)
    (hprod : chi1 * chi2 * chi3 = 1) :
    (∑ i : Fin 14, coef14 i *
        (((chi14 N chi1 chi2 chi3 i) (n : ZMod N) * hbE (dl14 γ1 γ2 γ3 i) n).re))
      = (1 + (chi1 ↑n * hbE γ1 n).re) * (1 + (chi2 ↑n * hbE γ2 n).re)
        * (1 + (chi3 ↑n * hbE γ3 n).re) := by
  have h := congrArg Complex.re
    (comb14_complex chi1 chi2 chi3 γ1 γ2 γ3 n hunit hsq1 hsq2 hsq3 hprod)
  have hL : (∑ i : Fin 14, ((coef14 i : ℂ) *
        ((chi14 N chi1 chi2 chi3 i) (n : ZMod N) * hbE (dl14 γ1 γ2 γ3 i) n))).re
      = ∑ i : Fin 14, coef14 i *
        (((chi14 N chi1 chi2 chi3 i) (n : ZMod N) * hbE (dl14 γ1 γ2 γ3 i) n).re) := by
    have hh := map_sum Complex.reAddGroupHom
      (fun i : Fin 14 => (coef14 i : ℂ) *
        ((chi14 N chi1 chi2 chi3 i) (n : ZMod N) * hbE (dl14 γ1 γ2 γ3 i) n)) Finset.univ
    have hh' : (∑ i : Fin 14, ((coef14 i : ℂ) *
          ((chi14 N chi1 chi2 chi3 i) (n : ZMod N) * hbE (dl14 γ1 γ2 γ3 i) n))).re
        = ∑ i : Fin 14, ((coef14 i : ℂ) *
          ((chi14 N chi1 chi2 chi3 i) (n : ZMod N) * hbE (dl14 γ1 γ2 γ3 i) n)).re := by
      simpa using hh
    rw [hh']
    apply Finset.sum_congr rfl
    intro i _
    exact Complex.re_ofReal_mul (coef14 i) _
  rw [hL] at h
  have hEre : (1 + (chi1 ↑n * hbE γ1 n) + (chi2 ↑n * hbE γ2 n) + (chi3 ↑n * hbE γ3 n)
        + ((1/2 : ℝ) : ℂ) * (
            (chi1 ↑n * hbE γ1 n) * (chi2 ↑n * hbE γ2 n)
          + (chi1 ↑n * hbE γ1 n) * conj (chi2 ↑n * hbE γ2 n)
          + (chi1 ↑n * hbE γ1 n) * (chi3 ↑n * hbE γ3 n)
          + (chi1 ↑n * hbE γ1 n) * conj (chi3 ↑n * hbE γ3 n)
          + (chi2 ↑n * hbE γ2 n) * (chi3 ↑n * hbE γ3 n)
          + (chi2 ↑n * hbE γ2 n) * conj (chi3 ↑n * hbE γ3 n))
        + ((1/4 : ℝ) : ℂ) * (
            (chi1 ↑n * hbE γ1 n) * (chi2 ↑n * hbE γ2 n) * (chi3 ↑n * hbE γ3 n)
          + (chi1 ↑n * hbE γ1 n) * (chi2 ↑n * hbE γ2 n) * conj (chi3 ↑n * hbE γ3 n)
          + (chi1 ↑n * hbE γ1 n) * conj (chi2 ↑n * hbE γ2 n) * (chi3 ↑n * hbE γ3 n)
          + conj (chi1 ↑n * hbE γ1 n) * (chi2 ↑n * hbE γ2 n) * (chi3 ↑n * hbE γ3 n))).re
      = (1 + (chi1 ↑n * hbE γ1 n).re) * (1 + (chi2 ↑n * hbE γ2 n).re)
        * (1 + (chi3 ↑n * hbE γ3 n).re) := by
    rw [prod_three_re_expand]
    simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.one_re]
  rw [hEre] at h
  exact h

/-- **`comb14Raw` at a unit `n`.**  The fourteen-term combination factors as the common
non-negative factor `Λ n · n^{-σ} · u(log n / L)` times `(1 + Re z₁)(1 + Re z₂)(1 + Re z₃)`. -/
private lemma comb14Raw_unit {N : ℕ} [NeZero N] (chi1 chi2 chi3 : DirichletCharacter ℂ N)
    (L σ γ1 γ2 γ3 a lam₁ : ℝ) (n : ℕ) (hunit : IsUnit (n : ZMod N))
    (hsq1 : chi1 ^ 2 = 1) (hsq2 : chi2 ^ 2 = 1) (hsq3 : chi3 ^ 2 = 1)
    (hprod : chi1 * chi2 * chi3 = 1) :
    comb14Raw N chi1 chi2 chi3 L σ γ1 γ2 γ3 a lam₁ n
      = (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)
          * Work.ZeroFreeTables.hbWL L a lam₁ n
        * ((1 + (chi1 ↑n * hbE γ1 n).re) * (1 + (chi2 ↑n * hbE γ2 n).re)
            * (1 + (chi3 ↑n * hbE γ3 n).re)) := by
  have h1 : comb14Raw N chi1 chi2 chi3 L σ γ1 γ2 γ3 a lam₁ n
      = ∑ i : Fin 14, coef14 i * ((ArithmeticFunction.vonMangoldt n : ℝ) *
          (((chi14 N chi1 chi2 chi3 i) (n : ZMod N) * hbE (dl14 γ1 γ2 γ3 i) n).re)
          * (n : ℝ) ^ (-σ) * Work.ZeroFreeTables.hbWL L a lam₁ n) := by
    simp only [comb14Raw]
    apply Finset.sum_congr rfl
    intro i _
    simp only [hbRawG_eq_hbTermG, hbTermG]
  have hkey := comb14_re chi1 chi2 chi3 γ1 γ2 γ3 n hunit hsq1 hsq2 hsq3 hprod
  rw [h1, ← hkey, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem Comb14Positivity {N : ℕ} [NeZero N] (chi1 chi2 chi3 : DirichletCharacter ℂ N)
    (L σ γ1 γ2 γ3 a lam₁ : ℝ) (ha : 0 < a) (hL : 0 < L) (hlam : 0 ≤ lam₁)
    (hsq1 : chi1 ^ 2 = 1) (hsq2 : chi2 ^ 2 = 1) (hsq3 : chi3 ^ 2 = 1)
    (hprod : chi1 * chi2 * chi3 = 1) (n : ℕ) :
    0 ≤ Work.ZeroFreeTables.P10.comb14Raw N chi1 chi2 chi3 L σ γ1 γ2 γ3 a lam₁ n := by
  by_cases hunit : IsUnit (n : ZMod N)
  · rw [comb14Raw_unit chi1 chi2 chi3 L σ γ1 γ2 γ3 a lam₁ n hunit hsq1 hsq2 hsq3 hprod]
    refine mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) (mul_nonneg (mul_nonneg ?_ ?_) ?_)
    · exact ArithmeticFunction.vonMangoldt_nonneg
    · exact Real.rpow_nonneg (Nat.cast_nonneg n) _
    · exact hbWL_nonneg hL ha hlam n
    · have hnorm : ‖chi1 ↑n * hbE γ1 n‖ = 1 := by
        have h : (↑hunit.unit : ZMod N) = (n : ZMod N) := hunit.unit_spec
        rw [norm_mul, ← h, DirichletCharacter.unit_norm_eq_one chi1 hunit.unit, hbE_norm, one_mul]
      have hre := Complex.re_le_norm (-(chi1 ↑n * hbE γ1 n))
      rw [Complex.neg_re, norm_neg, hnorm] at hre
      linarith
    · have hnorm : ‖chi2 ↑n * hbE γ2 n‖ = 1 := by
        have h : (↑hunit.unit : ZMod N) = (n : ZMod N) := hunit.unit_spec
        rw [norm_mul, ← h, DirichletCharacter.unit_norm_eq_one chi2 hunit.unit, hbE_norm, one_mul]
      have hre := Complex.re_le_norm (-(chi2 ↑n * hbE γ2 n))
      rw [Complex.neg_re, norm_neg, hnorm] at hre
      linarith
    · have hnorm : ‖chi3 ↑n * hbE γ3 n‖ = 1 := by
        have h : (↑hunit.unit : ZMod N) = (n : ZMod N) := hunit.unit_spec
        rw [norm_mul, ← h, DirichletCharacter.unit_norm_eq_one chi3 hunit.unit, hbE_norm, one_mul]
      have hre := Complex.re_le_norm (-(chi3 ↑n * hbE γ3 n))
      rw [Complex.neg_re, norm_neg, hnorm] at hre
      linarith
  · have h0 : ∀ ψ : DirichletCharacter ℂ N, ψ (n : ZMod N) = 0 :=
      fun ψ => MulChar.map_nonunit ψ hunit
    have hzero : comb14Raw N chi1 chi2 chi3 L σ γ1 γ2 γ3 a lam₁ n = 0 := by
      simp only [comb14Raw]
      apply Finset.sum_eq_zero
      intro i _
      simp only [hbRawG, h0 (chi14 N chi1 chi2 chi3 i)]
      simp
    rw [hzero]

end

end Work.ZeroFreeTables.HB103
