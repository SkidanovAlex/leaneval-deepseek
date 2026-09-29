import Mathlib
import Submission.Work.C17adj.divisor_defs

/-!
# Leading-term facts for the adjoint divisor bound (`Work.C17adj.phi_lead_facts`)

The hypotheses of `Work.C17adj.phi_UZ_facts` — the degree and leading-coefficient data of the
three coefficient polynomials `PhiU, PhiV, PhiZ` of the cleared adjoint numerator — are the
top-degree data of the polynomials

* `P2Cm, P1Cm, P0Cm`, the `ℂ`-images of the coefficient polynomials `P2x, P1x, P0x` of the
  order-two operator `M = P₂∂² + P₁∂ + P₀` of Calegari--Dimitrov--Tang (arXiv:2408.15403),
* `AadjL = 2·P2Cm' − P1Cm` and `CadjL = P2Cm'' − P1Cm' + P0Cm`, the `β'`- and
  `β`-coefficients of the adjoint operator,
* `DadjL = X⁶(X−1)²(X+1)²`, the universal denominator, together with its first two derivatives.

Here `P2x = (X−1)·X·(X+1)·Q₄` with `Q₄` monic of degree four, so `P2x` is monic of degree `7`;
`P1x` has degree `6` with leading coefficient `3`, and `P0x` has degree `5` with leading
coefficient `1`.  Hence `AadjL` has degree `6` with leading coefficient `2·7 − 3 = 11`, while
`CadjL` has degree `5` with leading coefficient `7·6 − 6·3 + 1 = 25`.  On the `D`-side,
`DadjL' = 10X⁹ − 16X⁷ + 6X⁵` and `DadjL'' = 90X⁸ − 112X⁶ + 30X⁴`.

Everything is a finite coefficient computation on explicit polynomials; the `ℚ`-facts are pushed
to `ℂ` with `Polynomial.natDegree_map_eq_of_injective` (for the degree bounds, since `DadjL` is
not monic) and `Polynomial.coeff_map` (for the coefficient values), and the two adjoint
coefficients are identified with the explicit polynomials `Work.C17.Badj`, `Work.C17.Cadj` of
`Work.C17.adjoint_defs`.
-/

open Polynomial

namespace Work.C17adj

noncomputable section

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-! ## The `ℚ`-facts: `P2x, P1x, P0x` -/

private lemma P2x_natDegree_lc (a b : ℚ) : (Work.C17.P2x a b).natDegree = 7 := by
  rw [Work.C17.P2x, Work.C17.Q4x]; compute_degree!

private lemma P2x_coeff_lc (a b : ℚ) : (Work.C17.P2x a b).coeff 7 = 1 := by
  rw [Work.C17.P2x, Work.C17.Q4x]; compute_degree!

private lemma P1x_natDegree_lc (a b : ℚ) : (Work.C17.P1x a b).natDegree = 6 := by
  rw [Work.C17.P1x]; compute_degree!; norm_num [Polynomial.coeff_one]

private lemma P1x_coeff_lc (a b : ℚ) : (Work.C17.P1x a b).coeff 6 = 3 := by
  rw [Work.C17.P1x]; compute_degree!; norm_num [Polynomial.coeff_one]

private lemma P0x_natDegree_lc (a b : ℚ) : (Work.C17.P0x a b).natDegree = 5 := by
  rw [Work.C17.P0x]; compute_degree!

private lemma P0x_coeff_lc (a b : ℚ) : (Work.C17.P0x a b).coeff 5 = 1 := by
  rw [Work.C17.P0x]; compute_degree!

/-! ## The `ℚ`-facts: `Dadj` and its derivatives -/

private lemma Dadj_natDegree_lc : (Work.C17.Dadj : Polynomial ℚ).natDegree ≤ 10 := by
  rw [Work.C17.Dadj]; compute_degree!

private lemma Dadj_coeff_lc : (Work.C17.Dadj : Polynomial ℚ).coeff 10 = 1 := by
  rw [Work.C17.Dadj]; compute_degree!

private lemma Dadj1_natDegree_lc : (Work.C17.Dadj1 : Polynomial ℚ).natDegree ≤ 9 := by
  rw [Work.C17.Dadj1]; compute_degree!

private lemma Dadj1_coeff_lc : (Work.C17.Dadj1 : Polynomial ℚ).coeff 9 = 10 := by
  rw [Work.C17.Dadj1]; compute_degree!

private lemma Dadj2_natDegree_lc : (Work.C17.Dadj2 : Polynomial ℚ).natDegree ≤ 8 := by
  rw [Work.C17.Dadj2]; compute_degree!

private lemma Dadj2_coeff_lc : (Work.C17.Dadj2 : Polynomial ℚ).coeff 8 = 90 := by
  rw [Work.C17.Dadj2]; compute_degree!

private lemma Dadj_derivative_lc : (Work.C17.Dadj : Polynomial ℚ).derivative = Work.C17.Dadj1 := by
  simp only [Work.C17.Dadj, Work.C17.Dadj1, derivative_add, derivative_C_mul_X_pow]; norm_num

private lemma Dadj1_derivative_lc : (Work.C17.Dadj1 : Polynomial ℚ).derivative = Work.C17.Dadj2 := by
  simp only [Work.C17.Dadj1, Work.C17.Dadj2, derivative_add, derivative_C_mul_X_pow]; norm_num

/-! ## The `ℚ`-facts: the explicit adjoint coefficients `Badj`, `Cadj` -/

private lemma Badj_natDegree_lc (a b : ℚ) : (Work.C17.Badj a b).natDegree ≤ 6 := by
  rw [Work.C17.Badj]; compute_degree!

private lemma Badj_coeff_lc (a b : ℚ) : (Work.C17.Badj a b).coeff 6 = 11 := by
  rw [Work.C17.Badj]; compute_degree!

private lemma Cadj_natDegree_lc (a b : ℚ) : (Work.C17.Cadj a b).natDegree ≤ 5 := by
  rw [Work.C17.Cadj]; compute_degree!

private lemma Cadj_coeff_lc (a b : ℚ) : (Work.C17.Cadj a b).coeff 5 = 25 := by
  rw [Work.C17.Cadj]; compute_degree!

/-- `Work.C17.Badj` is `2·P2x' − P1x`. -/
private lemma Badj_eq_deriv_lc (a b : ℚ) :
    Work.C17.Badj a b = 2 * (Work.C17.P2x a b).derivative - Work.C17.P1x a b := by
  simp only [Work.C17.Badj, Work.C17.P1x, Work.C17.P2x, Work.C17.Q4x, derivative_add, derivative_mul,
    derivative_sub, derivative_X, derivative_C, derivative_one, derivative_X_pow]
  ring_nf
  simp only [map_mul, map_add, map_sub, map_pow, map_neg, map_natCast, map_ofNat, map_one, map_zero,
    Nat.cast_ofNat, pow_zero, mul_one, one_mul, zero_mul, mul_zero, neg_zero, zero_add, add_zero,
    pow_one]
  ring

/-- `Work.C17.Cadj` is `P2x'' − P1x' + P0x`. -/
private lemma Cadj_eq_deriv_lc (a b : ℚ) :
    Work.C17.Cadj a b
      = (Work.C17.P2x a b).derivative.derivative - (Work.C17.P1x a b).derivative
        + Work.C17.P0x a b := by
  simp only [Work.C17.Cadj, Work.C17.P1x, Work.C17.P2x, Work.C17.P0x, Work.C17.Q4x, derivative_add,
    derivative_mul, derivative_sub, derivative_neg, derivative_X, derivative_C, derivative_one,
    derivative_X_pow]
  ring_nf
  simp only [map_mul, map_add, map_sub, map_pow, map_neg, map_natCast, map_ofNat, map_one, map_zero,
    Nat.cast_ofNat, pow_zero, mul_one, one_mul, zero_mul, mul_zero, neg_zero, zero_add, add_zero,
    pow_one]
  ring

/-! ## Transfer to `ℂ`: `P2Cm, P1Cm, P0Cm` -/

private lemma P2Cm_natDegree_lc (a b : ℚ) : (P2Cm a b).natDegree ≤ 7 := by
  rw [P2Cm, Polynomial.natDegree_map_eq_of_injective (Rat.cast_injective), P2x_natDegree_lc]

private lemma P2Cm_coeff_lc (a b : ℚ) : (P2Cm a b).coeff 7 = 1 := by
  rw [P2Cm, Polynomial.coeff_map, P2x_coeff_lc]; norm_num

private lemma P1Cm_natDegree_lc (a b : ℚ) : (P1Cm a b).natDegree ≤ 6 := by
  rw [P1Cm, Polynomial.natDegree_map_eq_of_injective (Rat.cast_injective), P1x_natDegree_lc]

private lemma P1Cm_coeff_lc (a b : ℚ) : (P1Cm a b).coeff 6 = 3 := by
  rw [P1Cm, Polynomial.coeff_map, P1x_coeff_lc]; norm_num

private lemma P0Cm_natDegree_lc (a b : ℚ) : (P0Cm a b).natDegree ≤ 5 := by
  rw [P0Cm, Polynomial.natDegree_map_eq_of_injective (Rat.cast_injective), P0x_natDegree_lc]

private lemma P0Cm_coeff_lc (a b : ℚ) : (P0Cm a b).coeff 5 = 1 := by
  rw [P0Cm, Polynomial.coeff_map, P0x_coeff_lc]; norm_num

/-! ## Transfer to `ℂ`: `DadjL` and its derivatives -/

private lemma DadjL_derivative_lc :
    DadjL.derivative = (Work.C17.Dadj1).map (algebraMap ℚ ℂ) := by
  rw [DadjL, Polynomial.derivative_map, Dadj_derivative_lc]

private lemma DadjL_deriv2_lc :
    DadjL.derivative.derivative = (Work.C17.Dadj2).map (algebraMap ℚ ℂ) := by
  rw [DadjL_derivative_lc, Polynomial.derivative_map, Dadj1_derivative_lc]

private lemma DadjL_natDegree_lc : DadjL.natDegree ≤ 10 := by
  rw [DadjL, Polynomial.natDegree_map_eq_of_injective (Rat.cast_injective)]
  exact Dadj_natDegree_lc

private lemma DadjL_coeff_lc : DadjL.coeff 10 = 1 := by
  rw [DadjL, Polynomial.coeff_map, Dadj_coeff_lc]; norm_num

private lemma DadjL_derivative_natDegree_lc : DadjL.derivative.natDegree ≤ 9 := by
  rw [DadjL_derivative_lc, Polynomial.natDegree_map_eq_of_injective (Rat.cast_injective)]
  exact Dadj1_natDegree_lc

private lemma DadjL_derivative_coeff_lc : DadjL.derivative.coeff 9 = 10 := by
  rw [DadjL_derivative_lc, Polynomial.coeff_map, Dadj1_coeff_lc]; norm_num

private lemma DadjL_deriv2_natDegree_lc : DadjL.derivative.derivative.natDegree ≤ 8 := by
  rw [DadjL_deriv2_lc, Polynomial.natDegree_map_eq_of_injective (Rat.cast_injective)]
  exact Dadj2_natDegree_lc

private lemma DadjL_deriv2_coeff_lc : DadjL.derivative.derivative.coeff 8 = 90 := by
  rw [DadjL_deriv2_lc, Polynomial.coeff_map, Dadj2_coeff_lc]; norm_num

/-! ## Transfer to `ℂ`: the adjoint coefficients `AadjL, CadjL` -/

private lemma AadjL_eq_map_lc (a b : ℚ) :
    AadjL a b = (Work.C17.Badj a b).map (algebraMap ℚ ℂ) := by
  rw [AadjL, P2Cm, P1Cm, Polynomial.derivative_map, Badj_eq_deriv_lc]
  simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_ofNat]

private lemma CadjL_eq_map_lc (a b : ℚ) :
    CadjL a b = (Work.C17.Cadj a b).map (algebraMap ℚ ℂ) := by
  rw [CadjL, P2Cm, P1Cm, P0Cm, Cadj_eq_deriv_lc]
  simp only [Polynomial.derivative_map, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_ofNat]

private lemma AadjL_natDegree_lc (a b : ℚ) : (AadjL a b).natDegree ≤ 6 := by
  rw [AadjL_eq_map_lc, Polynomial.natDegree_map_eq_of_injective (Rat.cast_injective)]
  exact Badj_natDegree_lc a b

private lemma AadjL_coeff_lc (a b : ℚ) : (AadjL a b).coeff 6 = 11 := by
  rw [AadjL_eq_map_lc, Polynomial.coeff_map, Badj_coeff_lc]; norm_num

private lemma CadjL_natDegree_lc (a b : ℚ) : (CadjL a b).natDegree ≤ 5 := by
  rw [CadjL_eq_map_lc, Polynomial.natDegree_map_eq_of_injective (Rat.cast_injective)]
  exact Cadj_natDegree_lc a b

private lemma CadjL_coeff_lc (a b : ℚ) : (CadjL a b).coeff 5 = 25 := by
  rw [CadjL_eq_map_lc, Polynomial.coeff_map, Cadj_coeff_lc]; norm_num

/-! ## The target -/

theorem phi_lead_facts (a b : ℚ) :
    (Work.C17adj.P2Cm a b).natDegree ≤ 7 ∧ (Work.C17adj.P2Cm a b).coeff 7 = 1 ∧
    (Work.C17adj.P1Cm a b).natDegree ≤ 6 ∧ (Work.C17adj.P1Cm a b).coeff 6 = 3 ∧
    (Work.C17adj.P0Cm a b).natDegree ≤ 5 ∧ (Work.C17adj.P0Cm a b).coeff 5 = 1 ∧
    (Work.C17adj.AadjL a b).natDegree ≤ 6 ∧ (Work.C17adj.AadjL a b).coeff 6 = 11 ∧
    (Work.C17adj.CadjL a b).natDegree ≤ 5 ∧ (Work.C17adj.CadjL a b).coeff 5 = 25 ∧
    Work.C17adj.DadjL.natDegree ≤ 10 ∧ Work.C17adj.DadjL.coeff 10 = 1 ∧
    Work.C17adj.DadjL.derivative.natDegree ≤ 9 ∧ Work.C17adj.DadjL.derivative.coeff 9 = 10 ∧
    Work.C17adj.DadjL.derivative.derivative.natDegree ≤ 8 ∧
      Work.C17adj.DadjL.derivative.derivative.coeff 8 = 90 :=
  ⟨P2Cm_natDegree_lc a b, P2Cm_coeff_lc a b, P1Cm_natDegree_lc a b, P1Cm_coeff_lc a b,
    P0Cm_natDegree_lc a b, P0Cm_coeff_lc a b, AadjL_natDegree_lc a b, AadjL_coeff_lc a b,
    CadjL_natDegree_lc a b, CadjL_coeff_lc a b, DadjL_natDegree_lc, DadjL_coeff_lc,
    DadjL_derivative_natDegree_lc, DadjL_derivative_coeff_lc, DadjL_deriv2_natDegree_lc,
    DadjL_deriv2_coeff_lc⟩

end

end Work.C17adj
