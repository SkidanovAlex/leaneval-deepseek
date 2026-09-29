import Mathlib
import Submission.Work.C17.local_tools
import Submission.Work.C17.lead2_rhoQ
import Submission.Work.C17.lead2_ratio

/-!
# The local expansion data at `x = 0` for the `C17` order-three class lemma

This file proves `Work.C17.local_base`, the six `Lead2At` facts at `x = 0` used by
`Work.C17.order3_class_injective`:

* `rhoQ = -1/(2x) + 3/4 + O(x)`,  `dRat rhoQ = 1/(2x²) + O(1)`;
* `P₀ = a·b + (1-3a²-3b²)·x + O(x²)`;
* `P₁ = -1 + 8ab·x + O(x²)`;
* `P₂ = -x + 4ab·x² + O(x³)`;
* `P₁/P₂ = 1/x - 4ab + O(x)`.

Each is proved by exhibiting the (regular) quotient `g` in
`f·x^{-e} - l - m·x = x²·g` and applying `Work.C17.lead2At_of_eq`.
-/

namespace Work.C17

open Commons.FieldTheory.RatFunc
open Polynomial

noncomputable section

local notation "algP" => algebraMap (Polynomial ℚ) (RatFunc ℚ)

/-! ## The polynomial cofactors -/

/-- The quotient `(P₀ - a·b - (1-3a²-3b²)·X)/X²`. -/
def coefP0 (a b : ℚ) : Polynomial ℚ :=
  C (8 * a * b) - C (a ^ 2 + b ^ 2 + 2) * X - C (a * b) * X ^ 2 + X ^ 3

/-- The quotient `(P₁ + 1 - 8ab·X)/X²`. -/
def coefP1 (a b : ℚ) : Polynomial ℚ :=
  C (5 - 12 * a ^ 2 - 12 * b ^ 2) + C (16 * a * b) * X + C (4 * a ^ 2 + 4 * b ^ 2 - 7) * X ^ 2
    - C (8 * a * b) * X ^ 3 + C 3 * X ^ 4

/-- `P₂/X = (x²-1)·Q₄`. -/
def coefP2a (a b : ℚ) : Polynomial ℚ := (X - 1) * (X + 1) * Q4x a b

/-- The quotient `(P₂/X + 1 - 4ab·X)/X²`. -/
def coefP2b (a b : ℚ) : Polynomial ℚ :=
  (1 - C (4 * a ^ 2 + 4 * b ^ 2 - 2))
    + (C (4 * a ^ 2 + 4 * b ^ 2 - 2) - 1) * X ^ 2 - C (4 * a * b) * X ^ 3 + X ^ 4

lemma P0x_sub (a b : ℚ) :
    P0x a b - C (a * b) - C (1 - 3 * a ^ 2 - 3 * b ^ 2) * X
      = X ^ 2 * coefP0 a b := by
  unfold coefP0 P0x
  ring

lemma P1x_sub (a b : ℚ) :
    P1x a b - C (-1) - C (8 * a * b) * X = X ^ 2 * coefP1 a b := by
  unfold coefP1 P1x
  simp only [Polynomial.C_neg, Polynomial.C_1]
  ring

lemma P2x_eq_X_mul (a b : ℚ) : P2x a b = X * coefP2a a b := by
  unfold coefP2a P2x
  ring

lemma coefP2a_sub (a b : ℚ) :
    coefP2a a b - C (-1) - C (4 * a * b) * X = X ^ 2 * coefP2b a b := by
  unfold coefP2b coefP2a Q4x
  simp only [Polynomial.C_neg, Polynomial.C_1]
  ring

lemma coefP2a_coeff_zero (a b : ℚ) : (coefP2a a b).coeff 0 ≠ 0 := by
  rw [coeff_zero_eq_eval_zero]
  unfold coefP2a Q4x
  norm_num

/-! ## The three `P`-cases -/

lemma lead2_P0Q (a b : ℚ) (hA : AdmQ a b) :
    Lead2At (P0Q a b) 0 (a * b) (1 - 3 * a ^ 2 - 3 * b ^ 2) := by
  have hab : a * b ≠ 0 := by
    have ha : 0 < a := lt_of_lt_of_le (by norm_num) hA.1
    have hb : 0 < b := lt_trans ha hA.2.1
    exact mul_ne_zero (ne_of_gt ha) (ne_of_gt hb)
  refine lead2At_of_eq (P0Q a b) 0 (a * b) (1 - 3 * a ^ 2 - 3 * b ^ 2) hab
    (g := algP (coefP0 a b)) (reg_algebraMap_local_tools _) ?_
  simp only [neg_zero, zpow_zero, mul_one]
  rw [P0Q, xQ_eq_algP, algQ_eq_algP (a * b), algQ_eq_algP (1 - 3 * a ^ 2 - 3 * b ^ 2)]
  simp only [← map_mul, ← map_sub, ← map_pow, ← map_add]
  rw [algP_inj_iff, P0x_sub]

lemma lead2_P1Q (a b : ℚ) :
    Lead2At (P1Q a b) 0 (-1) (8 * a * b) := by
  refine lead2At_of_eq (P1Q a b) 0 (-1) (8 * a * b) (by norm_num)
    (g := algP (coefP1 a b)) (reg_algebraMap_local_tools _) ?_
  simp only [neg_zero, zpow_zero, mul_one]
  rw [P1Q, xQ_eq_algP, algQ_eq_algP (-1), algQ_eq_algP (8 * a * b)]
  simp only [← map_mul, ← map_sub, ← map_pow, ← map_add]
  rw [algP_inj_iff, P1x_sub]

lemma lead2_P2Q (a b : ℚ) :
    Lead2At (P2Q a b) 1 (-1) (4 * a * b) := by
  have hP2 : P2Q a b = xQ * algP (coefP2a a b) := by
    rw [P2Q, P2x_eq_X_mul, map_mul, xQ_eq_algP]
  have hcan : algP (Polynomial.X : Polynomial ℚ) * algP (coefP2a a b)
      * (algP (Polynomial.X : Polynomial ℚ))⁻¹ = algP (coefP2a a b) := by
    rw [mul_assoc, mul_comm (algP (coefP2a a b)) (algP (Polynomial.X : Polynomial ℚ))⁻¹,
      ← mul_assoc, mul_inv_cancel₀ (algP_ne_zero Polynomial.X_ne_zero), one_mul]
  refine lead2At_of_eq (P2Q a b) 1 (-1) (4 * a * b) (by norm_num)
    (g := algP (coefP2b a b)) (reg_algebraMap_local_tools _) ?_
  rw [zpow_neg_one, hP2, algQ_eq_algP (-1), algQ_eq_algP (4 * a * b), xQ_eq_algP, hcan]
  simp only [← map_mul, ← map_sub, ← map_pow, ← map_add]
  rw [algP_inj_iff, coefP2a_sub]

/-! ## `rhoQ` and its derivative -/

lemma two_eq_algP_P : (2 : RatFunc ℚ) = algP (2 : Polynomial ℚ) :=
  (map_natCast (algebraMap (Polynomial ℚ) (RatFunc ℚ)) 2).symm

lemma rhoQ_eq_algP :
    (rhoQ : RatFunc ℚ) = algP ((Polynomial.X - 1) ^ 2)
      / algP (Polynomial.X ^ 2 - 2 * Polynomial.X) := by
  have e1 : (algP (Polynomial.X : Polynomial ℚ) - 1) ^ 2 = algP ((Polynomial.X - 1) ^ 2) := by
    rw [show algP (Polynomial.X : Polynomial ℚ) - 1 = algP (Polynomial.X - 1) from by
          rw [← map_one (algebraMap (Polynomial ℚ) (RatFunc ℚ)), ← map_sub],
      ← map_pow]
  have e2 : algP (Polynomial.X : Polynomial ℚ) ^ 2 - 2 * algP (Polynomial.X : Polynomial ℚ)
      = algP (Polynomial.X ^ 2 - 2 * Polynomial.X) := by
    rw [← map_pow, two_eq_algP_P, ← map_mul, ← map_sub]
  rw [rhoQ, xQ_eq_algP, e1, e2]

lemma xQ_sub_two_eq_algP :
    (xQ - 2 : RatFunc ℚ) = algP (Polynomial.X - 2 : Polynomial ℚ) := by
  rw [two_eq_algP_P, xQ_eq_algP, ← map_sub]

lemma coeff_X_sub_two : (Polynomial.X - 2 : Polynomial ℚ).coeff 0 ≠ 0 := by
  rw [coeff_zero_eq_eval_zero]
  norm_num

lemma xQ_sub_two_ne_zero : (xQ - 2 : RatFunc ℚ) ≠ 0 := by
  rw [xQ_sub_two_eq_algP]
  exact algP_ne_zero (fun h => coeff_X_sub_two (by rw [h, Polynomial.coeff_zero]))

lemma reg_div_xQ_sub_two_sq : Reg ((-1/2 : RatFunc ℚ) / (xQ - 2) ^ 2) := by
  have hconv : (-1/2 : RatFunc ℚ) / (xQ - 2) ^ 2
      = algP (Polynomial.C (-1/2)) / algP ((Polynomial.X - 2) ^ 2) := by
    rw [show (-1/2 : RatFunc ℚ) = algP (Polynomial.C (-1/2)) by
          rw [show (-1/2 : RatFunc ℚ) = algebraMap ℚ (RatFunc ℚ) (-1/2) by norm_num,
            algQ_eq_algP],
      show ((xQ - 2 : RatFunc ℚ)) ^ 2 = algP ((Polynomial.X - 2) ^ 2) by
        rw [xQ_sub_two_eq_algP, ← map_pow]]
  rw [hconv]
  exact reg_div_algebraMap_local_tools (by rw [coeff_zero_eq_eval_zero]; norm_num)

lemma dRat_rhoQ_eq_xQ :
    Submission.CDT.dRat rhoQ = -(2 : RatFunc ℚ) * (xQ - 1) / (xQ ^ 2 - 2 * xQ) ^ 2 := by
  have hnum : ((Polynomial.X - 1 : Polynomial ℚ) ^ 2).derivative
        * (Polynomial.X ^ 2 - 2 * Polynomial.X : Polynomial ℚ)
      - (Polynomial.X - 1 : Polynomial ℚ) ^ 2
        * (Polynomial.X ^ 2 - 2 * Polynomial.X : Polynomial ℚ).derivative
      = -(2 : Polynomial ℚ) * (Polynomial.X - 1) := by
    have h1 : (Polynomial.X - 1 : Polynomial ℚ) ^ 2
        = (Polynomial.X - 1) * (Polynomial.X - 1) := by ring
    have h2 : (Polynomial.X ^ 2 - 2 * Polynomial.X : Polynomial ℚ)
        = Polynomial.X * Polynomial.X - 2 * Polynomial.X := by ring
    rw [h1, h2]
    simp only [Polynomial.derivative_sub, Polynomial.derivative_mul, Polynomial.derivative_X,
      Polynomial.derivative_one, Polynomial.derivative_natCast, Polynomial.derivative_ofNat,
      Polynomial.derivative_C, Polynomial.derivative_add]
    ring
  have hden : (Polynomial.X ^ 2 - 2 * Polynomial.X : Polynomial ℚ) ^ 2
      = (Polynomial.X - 2) ^ 2 * Polynomial.X ^ 2 := by ring
  rw [rhoQ_eq_algP, Submission.CDT.dRat_div, ← map_pow, hnum, hden]
  congr 1
  · rw [map_mul, map_neg, map_sub, map_one, ← two_eq_algP_P, xQ_eq_algP]
  · rw [map_mul, map_pow, map_pow, map_sub, ← two_eq_algP_P, xQ_eq_algP]
    ring

lemma lead2_dRat_rhoQ_base : Lead2At (Submission.CDT.dRat rhoQ) (-2) (1/2) 0 := by
  have hx2 : (xQ - 2 : RatFunc ℚ) ≠ 0 := xQ_sub_two_ne_zero
  have hfac : (xQ : RatFunc ℚ) ^ 2 - 2 * xQ = xQ * (xQ - 2) := by ring
  have hxn : (xQ : RatFunc ℚ) ^ 2 - 2 * xQ ≠ 0 := by
    rw [hfac]; exact mul_ne_zero xQ_ne_zero_local_tools hx2
  have hxn2 : ((xQ : RatFunc ℚ) ^ 2 - 2 * xQ) ^ 2 ≠ 0 := pow_ne_zero 2 hxn
  have hx2sq : ((xQ : RatFunc ℚ) - 2) ^ 2 ≠ 0 := pow_ne_zero 2 hx2
  refine lead2At_of_eq (Submission.CDT.dRat rhoQ) (-2) (1/2) 0 (by norm_num)
    (g := (-1/2 : RatFunc ℚ) / (xQ - 2) ^ 2) reg_div_xQ_sub_two_sq ?_
  simp only [neg_neg, map_zero, zero_mul, sub_zero]
  rw [dRat_rhoQ_eq_xQ,
    show (algebraMap ℚ (RatFunc ℚ) (1/2)) = (1/2 : RatFunc ℚ) by norm_num]
  field_simp [xQ_ne_zero_local_tools, hx2, hxn, hxn2, hx2sq]
  ring

/-! ## The target lemma -/

theorem local_base (a b : ℚ) (hA : AdmQ a b) :
    Lead2At rhoQ (-1) (-1/2) (3/4) ∧
    Lead2At (Submission.CDT.dRat rhoQ) (-2) (1/2) 0 ∧
    Lead2At (P0Q a b) 0 (a * b) (1 - 3 * a ^ 2 - 3 * b ^ 2) ∧
    Lead2At (P1Q a b) 0 (-1) (8 * a * b) ∧
    Lead2At (P2Q a b) 1 (-1) (4 * a * b) ∧
    Lead2At (P1Q a b / P2Q a b) (-1) 1 (-4 * a * b) :=
  ⟨lead2_rhoQ, lead2_dRat_rhoQ_base, lead2_P0Q a b hA, lead2_P1Q a b, lead2_P2Q a b,
    lead2_ratio a b⟩

end

end Work.C17
