import Mathlib
import Submission.Work.FIArea4.A4varbounds
import Submission.Work.FIArea4.sum_rpow_two_pow_le

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Work.FIArea4.Vflip

open Finset
open scoped BigOperators

/-!
# The dyadic sum of the bracket `p14T12` of Proposition 12.1

We show that the double dyadic sum
`∑_{j ≤ JR} ∑_{k ≤ JS} L(D, 2^j, 2^k)` is bounded by a constant times `L(D,R,S)`,
uniformly in all parameters, provided `2^JR ≤ 2R`, `2^JS ≤ 2S` and `D ≤ R·S`
(the standing hypothesis of Proposition 12.1).

The proof is term-by-term.  Writing `L(D,R,S) = T₁ + T₂ + T₃ + T₄ + T₅` with
`T₁ = D`, `T₂ = D^{1/3}(RS)^{2/3}(log 2RS + 1)^4`,
`T₃ = D⁻¹(RS)^{3/2}(RS)^ε`, `T₄ = R S^{3/4}(RS)^ε`, `T₅ = S R^{3/4}(RS)^ε`,
each monomial of `L(D,2^j,2^k)` is bounded by a product of a function of `j` and a
function of `k`; summing with `sum_rpow_two_pow_le` (the geometric dyadic bound) gives
a constant multiple of the corresponding `Tᵢ`.  The constant `T₁ = D` is handled by
noting `(JR+1)(JS+1) ≤ 4(log 2RS + 1)²` (geometric growth vs. logarithm) and `D ≤ RS`.
-/

/-- `log 2 < 1`. -/
private lemma log_two_lt_one : Real.log 2 < 1 := by
  have h := Real.log_lt_sub_one_of_pos (show (0:ℝ) < 2 by norm_num) (by norm_num)
  linarith

/-- `1 ≤ a → 1 ≤ b → 1 ≤ a*b` for reals (avoiding the missing `MulLeftMono ℝ`). -/
private lemma one_le_mulR {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b := by
  have := mul_le_mul ha hb (by norm_num : (0:ℝ) ≤ 1) (by linarith : (0:ℝ) ≤ a)
  simpa using this

/-- `log 8 ≤ 3`. -/
private lemma log_eight_le_three : Real.log 8 ≤ 3 := by
  have h : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]
    norm_num
  rw [h]
  have := log_two_lt_one
  linarith

/-- `(2R)^c (2S)^c = 4^c (RS)^c`. -/
private lemma rpow_split2 (R S : ℕ) (c : ℝ) :
    (2*(R:ℝ))^c * (2*(S:ℝ))^c = (4:ℝ)^c * ((R:ℝ)*(S:ℝ))^c := by
  rw [← Real.mul_rpow (by positivity) (by positivity)]
  rw [show (2*(R:ℝ))*(2*(S:ℝ)) = 4*((R:ℝ)*(S:ℝ)) by ring]
  rw [Real.mul_rpow (by norm_num) (by positivity)]

/-- `(4RS)^ε = 4^ε (RS)^ε`. -/
private lemma four_mul_rpow (R S : ℕ) (ε : ℝ) :
    (4*(R:ℝ)*(S:ℝ))^ε = (4:ℝ)^ε * ((R:ℝ)*(S:ℝ))^ε := by
  rw [show (4:ℝ)*(R:ℝ)*(S:ℝ) = 4*((R:ℝ)*(S:ℝ)) by ring]
  rw [Real.mul_rpow (by norm_num) (by positivity)]

/-- `log (2·2^j·2^k) + 1 ≤ 4(log (2RS) + 1)` when `2^j ≤ 2R`, `2^k ≤ 2S`, `R,S ≥ 1`. -/
private lemma log_dyadic_le (R S j k : ℕ) (hR : 1 ≤ R) (hS : 1 ≤ S)
    (hj : (2:ℝ)^j ≤ 2*(R:ℝ)) (hk : (2:ℝ)^k ≤ 2*(S:ℝ)) :
    Real.log (2 * (2:ℝ)^j * (2:ℝ)^k) + 1
      ≤ 4 * (Real.log (2*(R:ℝ)*(S:ℝ)) + 1) := by
  have hR0 : (0:ℝ) < (R:ℝ) := by exact_mod_cast (by omega : 0 < R)
  have hS0 : (0:ℝ) < (S:ℝ) := by exact_mod_cast (by omega : 0 < S)
  have hR1 : (1:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
  have hS1 : (1:ℝ) ≤ (S:ℝ) := by exact_mod_cast hS
  have hRS : (0:ℝ) < (R:ℝ)*(S:ℝ) := mul_pos hR0 hS0
  have hbase : (0:ℝ) < 2 * (2:ℝ)^j * (2:ℝ)^k := by positivity
  have hab : 2 * (2:ℝ)^j * (2:ℝ)^k ≤ 8*(R:ℝ)*(S:ℝ) := by
    have h1 : (2:ℝ)^j * (2:ℝ)^k ≤ (2*(R:ℝ))*(2*(S:ℝ)) :=
      mul_le_mul hj hk (by positivity) (by positivity)
    nlinarith [h1]
  have hlog1 := Real.log_le_log hbase hab
  have hlog8 : Real.log (8*(R:ℝ)*(S:ℝ)) = Real.log 8 + Real.log ((R:ℝ)*(S:ℝ)) := by
    rw [show (8:ℝ)*(R:ℝ)*(S:ℝ) = 8*((R:ℝ)*(S:ℝ)) by ring,
        Real.log_mul (by norm_num) (ne_of_gt hRS)]
  have hlogRS : Real.log ((R:ℝ)*(S:ℝ)) ≤ Real.log (2*(R:ℝ)*(S:ℝ)) :=
    Real.log_le_log hRS (by nlinarith [hRS])
  have hlog2RS : (0:ℝ) ≤ Real.log (2*(R:ℝ)*(S:ℝ)) := by
    apply Real.log_nonneg
    have hRS1 : (1:ℝ) ≤ (R:ℝ)*(S:ℝ) := one_le_mulR hR1 hS1
    nlinarith [hRS1]
  linarith [hlog1, hlog8, hlogRS, hlog2RS, log_eight_le_three]

/-- `n + 1 ≤ 2(log (2X) + 1)` when `2^n ≤ 2X` and `X ≥ 1`. -/
private lemma succ_le_log (n X : ℕ) (hX : 1 ≤ X) (h : (2:ℝ)^n ≤ 2*(X:ℝ)) :
    (n:ℝ) + 1 ≤ 2*(Real.log (2*(X:ℝ)) + 1) := by
  have hX0 : (0:ℝ) < (X:ℝ) := by exact_mod_cast (by omega : 0 < X)
  have h2n : (0:ℝ) < (2:ℝ)^n := by positivity
  have h2X : (0:ℝ) < 2*(X:ℝ) := by linarith
  have hlog := Real.log_le_log h2n h
  rw [Real.log_pow] at hlog
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hhalf : (1/2:ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hX1 : (1:ℝ) ≤ (X:ℝ) := by exact_mod_cast hX
  have hL0 : (0:ℝ) ≤ Real.log (2*(X:ℝ)) := Real.log_nonneg (by linarith [hX1])
  have hn : (n:ℝ) ≤ Real.log (2*(X:ℝ)) / Real.log 2 := by
    rw [le_div_iff₀ hlog2]; exact hlog
  have hdiv : Real.log (2*(X:ℝ)) / Real.log 2 ≤ 2 * Real.log (2*(X:ℝ)) := by
    rw [div_le_iff₀ hlog2]
    nlinarith [hL0, hhalf]
  linarith

/-- `D ≤ D^{1/3}(RS)^{2/3}` when `D ≤ RS`. -/
private lemma self_le_rpow (D R S : ℕ) (hD : 1 ≤ D) (hDRS : D ≤ R*S) :
    (D:ℝ) ≤ (D:ℝ)^((1:ℝ)/3) * ((R:ℝ)*(S:ℝ))^((2:ℝ)/3) := by
  have hDRS' : (D:ℝ) ≤ (R:ℝ)*(S:ℝ) := by exact_mod_cast hDRS
  have hD0 : (0:ℝ) ≤ (D:ℝ) := Nat.cast_nonneg D
  have hDpos : (0:ℝ) < (D:ℝ) := by exact_mod_cast (by omega : 0 < D)
  have hDsplit : (D:ℝ)^((2:ℝ)/3) * (D:ℝ)^((1:ℝ)/3) = (D:ℝ) := by
    rw [← Real.rpow_add hDpos]
    rw [show (2:ℝ)/3 + (1:ℝ)/3 = 1 by norm_num, Real.rpow_one]
  calc (D:ℝ) = (D:ℝ)^((2:ℝ)/3) * (D:ℝ)^((1:ℝ)/3) := hDsplit.symm
    _ ≤ ((R:ℝ)*(S:ℝ))^((2:ℝ)/3) * (D:ℝ)^((1:ℝ)/3) :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hD0 hDRS' (by norm_num))
          (Real.rpow_nonneg hD0 _)
    _ = (D:ℝ)^((1:ℝ)/3) * ((R:ℝ)*(S:ℝ))^((2:ℝ)/3) := by ring

/-- Per-term bound for the dyadic summation of `p14T12`. -/
private lemma dyadic_term_le (D R S j k : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hR : 1 ≤ R) (hS : 1 ≤ S)
    (hj : (2:ℝ)^j ≤ 2*(R:ℝ)) (hk : (2:ℝ)^k ≤ 2*(S:ℝ)) :
    Work.FIArea4.p14T12 D ((2:ℕ)^j) ((2:ℕ)^k) ε
      ≤ (D:ℝ)
        + (4*(Real.log (2*(R:ℝ)*(S:ℝ)) + 1))^4
            * ((D:ℝ)^((1:ℝ)/3) * ((2:ℝ)^j)^((2:ℝ)/3)) * ((2:ℝ)^k)^((2:ℝ)/3)
        + ((4*(R:ℝ)*(S:ℝ))^ε)
            * ((D:ℝ)⁻¹ * ((2:ℝ)^j)^((3:ℝ)/2)) * ((2:ℝ)^k)^((3:ℝ)/2)
        + ((4*(R:ℝ)*(S:ℝ))^ε) * ((2:ℝ)^j) * ((2:ℝ)^k)^((3:ℝ)/4)
        + ((4*(R:ℝ)*(S:ℝ))^ε) * ((2:ℝ)^j)^((3:ℝ)/4) * ((2:ℝ)^k) := by
  have ha : (0:ℝ) ≤ (2:ℝ)^j := by positivity
  have hb : (0:ℝ) ≤ (2:ℝ)^k := by positivity
  have hlog : Real.log (2 * (2:ℝ)^j * (2:ℝ)^k) + 1
      ≤ 4*(Real.log (2*(R:ℝ)*(S:ℝ)) + 1) := log_dyadic_le R S j k hR hS hj hk
  have hlog0 : (0:ℝ) ≤ Real.log (2 * (2:ℝ)^j * (2:ℝ)^k) + 1 := by
    have ha1 : (1:ℝ) ≤ (2:ℝ)^j := one_le_pow₀ (show (1:ℝ) ≤ 2 by norm_num)
    have hb1 : (1:ℝ) ≤ (2:ℝ)^k := one_le_pow₀ (show (1:ℝ) ≤ 2 by norm_num)
    have h1 : (0:ℝ) ≤ Real.log (2 * (2:ℝ)^j * (2:ℝ)^k) := by
      apply Real.log_nonneg
      have h2 : (1:ℝ) ≤ (2:ℝ)^j * (2:ℝ)^k := one_le_mulR ha1 hb1
      nlinarith [h2]
    linarith
  have hlog4 : (Real.log (2 * (2:ℝ)^j * (2:ℝ)^k) + 1)^4
      ≤ (4*(Real.log (2*(R:ℝ)*(S:ℝ)) + 1))^4 := pow_le_pow_left₀ hlog0 hlog 4
  have hYle : ((2:ℝ)^j * (2:ℝ)^k)^ε ≤ (4*(R:ℝ)*(S:ℝ))^ε := by
    apply Real.rpow_le_rpow (by positivity) _ hε
    nlinarith [hj, hk]
  have hs23 : ((2:ℝ)^j * (2:ℝ)^k)^((2:ℝ)/3)
      = ((2:ℝ)^j)^((2:ℝ)/3) * ((2:ℝ)^k)^((2:ℝ)/3) := Real.mul_rpow ha hb
  have hs32 : ((2:ℝ)^j * (2:ℝ)^k)^((3:ℝ)/2)
      = ((2:ℝ)^j)^((3:ℝ)/2) * ((2:ℝ)^k)^((3:ℝ)/2) := Real.mul_rpow ha hb
  have hp1 : (D:ℝ)^((1:ℝ)/3) * ((2:ℝ)^j * (2:ℝ)^k)^((2:ℝ)/3)
        * (Real.log (2 * (2:ℝ)^j * (2:ℝ)^k) + 1)^4
      ≤ (4*(Real.log (2*(R:ℝ)*(S:ℝ)) + 1))^4
          * ((D:ℝ)^((1:ℝ)/3) * ((2:ℝ)^j)^((2:ℝ)/3)) * ((2:ℝ)^k)^((2:ℝ)/3) := by
    rw [hs23]
    have hnn : (0:ℝ) ≤ (D:ℝ)^((1:ℝ)/3) * (((2:ℝ)^j)^((2:ℝ)/3) * ((2:ℝ)^k)^((2:ℝ)/3)) := by
      positivity
    calc (D:ℝ)^((1:ℝ)/3) * (((2:ℝ)^j)^((2:ℝ)/3) * ((2:ℝ)^k)^((2:ℝ)/3))
            * (Real.log (2 * (2:ℝ)^j * (2:ℝ)^k) + 1)^4
        ≤ (D:ℝ)^((1:ℝ)/3) * (((2:ℝ)^j)^((2:ℝ)/3) * ((2:ℝ)^k)^((2:ℝ)/3))
            * (4*(Real.log (2*(R:ℝ)*(S:ℝ)) + 1))^4 :=
          mul_le_mul_of_nonneg_left hlog4 hnn
      _ = (4*(Real.log (2*(R:ℝ)*(S:ℝ)) + 1))^4
          * ((D:ℝ)^((1:ℝ)/3) * ((2:ℝ)^j)^((2:ℝ)/3)) * ((2:ℝ)^k)^((2:ℝ)/3) := by ring
  have hp3 : (D:ℝ)⁻¹ * ((2:ℝ)^j * (2:ℝ)^k)^((3:ℝ)/2) * ((2:ℝ)^j * (2:ℝ)^k)^ε
      ≤ (4*(R:ℝ)*(S:ℝ))^ε * ((D:ℝ)⁻¹ * ((2:ℝ)^j)^((3:ℝ)/2))
          * ((2:ℝ)^k)^((3:ℝ)/2) := by
    rw [hs32]
    have hnn : (0:ℝ) ≤ (D:ℝ)⁻¹ * (((2:ℝ)^j)^((3:ℝ)/2) * ((2:ℝ)^k)^((3:ℝ)/2)) := by
      positivity
    calc (D:ℝ)⁻¹ * (((2:ℝ)^j)^((3:ℝ)/2) * ((2:ℝ)^k)^((3:ℝ)/2))
            * ((2:ℝ)^j * (2:ℝ)^k)^ε
        ≤ (D:ℝ)⁻¹ * (((2:ℝ)^j)^((3:ℝ)/2) * ((2:ℝ)^k)^((3:ℝ)/2))
            * (4*(R:ℝ)*(S:ℝ))^ε := mul_le_mul_of_nonneg_left hYle hnn
      _ = (4*(R:ℝ)*(S:ℝ))^ε * ((D:ℝ)⁻¹ * ((2:ℝ)^j)^((3:ℝ)/2))
          * ((2:ℝ)^k)^((3:ℝ)/2) := by ring
  have hp4 : (2:ℝ)^j * ((2:ℝ)^k)^((3:ℝ)/4) * ((2:ℝ)^j * (2:ℝ)^k)^ε
      ≤ (4*(R:ℝ)*(S:ℝ))^ε * ((2:ℝ)^j) * ((2:ℝ)^k)^((3:ℝ)/4) := by
    have hnn : (0:ℝ) ≤ (2:ℝ)^j * ((2:ℝ)^k)^((3:ℝ)/4) := by positivity
    calc (2:ℝ)^j * ((2:ℝ)^k)^((3:ℝ)/4) * ((2:ℝ)^j * (2:ℝ)^k)^ε
        ≤ (2:ℝ)^j * ((2:ℝ)^k)^((3:ℝ)/4) * (4*(R:ℝ)*(S:ℝ))^ε :=
          mul_le_mul_of_nonneg_left hYle hnn
      _ = (4*(R:ℝ)*(S:ℝ))^ε * ((2:ℝ)^j) * ((2:ℝ)^k)^((3:ℝ)/4) := by ring
  have hp5 : (2:ℝ)^k * ((2:ℝ)^j)^((3:ℝ)/4) * ((2:ℝ)^j * (2:ℝ)^k)^ε
      ≤ (4*(R:ℝ)*(S:ℝ))^ε * ((2:ℝ)^j)^((3:ℝ)/4) * ((2:ℝ)^k) := by
    have hnn : (0:ℝ) ≤ (2:ℝ)^k * ((2:ℝ)^j)^((3:ℝ)/4) := by positivity
    calc (2:ℝ)^k * ((2:ℝ)^j)^((3:ℝ)/4) * ((2:ℝ)^j * (2:ℝ)^k)^ε
        ≤ (2:ℝ)^k * ((2:ℝ)^j)^((3:ℝ)/4) * (4*(R:ℝ)*(S:ℝ))^ε :=
          mul_le_mul_of_nonneg_left hYle hnn
      _ = (4*(R:ℝ)*(S:ℝ))^ε * ((2:ℝ)^j)^((3:ℝ)/4) * ((2:ℝ)^k) := by ring
  simp only [Work.FIArea4.p14T12, Nat.cast_pow, Nat.cast_ofNat]
  rw [add_mul, add_mul]
  linarith [hp1, hp3, hp4, hp5]

theorem p14T12_dyadic_sum_le (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D R S JR JS : ℕ), 1 ≤ D → 1 ≤ R → 1 ≤ S → D ≤ R * S →
        (2:ℕ)^JR ≤ 2*R → (2:ℕ)^JS ≤ 2*S →
        (∑ j ∈ Finset.range (JR+1), ∑ k ∈ Finset.range (JS+1),
          Work.FIArea4.p14T12 D ((2:ℕ)^j) ((2:ℕ)^k) ε)
          ≤ C * Work.FIArea4.p14T12 D R S ε := by
  have hε0 : (0:ℝ) ≤ ε := hε.le
  set c23 : ℝ := (2:ℝ)^((2:ℝ)/3) / ((2:ℝ)^((2:ℝ)/3) - 1) with hc23
  set c32 : ℝ := (2:ℝ)^((3:ℝ)/2) / ((2:ℝ)^((3:ℝ)/2) - 1) with hc32
  set c34 : ℝ := (2:ℝ)^((3:ℝ)/4) / ((2:ℝ)^((3:ℝ)/4) - 1) with hc34
  have hc23pos : 0 < c23 := by
    rw [hc23]
    refine div_pos (Real.rpow_pos_of_pos (by norm_num) _) ?_
    have h := Real.one_lt_rpow (show (1:ℝ) < 2 by norm_num)
      (show (0:ℝ) < (2:ℝ)/3 by norm_num)
    linarith
  have hc32pos : 0 < c32 := by
    rw [hc32]
    refine div_pos (Real.rpow_pos_of_pos (by norm_num) _) ?_
    have h := Real.one_lt_rpow (show (1:ℝ) < 2 by norm_num)
      (show (0:ℝ) < (3:ℝ)/2 by norm_num)
    linarith
  have hc34pos : 0 < c34 := by
    rw [hc34]
    refine div_pos (Real.rpow_pos_of_pos (by norm_num) _) ?_
    have h := Real.one_lt_rpow (show (1:ℝ) < 2 by norm_num)
      (show (0:ℝ) < (3:ℝ)/4 by norm_num)
    linarith
  set K2 : ℝ := c23^2 * (4:ℝ)^((2:ℝ)/3) * (4:ℝ)^4 with hK2
  set K3 : ℝ := c32^2 * (4:ℝ)^((3:ℝ)/2) * (4:ℝ)^ε with hK3
  set K4 : ℝ := c34 * 4 * (2:ℝ)^((3:ℝ)/4) * (4:ℝ)^ε with hK4
  have hK2pos : 0 < K2 := by
    rw [hK2]
    exact mul_pos (mul_pos (pow_pos hc23pos 2)
      (Real.rpow_pos_of_pos (by norm_num) _)) (pow_pos (by norm_num) 4)
  have hK3pos : 0 < K3 := by
    rw [hK3]
    exact mul_pos (mul_pos (pow_pos hc32pos 2)
      (Real.rpow_pos_of_pos (by norm_num) _)) (Real.rpow_pos_of_pos (by norm_num) _)
  have hK4pos : 0 < K4 := by
    rw [hK4]
    exact mul_pos (mul_pos (mul_pos hc34pos (by norm_num))
      (Real.rpow_pos_of_pos (by norm_num) _)) (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨4 + K2 + K3 + 2*K4, by linarith, ?_⟩
  intro D R S JR JS hD hR hS hDRS hJR hJS
  have hJR' : (2:ℝ)^JR ≤ 2*(R:ℝ) := by
    have h1 : ((2:ℕ)^JR : ℝ) ≤ ((2*R : ℕ) : ℝ) := by exact_mod_cast hJR
    simpa [Nat.cast_pow] using h1
  have hJS' : (2:ℝ)^JS ≤ 2*(S:ℝ) := by
    have h1 : ((2:ℕ)^JS : ℝ) ≤ ((2*S : ℕ) : ℝ) := by exact_mod_cast hJS
    simpa [Nat.cast_pow] using h1
  set L : ℝ := Real.log (2*(R:ℝ)*(S:ℝ)) + 1 with hL
  set Y : ℝ := (4*(R:ℝ)*(S:ℝ))^ε with hY
  set T2 : ℝ := (D:ℝ)^((1:ℝ)/3) * ((R:ℝ)*(S:ℝ))^((2:ℝ)/3) * L^4 with hT2
  set T3 : ℝ := (D:ℝ)⁻¹ * ((R:ℝ)*(S:ℝ))^((3:ℝ)/2) * ((R:ℝ)*(S:ℝ))^ε with hT3
  set T4 : ℝ := (R:ℝ) * (S:ℝ)^((3:ℝ)/4) * ((R:ℝ)*(S:ℝ))^ε with hT4
  set T5 : ℝ := (S:ℝ) * (R:ℝ)^((3:ℝ)/4) * ((R:ℝ)*(S:ℝ))^ε with hT5
  have hp14 : Work.FIArea4.p14T12 D R S ε = (D:ℝ) + T2 + T3 + T4 + T5 := by
    simp only [hT2, hT3, hT4, hT5, hL, Work.FIArea4.p14T12]
    ring
  -- per-term bound
  have hstep : (∑ j ∈ Finset.range (JR+1), ∑ k ∈ Finset.range (JS+1),
        Work.FIArea4.p14T12 D ((2:ℕ)^j) ((2:ℕ)^k) ε)
      ≤ ∑ j ∈ Finset.range (JR+1), ∑ k ∈ Finset.range (JS+1),
          ((D:ℝ)
            + (4*L)^4 * ((D:ℝ)^((1:ℝ)/3) * ((2:ℝ)^j)^((2:ℝ)/3)) * ((2:ℝ)^k)^((2:ℝ)/3)
            + Y * ((D:ℝ)⁻¹ * ((2:ℝ)^j)^((3:ℝ)/2)) * ((2:ℝ)^k)^((3:ℝ)/2)
            + Y * ((2:ℝ)^j) * ((2:ℝ)^k)^((3:ℝ)/4)
            + Y * ((2:ℝ)^j)^((3:ℝ)/4) * ((2:ℝ)^k)) := by
    apply Finset.sum_le_sum
    intro j hj
    apply Finset.sum_le_sum
    intro k hk
    have hj1 : (2:ℝ)^j ≤ 2*(R:ℝ) := by
      have hjle : j ≤ JR := by simp only [Finset.mem_range] at hj; omega
      calc (2:ℝ)^j ≤ (2:ℝ)^JR := pow_le_pow_right₀ (by norm_num) hjle
        _ ≤ 2*(R:ℝ) := hJR'
    have hk1 : (2:ℝ)^k ≤ 2*(S:ℝ) := by
      have hkle : k ≤ JS := by simp only [Finset.mem_range] at hk; omega
      calc (2:ℝ)^k ≤ (2:ℝ)^JS := pow_le_pow_right₀ (by norm_num) hkle
        _ ≤ 2*(S:ℝ) := hJS'
    simpa only [← hL, ← hY] using dyadic_term_le D R S j k ε hε0 hR hS hj1 hk1
  -- the dyadic sums
  set Fj23 : ℝ := ∑ j ∈ Finset.range (JR+1), ((2:ℝ)^j)^((2:ℝ)/3) with hFj23
  set Fj32 : ℝ := ∑ j ∈ Finset.range (JR+1), ((2:ℝ)^j)^((3:ℝ)/2) with hFj32
  set Fj1 : ℝ := ∑ j ∈ Finset.range (JR+1), (2:ℝ)^j with hFj1
  set Fj34 : ℝ := ∑ j ∈ Finset.range (JR+1), ((2:ℝ)^j)^((3:ℝ)/4) with hFj34
  set Fk23 : ℝ := ∑ k ∈ Finset.range (JS+1), ((2:ℝ)^k)^((2:ℝ)/3) with hFk23
  set Fk32 : ℝ := ∑ k ∈ Finset.range (JS+1), ((2:ℝ)^k)^((3:ℝ)/2) with hFk32
  set Fk1 : ℝ := ∑ k ∈ Finset.range (JS+1), (2:ℝ)^k with hFk1
  set Fk34 : ℝ := ∑ k ∈ Finset.range (JS+1), ((2:ℝ)^k)^((3:ℝ)/4) with hFk34
  have hFj23_le : Fj23 ≤ c23 * (2*(R:ℝ))^((2:ℝ)/3) := by
    rw [hFj23, hc23]
    exact sum_rpow_two_pow_le ((2:ℝ)/3) (by norm_num) JR R hJR'
  have hFj32_le : Fj32 ≤ c32 * (2*(R:ℝ))^((3:ℝ)/2) := by
    rw [hFj32, hc32]
    exact sum_rpow_two_pow_le ((3:ℝ)/2) (by norm_num) JR R hJR'
  have hFj34_le : Fj34 ≤ c34 * (2*(R:ℝ))^((3:ℝ)/4) := by
    rw [hFj34, hc34]
    exact sum_rpow_two_pow_le ((3:ℝ)/4) (by norm_num) JR R hJR'
  have hFj1_le : Fj1 ≤ 4*(R:ℝ) := by
    rw [hFj1]
    calc (∑ j ∈ Finset.range (JR+1), (2:ℝ)^j)
        = ∑ j ∈ Finset.range (JR+1), ((2:ℝ)^j)^(1:ℝ) := by simp
      _ ≤ ((2:ℝ)^(1:ℝ) / ((2:ℝ)^(1:ℝ) - 1)) * (2*(R:ℝ))^(1:ℝ) :=
            sum_rpow_two_pow_le 1 (by norm_num) JR R hJR'
      _ = 4*(R:ℝ) := by rw [Real.rpow_one, Real.rpow_one]; ring
  have hFk23_le : Fk23 ≤ c23 * (2*(S:ℝ))^((2:ℝ)/3) := by
    rw [hFk23, hc23]
    exact sum_rpow_two_pow_le ((2:ℝ)/3) (by norm_num) JS S hJS'
  have hFk32_le : Fk32 ≤ c32 * (2*(S:ℝ))^((3:ℝ)/2) := by
    rw [hFk32, hc32]
    exact sum_rpow_two_pow_le ((3:ℝ)/2) (by norm_num) JS S hJS'
  have hFk34_le : Fk34 ≤ c34 * (2*(S:ℝ))^((3:ℝ)/4) := by
    rw [hFk34, hc34]
    exact sum_rpow_two_pow_le ((3:ℝ)/4) (by norm_num) JS S hJS'
  have hFk1_le : Fk1 ≤ 4*(S:ℝ) := by
    rw [hFk1]
    calc (∑ k ∈ Finset.range (JS+1), (2:ℝ)^k)
        = ∑ k ∈ Finset.range (JS+1), ((2:ℝ)^k)^(1:ℝ) := by simp
      _ ≤ ((2:ℝ)^(1:ℝ) / ((2:ℝ)^(1:ℝ) - 1)) * (2*(S:ℝ))^(1:ℝ) :=
            sum_rpow_two_pow_le 1 (by norm_num) JS S hJS'
      _ = 4*(S:ℝ) := by rw [Real.rpow_one, Real.rpow_one]; ring
  -- factorization of the five pieces
  have hsumP1 : (∑ j ∈ Finset.range (JR+1), ∑ k ∈ Finset.range (JS+1), (D:ℝ))
      = ((JR:ℝ)+1)*((JS:ℝ)+1)*(D:ℝ) := by
    simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have hsumP2 : (∑ j ∈ Finset.range (JR+1), ∑ k ∈ Finset.range (JS+1),
        (4*L)^4 * ((D:ℝ)^((1:ℝ)/3) * ((2:ℝ)^j)^((2:ℝ)/3)) * ((2:ℝ)^k)^((2:ℝ)/3))
      = (4*L)^4 * ((D:ℝ)^((1:ℝ)/3) * Fj23) * Fk23 := by
    rw [hFj23, hFk23]
    rw [← Finset.sum_mul_sum]
    congr 1
    rw [← Finset.mul_sum, ← Finset.mul_sum]
  have hsumP3 : (∑ j ∈ Finset.range (JR+1), ∑ k ∈ Finset.range (JS+1),
        Y * ((D:ℝ)⁻¹ * ((2:ℝ)^j)^((3:ℝ)/2)) * ((2:ℝ)^k)^((3:ℝ)/2))
      = Y * ((D:ℝ)⁻¹ * Fj32) * Fk32 := by
    rw [hFj32, hFk32]
    rw [← Finset.sum_mul_sum]
    congr 1
    rw [← Finset.mul_sum, ← Finset.mul_sum]
  have hsumP4 : (∑ j ∈ Finset.range (JR+1), ∑ k ∈ Finset.range (JS+1),
        Y * ((2:ℝ)^j) * ((2:ℝ)^k)^((3:ℝ)/4))
      = Y * Fj1 * Fk34 := by
    rw [hFj1, hFk34]
    rw [← Finset.sum_mul_sum]
    congr 1
    rw [← Finset.mul_sum]
  have hsumP5 : (∑ j ∈ Finset.range (JR+1), ∑ k ∈ Finset.range (JS+1),
        Y * ((2:ℝ)^j)^((3:ℝ)/4) * ((2:ℝ)^k))
      = Y * Fj34 * Fk1 := by
    rw [hFj34, hFk1]
    rw [← Finset.sum_mul_sum]
    congr 1
    rw [← Finset.mul_sum]
  have hRsum : (∑ j ∈ Finset.range (JR+1), ∑ k ∈ Finset.range (JS+1),
        ((D:ℝ)
          + (4*L)^4 * ((D:ℝ)^((1:ℝ)/3) * ((2:ℝ)^j)^((2:ℝ)/3)) * ((2:ℝ)^k)^((2:ℝ)/3)
          + Y * ((D:ℝ)⁻¹ * ((2:ℝ)^j)^((3:ℝ)/2)) * ((2:ℝ)^k)^((3:ℝ)/2)
          + Y * ((2:ℝ)^j) * ((2:ℝ)^k)^((3:ℝ)/4)
          + Y * ((2:ℝ)^j)^((3:ℝ)/4) * ((2:ℝ)^k)))
      = ((JR:ℝ)+1)*((JS:ℝ)+1)*(D:ℝ)
        + (4*L)^4 * ((D:ℝ)^((1:ℝ)/3) * Fj23) * Fk23
        + Y * ((D:ℝ)⁻¹ * Fj32) * Fk32
        + Y * Fj1 * Fk34
        + Y * Fj34 * Fk1 := by
    simp only [Finset.sum_add_distrib]
    rw [hsumP1, hsumP2, hsumP3, hsumP4, hsumP5]
  -- bounds on the five pieces
  have hbP1 : ((JR:ℝ)+1) * ((JS:ℝ)+1) * (D:ℝ) ≤ 4 * T2 := by
    have hR0 : (0:ℝ) < (R:ℝ) := by exact_mod_cast (by omega : 0 < R)
    have hS0 : (0:ℝ) < (S:ℝ) := by exact_mod_cast (by omega : 0 < S)
    have hR1 : (1:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
    have hS1 : (1:ℝ) ≤ (S:ℝ) := by exact_mod_cast hS
    have hlogR_le : Real.log (2*(R:ℝ)) ≤ Real.log (2*(R:ℝ)*(S:ℝ)) := by
      apply Real.log_le_log (by positivity)
      nlinarith [hS1, hR0]
    have hlogS_le : Real.log (2*(S:ℝ)) ≤ Real.log (2*(R:ℝ)*(S:ℝ)) := by
      apply Real.log_le_log (by positivity)
      nlinarith [hR1, hS0]
    have hJRl : (JR:ℝ) + 1 ≤ 2*L := by
      have h1 := succ_le_log JR R hR hJR'
      rw [hL]; linarith
    have hJSl : (JS:ℝ) + 1 ≤ 2*L := by
      have h1 := succ_le_log JS S hS hJS'
      rw [hL]; linarith
    have hL1 : (1:ℝ) ≤ L := by
      rw [hL]
      have h2RS1 : (1:ℝ) ≤ 2*(R:ℝ)*(S:ℝ) := by
        have hRS1 : (1:ℝ) ≤ (R:ℝ)*(S:ℝ) :=
          one_le_mulR (by exact_mod_cast hR) (by exact_mod_cast hS)
        nlinarith [hRS1]
      have := Real.log_nonneg h2RS1
      linarith
    have hJRJS : ((JR:ℝ)+1) * ((JS:ℝ)+1) ≤ 4*L^2 := by
      have h2Ln : (0:ℝ) ≤ 2*L := by linarith [hL1]
      have h := mul_le_mul hJRl hJSl (by positivity) h2Ln
      nlinarith [h]
    have hDle : (D:ℝ) ≤ (D:ℝ)^((1:ℝ)/3) * ((R:ℝ)*(S:ℝ))^((2:ℝ)/3) :=
      self_le_rpow D R S hD hDRS
    have hLsq : L^2 ≤ L^4 := by
      have hL2ge1 : (1:ℝ) ≤ L^2 := one_le_pow₀ hL1
      calc L^2 = L^2 * 1 := by ring
        _ ≤ L^2 * L^2 := mul_le_mul_of_nonneg_left hL2ge1 (by positivity)
        _ = L^4 := by ring
    rw [hT2]
    have hkey : 4*L^2 * ((D:ℝ)^((1:ℝ)/3) * ((R:ℝ)*(S:ℝ))^((2:ℝ)/3))
        ≤ 4 * ((D:ℝ)^((1:ℝ)/3) * ((R:ℝ)*(S:ℝ))^((2:ℝ)/3) * L^4) := by
      have h := mul_le_mul_of_nonneg_left hLsq
        (by positivity : (0:ℝ) ≤ 4 * ((D:ℝ)^((1:ℝ)/3) * ((R:ℝ)*(S:ℝ))^((2:ℝ)/3)))
      nlinarith [h]
    calc ((JR:ℝ)+1) * ((JS:ℝ)+1) * (D:ℝ)
        ≤ 4*L^2 * (D:ℝ) := by
          have h := mul_le_mul_of_nonneg_right hJRJS (Nat.cast_nonneg D)
          nlinarith [h]
      _ ≤ 4*L^2 * ((D:ℝ)^((1:ℝ)/3) * ((R:ℝ)*(S:ℝ))^((2:ℝ)/3)) :=
          mul_le_mul_of_nonneg_left hDle (by positivity)
      _ ≤ 4 * ((D:ℝ)^((1:ℝ)/3) * ((R:ℝ)*(S:ℝ))^((2:ℝ)/3) * L^4) := hkey
  have hbP2 : (4*L)^4 * ((D:ℝ)^((1:ℝ)/3) * Fj23) * Fk23 ≤ K2 * T2 := by
    have hFknn : (0:ℝ) ≤ Fk23 := by
      rw [hFk23]; exact Finset.sum_nonneg (fun k _ => by positivity)
    have hD3 : (0:ℝ) ≤ (D:ℝ)^((1:ℝ)/3) := Real.rpow_nonneg (Nat.cast_nonneg D) _
    have hstepA : (4*L)^4 * ((D:ℝ)^((1:ℝ)/3) * Fj23) * Fk23
        ≤ (4*L)^4 * ((D:ℝ)^((1:ℝ)/3) * (c23*(2*(R:ℝ))^((2:ℝ)/3)))
            * (c23*(2*(S:ℝ))^((2:ℝ)/3)) := by
      have h1 : (D:ℝ)^((1:ℝ)/3) * Fj23
          ≤ (D:ℝ)^((1:ℝ)/3) * (c23*(2*(R:ℝ))^((2:ℝ)/3)) :=
        mul_le_mul_of_nonneg_left hFj23_le hD3
      have h2 : (4*L)^4 * ((D:ℝ)^((1:ℝ)/3) * Fj23)
          ≤ (4*L)^4 * ((D:ℝ)^((1:ℝ)/3) * (c23*(2*(R:ℝ))^((2:ℝ)/3))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      exact mul_le_mul h2 hFk23_le hFknn (by positivity)
    have hstepB : (4*L)^4 * ((D:ℝ)^((1:ℝ)/3) * (c23*(2*(R:ℝ))^((2:ℝ)/3)))
          * (c23*(2*(S:ℝ))^((2:ℝ)/3)) = K2 * T2 := by
      rw [show (4*L)^4 * ((D:ℝ)^((1:ℝ)/3) * (c23*(2*(R:ℝ))^((2:ℝ)/3)))
              * (c23*(2*(S:ℝ))^((2:ℝ)/3))
            = c23^2 * (4*L)^4
              * ((D:ℝ)^((1:ℝ)/3) * ((2*(R:ℝ))^((2:ℝ)/3) * (2*(S:ℝ))^((2:ℝ)/3))) by ring]
      rw [rpow_split2 R S ((2:ℝ)/3), hK2, hT2]
      ring
    linarith [hstepA, hstepB.le]
  have hbP3 : Y * ((D:ℝ)⁻¹ * Fj32) * Fk32 ≤ K3 * T3 := by
    have hFknn : (0:ℝ) ≤ Fk32 := by
      rw [hFk32]; exact Finset.sum_nonneg (fun k _ => by positivity)
    have hDinv : (0:ℝ) ≤ (D:ℝ)⁻¹ := by positivity
    have hYnn : (0:ℝ) ≤ Y := by rw [hY]; positivity
    have hstepA : Y * ((D:ℝ)⁻¹ * Fj32) * Fk32
        ≤ Y * ((D:ℝ)⁻¹ * (c32*(2*(R:ℝ))^((3:ℝ)/2)))
            * (c32*(2*(S:ℝ))^((3:ℝ)/2)) := by
      have h1 : (D:ℝ)⁻¹ * Fj32 ≤ (D:ℝ)⁻¹ * (c32*(2*(R:ℝ))^((3:ℝ)/2)) :=
        mul_le_mul_of_nonneg_left hFj32_le hDinv
      have h2 : Y * ((D:ℝ)⁻¹ * Fj32) ≤ Y * ((D:ℝ)⁻¹ * (c32*(2*(R:ℝ))^((3:ℝ)/2))) :=
        mul_le_mul_of_nonneg_left h1 hYnn
      exact mul_le_mul h2 hFk32_le hFknn (by positivity)
    have hY' : Y = (4:ℝ)^ε * ((R:ℝ)*(S:ℝ))^ε := by rw [hY, four_mul_rpow R S ε]
    have hstepB : Y * ((D:ℝ)⁻¹ * (c32*(2*(R:ℝ))^((3:ℝ)/2)))
          * (c32*(2*(S:ℝ))^((3:ℝ)/2)) = K3 * T3 := by
      rw [hY']
      rw [show (4:ℝ)^ε * ((R:ℝ)*(S:ℝ))^ε * ((D:ℝ)⁻¹ * (c32*(2*(R:ℝ))^((3:ℝ)/2)))
              * (c32*(2*(S:ℝ))^((3:ℝ)/2))
            = c32^2 * (4:ℝ)^ε * ((R:ℝ)*(S:ℝ))^ε * (D:ℝ)⁻¹
              * ((2*(R:ℝ))^((3:ℝ)/2) * (2*(S:ℝ))^((3:ℝ)/2)) by ring]
      rw [rpow_split2 R S ((3:ℝ)/2), hK3, hT3]
      ring
    linarith [hstepA, hstepB.le]
  have hbP4 : Y * Fj1 * Fk34 ≤ K4 * T4 := by
    have hFknn : (0:ℝ) ≤ Fk34 := by
      rw [hFk34]; exact Finset.sum_nonneg (fun k _ => by positivity)
    have hYnn : (0:ℝ) ≤ Y := by rw [hY]; positivity
    have hstepA : Y * Fj1 * Fk34 ≤ Y * (4*(R:ℝ)) * (c34*(2*(S:ℝ))^((3:ℝ)/4)) := by
      have h1 : Y * Fj1 ≤ Y * (4*(R:ℝ)) := mul_le_mul_of_nonneg_left hFj1_le hYnn
      exact mul_le_mul h1 hFk34_le hFknn (by positivity)
    have hY' : Y = (4:ℝ)^ε * ((R:ℝ)*(S:ℝ))^ε := by rw [hY, four_mul_rpow R S ε]
    have hstepB : Y * (4*(R:ℝ)) * (c34*(2*(S:ℝ))^((3:ℝ)/4)) = K4 * T4 := by
      rw [hY']
      rw [show (4:ℝ)^ε * ((R:ℝ)*(S:ℝ))^ε * (4*(R:ℝ)) * (c34*(2*(S:ℝ))^((3:ℝ)/4))
            = c34 * 4 * (4:ℝ)^ε * ((R:ℝ)*(S:ℝ))^ε * (R:ℝ)
              * (2*(S:ℝ))^((3:ℝ)/4) by ring]
      rw [Real.mul_rpow (show (0:ℝ) ≤ 2 by norm_num) (show (0:ℝ) ≤ (S:ℝ) by positivity),
          hK4, hT4]
      ring
    linarith [hstepA, hstepB.le]
  have hbP5 : Y * Fj34 * Fk1 ≤ K4 * T5 := by
    have hFknn : (0:ℝ) ≤ Fk1 := by
      rw [hFk1]; exact Finset.sum_nonneg (fun k _ => by positivity)
    have hYnn : (0:ℝ) ≤ Y := by rw [hY]; positivity
    have hstepA : Y * Fj34 * Fk1 ≤ Y * (c34*(2*(R:ℝ))^((3:ℝ)/4)) * (4*(S:ℝ)) := by
      have h1 : Y * Fj34 ≤ Y * (c34*(2*(R:ℝ))^((3:ℝ)/4)) :=
        mul_le_mul_of_nonneg_left hFj34_le hYnn
      exact mul_le_mul h1 hFk1_le hFknn (by positivity)
    have hY' : Y = (4:ℝ)^ε * ((R:ℝ)*(S:ℝ))^ε := by rw [hY, four_mul_rpow R S ε]
    have hstepB : Y * (c34*(2*(R:ℝ))^((3:ℝ)/4)) * (4*(S:ℝ)) = K4 * T5 := by
      rw [hY']
      rw [show (4:ℝ)^ε * ((R:ℝ)*(S:ℝ))^ε * (c34*(2*(R:ℝ))^((3:ℝ)/4)) * (4*(S:ℝ))
            = c34 * 4 * (4:ℝ)^ε * ((R:ℝ)*(S:ℝ))^ε * (S:ℝ)
              * (2*(R:ℝ))^((3:ℝ)/4) by ring]
      rw [Real.mul_rpow (show (0:ℝ) ≤ 2 by norm_num) (show (0:ℝ) ≤ (R:ℝ) by positivity),
          hK4, hT5]
      ring
    linarith [hstepA, hstepB.le]
  -- assemble
  have hchain : (∑ j ∈ Finset.range (JR+1), ∑ k ∈ Finset.range (JS+1),
        Work.FIArea4.p14T12 D ((2:ℕ)^j) ((2:ℕ)^k) ε)
      ≤ 4*T2 + K2*T2 + K3*T3 + K4*T4 + K4*T5 := by
    calc (∑ j ∈ Finset.range (JR+1), ∑ k ∈ Finset.range (JS+1),
          Work.FIArea4.p14T12 D ((2:ℕ)^j) ((2:ℕ)^k) ε)
        ≤ ∑ j ∈ Finset.range (JR+1), ∑ k ∈ Finset.range (JS+1),
            ((D:ℝ)
              + (4*L)^4 * ((D:ℝ)^((1:ℝ)/3) * ((2:ℝ)^j)^((2:ℝ)/3)) * ((2:ℝ)^k)^((2:ℝ)/3)
              + Y * ((D:ℝ)⁻¹ * ((2:ℝ)^j)^((3:ℝ)/2)) * ((2:ℝ)^k)^((3:ℝ)/2)
              + Y * ((2:ℝ)^j) * ((2:ℝ)^k)^((3:ℝ)/4)
              + Y * ((2:ℝ)^j)^((3:ℝ)/4) * ((2:ℝ)^k)) := hstep
      _ = ((JR:ℝ)+1)*((JS:ℝ)+1)*(D:ℝ)
            + (4*L)^4 * ((D:ℝ)^((1:ℝ)/3) * Fj23) * Fk23
            + Y * ((D:ℝ)⁻¹ * Fj32) * Fk32
            + Y * Fj1 * Fk34
            + Y * Fj34 * Fk1 := hRsum
      _ ≤ 4*T2 + K2*T2 + K3*T3 + K4*T4 + K4*T5 := by
            linarith [hbP1, hbP2, hbP3, hbP4, hbP5]
  have hT2nn : (0:ℝ) ≤ T2 := by rw [hT2]; positivity
  have hT3nn : (0:ℝ) ≤ T3 := by rw [hT3]; positivity
  have hT4nn : (0:ℝ) ≤ T4 := by rw [hT4]; positivity
  have hT5nn : (0:ℝ) ≤ T5 := by rw [hT5]; positivity
  have hfinal : 4*T2 + K2*T2 + K3*T3 + K4*T4 + K4*T5
      ≤ (4 + K2 + K3 + 2*K4) * ((D:ℝ) + T2 + T3 + T4 + T5) := by
    have hT1nn : (0:ℝ) ≤ (D:ℝ) := Nat.cast_nonneg D
    have hc0 : (0:ℝ) ≤ 4 + K2 + K3 + 2*K4 := by linarith [hK2pos, hK3pos, hK4pos]
    have e2 : 4*T2 + K2*T2 ≤ (4 + K2 + K3 + 2*K4) * T2 := by
      have h : (4 + K2) ≤ (4 + K2 + K3 + 2*K4) := by linarith [hK3pos, hK4pos]
      have h' := mul_le_mul_of_nonneg_right h hT2nn
      linarith [h']
    have e3 : K3*T3 ≤ (4 + K2 + K3 + 2*K4) * T3 := by
      have h : K3 ≤ (4 + K2 + K3 + 2*K4) := by linarith [hK2pos, hK4pos]
      exact mul_le_mul_of_nonneg_right h hT3nn
    have e4 : K4*T4 ≤ (4 + K2 + K3 + 2*K4) * T4 := by
      have h : K4 ≤ (4 + K2 + K3 + 2*K4) := by linarith [hK2pos, hK3pos]
      exact mul_le_mul_of_nonneg_right h hT4nn
    have e5 : K4*T5 ≤ (4 + K2 + K3 + 2*K4) * T5 := by
      have h : K4 ≤ (4 + K2 + K3 + 2*K4) := by linarith [hK2pos, hK3pos]
      exact mul_le_mul_of_nonneg_right h hT5nn
    have e1 : (0:ℝ) ≤ (4 + K2 + K3 + 2*K4) * (D:ℝ) := mul_nonneg hc0 hT1nn
    have hexp : (4 + K2 + K3 + 2*K4) * ((D:ℝ) + T2 + T3 + T4 + T5)
        = (4 + K2 + K3 + 2*K4)*(D:ℝ) + (4 + K2 + K3 + 2*K4)*T2
          + (4 + K2 + K3 + 2*K4)*T3 + (4 + K2 + K3 + 2*K4)*T4
          + (4 + K2 + K3 + 2*K4)*T5 := by ring
    rw [hexp]
    linarith [e1, e2, e3, e4, e5]
  calc (∑ j ∈ Finset.range (JR+1), ∑ k ∈ Finset.range (JS+1),
        Work.FIArea4.p14T12 D ((2:ℕ)^j) ((2:ℕ)^k) ε)
      ≤ 4*T2 + K2*T2 + K3*T3 + K4*T4 + K4*T5 := hchain
    _ ≤ (4 + K2 + K3 + 2*K4) * ((D:ℝ) + T2 + T3 + T4 + T5) := hfinal
    _ = (4 + K2 + K3 + 2*K4) * Work.FIArea4.p14T12 D R S ε := by rw [hp14]

end Work.FIArea4.Vflip
