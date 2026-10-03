import Mathlib
import Submission.Work.KMTPlan.A6.MZBlockZero
import Submission.Commons.Analysis.ExponentialSums.weyl_inequality


namespace Work.KMTPlan.A6

open Polynomial Finset
open scoped BigOperators

/-- The real evaluation of an integer polynomial at a natural number, in the two forms used
below: `((P.eval (u : ℤ) : ℤ) : ℝ)` and the evaluation of the image of `P` in `ℝ[X]`. -/
lemma eval_intCastR (P : Polynomial ℤ) (u : ℕ) :
    ((P.eval (u : ℤ) : ℤ) : ℝ) = (P.map (Int.castRingHom ℝ)).eval (u : ℝ) := by
  rw [Polynomial.eval_map, Polynomial.eval₂_at_natCast]
  exact congr_fun Int.coe_castRingHom _

/-- The sum of the arithmetic character over a period, written as a single exponential sum of a
real polynomial phase. -/
lemma arithFourierSum_eq_expSum (P : Polynomial ℤ) (q : ℕ) (m : ℤ) (θ : ℝ) :
    (∑ u ∈ Finset.range q, fourier (T := 1) (u : ℤ) ((θ : ℝ) : Work.Analysis.IonescuWainger.Circle)
        * fourier (T := 1) (P.eval (u : ℤ)) (((m : ℝ) / (q : ℝ) : ℝ) : Work.Analysis.IonescuWainger.Circle))
      = ∑ u ∈ Finset.range q, Complex.exp (↑(2 * Real.pi * (θ * (u : ℝ)
          + (m : ℝ) * (P.map (Int.castRingHom ℝ)).eval (u : ℝ) / (q : ℝ))) * Complex.I) := by
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [fourier_apply, fourier_apply, fourier_coe_apply', fourier_coe_apply', ← Complex.exp_add]
  apply congrArg Complex.exp
  have h1 : ((P.eval (u : ℤ) : ℤ) : ℂ)
      = (((P.map (Int.castRingHom ℝ)).eval (u : ℝ) : ℝ) : ℂ) := by
    rw [← eval_intCastR P u]
    simp
  rw [h1]
  push_cast
  ring

/-- The IW height of an arithmetic frequency is at most twice the order of the frequency. -/
lemma heightIndex_le_two_mul_addOrderOf {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {L : ℕ} {α : Work.Analysis.IonescuWainger.Circle}
    (hα : α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ L) :
    2 ^ Work.Analysis.IonescuWainger.iwHeightIndex ρ α ≤ 2 * addOrderOf α := by
  obtain ⟨q, hq, hqα⟩ := Work.Analysis.IonescuWainger.mem_iwArithFreqs.mp hα
  have htor : IsOfFinAddOrder α :=
    isOfFinAddOrder_iff_nsmul_eq_zero.mpr
      ⟨q, Work.Analysis.IonescuWainger.pos_of_mem_iwP hq, hqα⟩
  have hle : Work.Analysis.IonescuWainger.iwHeightIndex ρ α ≤ Nat.clog 2 (addOrderOf α) :=
    Nat.sInf_le ⟨addOrderOf α, Work.Analysis.IonescuWainger.addOrderOf_mem_iwP hρ hρ1 htor,
      addOrderOf_nsmul_eq_zero α⟩
  have ho : 0 < addOrderOf α := addOrderOf_pos_iff.mpr htor
  have h2 : 2 ^ Nat.clog 2 (addOrderOf α) ≤ 2 * addOrderOf α := by
    by_cases hgt : 1 < addOrderOf α
    · have hp := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hgt
      have hpos : 0 < Nat.clog 2 (addOrderOf α) := Nat.clog_pos (by norm_num) hgt
      calc 2 ^ Nat.clog 2 (addOrderOf α)
          = 2 ^ ((Nat.clog 2 (addOrderOf α)).pred + 1) :=
              (congrArg (fun k => (2:ℕ) ^ k) (Nat.succ_pred_eq_of_pos hpos)).symm
        _ = 2 * 2 ^ (Nat.clog 2 (addOrderOf α)).pred := by rw [pow_succ']
        _ ≤ 2 * addOrderOf α := Nat.mul_le_mul_left 2 (le_of_lt hp)
    · have h1 : addOrderOf α = 1 := by omega
      rw [h1, Nat.clog_one_right]
      norm_num
  calc 2 ^ Work.Analysis.IonescuWainger.iwHeightIndex ρ α
      ≤ 2 ^ Nat.clog 2 (addOrderOf α) := Nat.pow_le_pow_right (by norm_num) hle
    _ ≤ 2 * addOrderOf α := h2

/-- If `2 ^ h ≤ 2 * q` and `1 ≤ q` then `2 ^ (h - 1) ≤ q`. -/
lemma two_pow_pred_le_of_le_mul {h q : ℕ} (hq : 1 ≤ q) (hh : 2 ^ h ≤ 2 * q) :
    2 ^ (h - 1) ≤ q := by
  rcases Nat.eq_zero_or_pos h with h0 | hpos
  · subst h0
    simpa using hq
  · have hsucc : h - 1 + 1 = h := Nat.succ_pred_eq_of_pos hpos
    have hsplit : 2 ^ h = 2 * 2 ^ (h - 1) := by
      conv_lhs => rw [← hsucc]
      rw [pow_succ']
    rw [hsplit] at hh
    exact Nat.le_of_mul_le_mul_left hh (by norm_num)

end Work.KMTPlan.A6

namespace Work.KMTPlan.A6

open Polynomial Finset
open scoped BigOperators

end Work.KMTPlan.A6
