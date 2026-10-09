import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Star
import Mathlib.RingTheory.Valuation.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.Nonarchimedean

open WithZero

/-- The order on the value group `ℤᵐ⁰` is compatible with `WithZero.exp`. -/
lemma val_exp_le_exp_iff {a b : ℤ} :
    (WithZero.exp a : WithZero (Multiplicative ℤ)) ≤ WithZero.exp b ↔ a ≤ b := by
  simp [WithZero.exp_eq_coe_ofAdd, Multiplicative.ofAdd_le]

/-- Every natural number has valuation at most `1` (the integers lie in the
valuation ring), since `n` is a sum of `n` copies of `1`. -/
lemma val_natCast_le_one {F : Type*} [Field F]
    (w : Valuation F (WithZero (Multiplicative ℤ))) (n : ℕ) : w (n : F) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_succ]
      calc w ((n : F) + 1) ≤ max (w (n : F)) (w 1) := w.map_add _ _
        _ = max (w (n : F)) 1 := by rw [Valuation.map_one]
        _ = 1 := max_eq_right ih

/-- Binomial expansion of `(1 + y) ^ m - 1`, with the `j = 0` term of the sum
the linear term `m * y`. -/
lemma val_pow_sub_one_binomial_split {F : Type*} [Field F] (y : F) {m : ℕ} (hm : 1 ≤ m) :
    (1 + y) ^ m - 1
      = (m : F) * y
        + ∑ k ∈ Finset.range (m - 1), y ^ (k + 2) * (Nat.choose m (k + 2) : F) := by
  have h : (1 + y) ^ m = ∑ k ∈ Finset.range m, y ^ (k + 1) * (Nat.choose m (k + 1) : F) + 1 := by
    rw [add_comm 1 y, add_pow]
    rw [Finset.sum_range_succ']
    simp
  rw [h, add_sub_cancel_right]
  conv_lhs => rw [show m = (m - 1) + 1 from (Nat.succ_pred_eq_of_pos (by omega)).symm]
  rw [Finset.sum_range_succ']
  rw [Nat.choose_one_right]
  have hm1 : (m - 1) + 1 = m := by omega
  simp only [hm1]
  ring

/-- One step of the iteration: if `w y ≤ exp (-t)` with `t ≥ 1` and
`w m ≤ exp (-1)`, then `w ((1 + y) ^ m - 1) ≤ exp (-(t + 1))`. -/
lemma val_pow_sub_one_step {F : Type*} [Field F]
    (w : Valuation F (WithZero (Multiplicative ℤ)))
    {m : ℕ} (hm1 : 1 ≤ m) (hm : w (m : F) ≤ WithZero.exp (-(1 : ℤ)))
    {y : F} {t : ℕ} (ht : 1 ≤ t) (hy : w y ≤ WithZero.exp (-(t : ℤ))) :
    w ((1 + y) ^ m - 1) ≤ WithZero.exp (-((t : ℤ) + 1)) := by
  have hC : ∀ k : ℕ, w ((Nat.choose m (k + 2) : ℕ) : F) ≤ 1 :=
    fun k => val_natCast_le_one w _
  have hmy : w ((m : F) * y) ≤ WithZero.exp (-((t : ℤ) + 1)) := by
    calc w ((m : F) * y) = w (m : F) * w y := by rw [Valuation.map_mul]
      _ ≤ WithZero.exp (-(1 : ℤ)) * WithZero.exp (-(t : ℤ)) := mul_le_mul' hm hy
      _ = WithZero.exp (-(1 : ℤ) + -(t : ℤ)) := (WithZero.exp_add _ _).symm
      _ = WithZero.exp (-((t : ℤ) + 1)) := by
            congr 1; ring
  have hrest : w (∑ k ∈ Finset.range (m - 1), y ^ (k + 2) * (Nat.choose m (k + 2) : F))
      ≤ WithZero.exp (-((t : ℤ) + 1)) := by
    apply Valuation.map_sum_le
    intro k hk
    have hk' : (0 : ℤ) ≤ (k : ℤ) := by positivity
    have ht' : (1 : ℤ) ≤ (t : ℤ) := by exact_mod_cast ht
    calc w (y ^ (k + 2) * (Nat.choose m (k + 2) : F))
        = w (y ^ (k + 2)) * w ((Nat.choose m (k + 2) : ℕ) : F) := by rw [Valuation.map_mul]
      _ = (w y) ^ (k + 2) * w ((Nat.choose m (k + 2) : ℕ) : F) := by rw [Valuation.map_pow]
      _ ≤ (w y) ^ (k + 2) * 1 := mul_le_mul_right (hC k) _
      _ = (w y) ^ (k + 2) := mul_one _
      _ ≤ (WithZero.exp (-(t : ℤ))) ^ (k + 2) := pow_le_pow_left' hy _
      _ = WithZero.exp ((k + 2) • (-(t : ℤ))) := (WithZero.exp_nsmul (k + 2) (-(t : ℤ))).symm
      _ ≤ WithZero.exp (-((t : ℤ) + 1)) := by
            apply val_exp_le_exp_iff.mpr
            simp only [nsmul_eq_mul]
            push_cast
            nlinarith [ht', hk']
  rw [val_pow_sub_one_binomial_split y hm1]
  calc w ((m : F) * y
        + ∑ k ∈ Finset.range (m - 1), y ^ (k + 2) * (Nat.choose m (k + 2) : F))
      ≤ max (w ((m : F) * y))
          (w (∑ k ∈ Finset.range (m - 1), y ^ (k + 2) * (Nat.choose m (k + 2) : F))) :=
        w.map_add _ _
    _ ≤ WithZero.exp (-((t : ℤ) + 1)) := max_le hmy hrest

theorem val_pow_sub_one_le_exp_neg {F : Type*} [Field F]
    (w : Valuation F (WithZero (Multiplicative ℤ)))
    {m : ℕ} (hm2 : 2 ≤ m) (hm : w (m : F) ≤ WithZero.exp (-(1 : ℤ)))
    {δ : F} (hδ : w δ ≤ WithZero.exp (-(1 : ℤ))) (k : ℕ) :
    w ((1 + δ) ^ (m ^ k) - 1) ≤ WithZero.exp (-((k : ℤ) + 1)) := by
  have hm1 : 1 ≤ m := by omega
  induction k with
  | zero => simpa using hδ
  | succ k ih =>
      have hkey : w ((1 + ((1 + δ) ^ (m ^ k) - 1)) ^ m - 1)
          ≤ WithZero.exp (-(((k + 1 : ℕ) : ℤ) + 1)) :=
        val_pow_sub_one_step w hm1 hm (t := k + 1) (by omega) ih
      have hbase : (1 : F) + ((1 + δ) ^ (m ^ k) - 1) = (1 + δ) ^ (m ^ k) := by ring
      rw [hbase] at hkey
      have hmm : m ^ (k + 1) = m ^ k * m := by rw [pow_succ]
      rw [← pow_mul, ← hmm] at hkey
      simpa using hkey

end Commons.Analysis.Nonarchimedean