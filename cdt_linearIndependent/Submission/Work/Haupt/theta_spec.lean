import Mathlib
import Submission.Work.Haupt.defs
import Submission.Work.Haupt.qp_defs

/-!
# Specialising the Jacobi triple product to `θ₄`

With nome `q = x²` and `z = -x`, the triple product

`∑_{n∈ℤ} q^{n(n-1)/2} z^n = (q;q)_∞ (-q/z;q)_∞ (-z;q)_∞`

reads `∑_{n∈ℤ} (-1)^n x^{n²} = ∏_n (1-x^{2(n+1)})(1-x^{2n+1})²`, i.e. `T4 x = T4prod x`.

Here we prove the term-by-term identification of the left hand side with `T4 x`
(`qhalfInt_tsum_eq_T4`) and the product identification of the right hand side with
`T4prod x` (`T4prod_eq_qpInf`), plus the value at `x = 0`.
-/

open scoped BigOperators
open Filter Topology

namespace Work.Haupt

/-- `qhalf (q^2) n = qhalf q n ^ 2`. -/
lemma qhalf_sq_pow2 (q : ℂ) (n : ℕ) : qhalf (q ^ 2) n = (qhalf q n) ^ 2 := by
  rw [qhalf, qhalf, ← Finset.prod_pow]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [← pow_mul, ← pow_mul, Nat.mul_comm]

/-- `(qhalf q n)^2 = q^(n(n-1))`. -/
lemma qhalf_sq_eq (q : ℂ) (n : ℕ) : (qhalf q n) ^ 2 = q ^ (n * (n - 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsub : n + 1 - 1 = n := Nat.add_sub_cancel n 1
    have h2 : (q ^ n) ^ 2 = q ^ (2 * n) := by rw [← pow_mul, Nat.mul_comm]
    have hexp : n * (n - 1) + 2 * n = (n + 1) * n := by
      cases n with
      | zero => simp
      | succ k => rw [show k + 1 - 1 = k from rfl]; ring
    rw [hsub]
    calc (qhalf q (n + 1)) ^ 2
        = (qhalf q n * q ^ n) ^ 2 := by rw [qhalf_succ]
      _ = (qhalf q n) ^ 2 * (q ^ n) ^ 2 := by rw [mul_pow]
      _ = q ^ (n * (n - 1)) * q ^ (2 * n) := by rw [ih, h2]
      _ = q ^ (n * (n - 1) + 2 * n) := by rw [← pow_add]
      _ = q ^ ((n + 1) * n) := by rw [hexp]

/-- `(((-1 : ℂ) ^ m))⁻¹ = (-1) ^ m`. -/
lemma inv_neg_one_pow (m : ℕ) : ((-1 : ℂ) ^ m)⁻¹ = (-1 : ℂ) ^ m := by
  rcases Nat.even_or_odd m with h | h
  · rw [h.neg_one_pow, inv_one]
  · rw [h.neg_one_pow, inv_neg, inv_one]

/-- Casting helper: `↑(m*(m-1)) = ↑m * (↑m - 1)` in `ℤ`. -/
lemma cast_mul_pred (m : ℕ) : ((m * (m - 1) : ℕ) : ℤ) = (m : ℤ) * ((m : ℤ) - 1) := by
  cases m with
  | zero => simp
  | succ k => rw [show k + 1 - 1 = k from rfl]; push_cast; ring

/-- Casting helper for the negative branch. -/
lemma cast_negSucc_mul_pred (k : ℕ) :
    (((k + 2) * ((k + 2) - 1) : ℕ) : ℤ) = (Int.negSucc k) * (Int.negSucc k - 1) := by
  have h : (k + 2) - 1 = k + 1 := by omega
  rw [h, Int.negSucc_eq]
  push_cast
  ring

/-- Integer version of `qhalf_sq`. -/
lemma qhalfInt_sq (q : ℂ) (n : ℤ) : qhalfInt (q ^ 2) n = (qhalfInt q n) ^ 2 := by
  match n with
  | (m : ℕ) => rw [qhalfInt_natCast, qhalfInt_natCast, qhalf_sq_pow2]
  | Int.negSucc k => rw [qhalfInt_negSucc, qhalfInt_negSucc, qhalf_sq_pow2]

/-- Integer version of `qhalf_sq_eq`: `(qhalfInt q n)^2 = q^{n(n-1)}`. -/
lemma qhalfInt_sq_eq (q : ℂ) (n : ℤ) : (qhalfInt q n) ^ 2 = q ^ (n * (n - 1)) := by
  match n with
  | (m : ℕ) => rw [qhalfInt_natCast, qhalf_sq_eq, ← zpow_natCast, cast_mul_pred]
  | Int.negSucc k => rw [qhalfInt_negSucc, qhalf_sq_eq, ← zpow_natCast, cast_negSucc_mul_pred]

/-- The key termwise identity: `q^{n(n-1)/2} z^n` with `q = x²`, `z = -x` equals `(-1)^n x^{n²}`. -/
lemma qhalfInt_mul_neg (x : ℂ) (hx : x ≠ 0) (n : ℤ) :
    qhalfInt (x ^ 2) n * (-x) ^ n = (-1) ^ n * x ^ (n ^ 2) := by
  have h3 : (-x) ^ n = (-1) ^ n * x ^ n := by
    rw [show -x = (-1 : ℂ) * x from by ring, mul_zpow]
  calc qhalfInt (x ^ 2) n * (-x) ^ n
      = (qhalfInt x n) ^ 2 * ((-1) ^ n * x ^ n) := by rw [qhalfInt_sq, h3]
    _ = (-1) ^ n * ((qhalfInt x n) ^ 2 * x ^ n) := by ring_nf
    _ = (-1) ^ n * (x ^ (n * (n - 1)) * x ^ n) := by rw [qhalfInt_sq_eq]
    _ = (-1) ^ n * x ^ (n * (n - 1) + n) := by rw [← zpow_add₀ hx]
    _ = (-1) ^ n * x ^ (n ^ 2) := by congr 1; ring

/-- The left hand side of the specialised triple product is `T4 x` (for `x ≠ 0`). -/
theorem qhalfInt_tsum_eq_T4 (x : ℂ) (hx : x ≠ 0) :
    (∑' n : ℤ, qhalfInt (x ^ 2) n * (-x) ^ n) = T4 x :=
  tsum_congr (fun n => qhalfInt_mul_neg x hx n)

/-- `T4 0 = 1`. -/
lemma T4_zero : T4 0 = 1 := by
  rw [T4, tsum_eq_single (0 : ℤ) (fun b hb => ?_)]
  · simp
  · have hb2 : b ^ 2 ≠ 0 := pow_ne_zero 2 hb
    have hnn : (0 : ℤ) ≤ b ^ 2 := sq_nonneg b
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hnn
    have hm0 : m ≠ 0 := by rintro rfl; simp at hm; omega
    rw [hm, zpow_natCast, zero_pow hm0, mul_zero]

/-- `T4prod 0 = 1`. -/
lemma T4prod_zero : T4prod 0 = 1 := by
  rw [T4prod]
  have h : (fun n : ℕ => (1 - (0:ℂ) ^ (2 * (n + 1))) * (1 - (0:ℂ) ^ (2 * n + 1)) ^ 2)
      = fun _ : ℕ => (1 : ℂ) := by
    funext n
    rw [zero_pow (by positivity : 2 * (n + 1) ≠ 0), zero_pow (by positivity : 2 * n + 1 ≠ 0)]
    norm_num
  rw [h, tprod_one]

/-- The right hand side of the specialised triple product is `T4prod x`. -/
theorem T4prod_eq_qpInf (x : ℂ) (hx : ‖x‖ < 1) :
    T4prod x = qpInf (x ^ 2) (x ^ 2) * qpInf x (x ^ 2) * qpInf x (x ^ 2) := by
  have hx2 : ‖x ^ 2‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg x) hx (by norm_num)
  have hs1 : Summable (fun n : ℕ => x ^ (2 * (n + 1))) := by
    have h : Summable (fun n : ℕ => (x ^ 2) ^ (n + 1)) :=
      (summable_nat_add_iff 1).2 (summable_geometric_of_norm_lt_one hx2)
    exact h.congr (fun n => by rw [pow_mul])
  have hs2 : Summable (fun n : ℕ => x ^ (2 * n + 1)) := by
    have h : Summable (fun n : ℕ => x * (x ^ 2) ^ n) :=
      (summable_geometric_of_norm_lt_one hx2).mul_left x
    exact h.congr (fun n => by rw [← pow_mul, ← pow_succ'])
  have mA2 : Multipliable (fun n : ℕ => 1 - x ^ (2 * (n + 1))) :=
    (Complex.multipliable_one_add_of_summable hs1.neg).congr (fun n => by simp [sub_eq_add_neg])
  have mD : Multipliable (fun n : ℕ => 1 - x ^ (2 * n + 1)) :=
    (Complex.multipliable_one_add_of_summable hs2.neg).congr (fun n => by simp [sub_eq_add_neg])
  have hT4 : T4prod x
      = (∏' n : ℕ, (1 - x ^ (2 * (n + 1)))) * (∏' n : ℕ, (1 - x ^ (2 * n + 1))) ^ 2 := by
    rw [T4prod, Multipliable.tprod_mul mA2 (mD.pow 2), mD.tprod_pow 2]
  have e1 : qpInf (x ^ 2) (x ^ 2) = ∏' n : ℕ, (1 - x ^ (2 * (n + 1))) := by
    rw [qpInf]
    refine tprod_congr (fun n => ?_)
    rw [← pow_succ', ← pow_mul]
  have e2 : qpInf x (x ^ 2) = ∏' n : ℕ, (1 - x ^ (2 * n + 1)) := by
    rw [qpInf]
    refine tprod_congr (fun n => ?_)
    rw [← pow_mul, ← pow_succ']
  rw [hT4, e1, e2, sq, mul_assoc]

end Work.Haupt
