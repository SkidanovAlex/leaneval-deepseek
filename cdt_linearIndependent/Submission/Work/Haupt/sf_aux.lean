import Mathlib
import Submission.Work.Haupt.qp_defs

/-!
# Auxiliary `q`-Pochhammer algebra for the semi-finite sum
-/

open scoped BigOperators
open Filter Topology

namespace Work.Haupt

lemma qhalf_eq_pow (q : ℂ) (n : ℕ) : qhalf q n = q ^ (n * (n - 1) / 2) := by
  rw [qhalf, Finset.prod_pow_eq_pow_sum, Finset.sum_range_id]

lemma qhalf_mul_succ (q : ℂ) (m : ℕ) : qhalf q m * qhalf q (m+1) = q ^ (m*m) := by
  induction m with
  | zero => simp
  | succ k ih =>
    have h1 : qhalf q (k+1) * qhalf q (k+1+1) = (qhalf q k * qhalf q (k+1)) * q^(2*k+1) := by
      rw [qhalf_succ q (k+1), qhalf_succ q k]; ring
    rw [h1, ih, ← pow_add]
    congr 1
    ring

lemma qhalf_sq (q : ℂ) (j : ℕ) : qhalf q j * qhalf q j = q ^ (j * (j-1)) := by
  induction j with
  | zero => simp
  | succ i ih =>
    have h1 : qhalf q (i+1) * qhalf q (i+1) = (qhalf q i * qhalf q i) * q^(2*i) := by
      rw [qhalf_succ q i]; ring
    have harith : i * (i-1) + 2*i = (i+1) * ((i+1)-1) := by
      rcases i with _ | k
      · simp
      · simp only [Nat.succ_sub_one]; ring
    rw [h1, ih, ← pow_add, harith]

lemma qhalf_shift' (q : ℂ) (hq : q ≠ 0) (k : ℕ) : ∀ j : ℕ,
    qhalf q (j+k+1) * qhalf q j * q^(-(((j*(j+k) : ℕ) : ℤ))) = qhalf q (k+1) := by
  intro j
  induction j with
  | zero => simp
  | succ i ih =>
    have h1 : qhalf q (i+1+k+1) = qhalf q (i+k+1) * q^(i+k+1) := by
      rw [show i+1+k+1 = (i+k+1)+1 from by ring, qhalf_succ]
    have h2 : qhalf q (i+1) = qhalf q i * q^i := qhalf_succ q i
    have key : (q^(i+k+1) : ℂ) * q^i * q^(-(((i+1)*((i+1)+k) : ℕ) : ℤ))
        = q^(-(((i*(i+k) : ℕ) : ℤ))) := by
      rw [← zpow_natCast q (i+k+1), ← zpow_natCast q i, ← zpow_add₀ hq, ← zpow_add₀ hq]
      congr 1
      push_cast
      ring
    have step : (qhalf q (i+k+1) * q^(i+k+1)) * (qhalf q i * q^i)
          * q^(-(((i+1)*((i+1)+k) : ℕ) : ℤ))
        = (qhalf q (i+k+1) * qhalf q i) * (q^(i+k+1) * q^i
          * q^(-(((i+1)*((i+1)+k) : ℕ) : ℤ))) := by
      ring
    rw [h1, h2, step, key, ih]

lemma qhalf_shift (q : ℂ) (hq : q ≠ 0) (m k : ℕ) (hk : k ≤ m) :
    qhalf q (m+1) * qhalf q (m-k) * q^(-(((m*(m-k) : ℕ) : ℤ))) = qhalf q (k+1) := by
  have h := qhalf_shift' q hq k (m-k)
  have e1 : ((m-k)*(m-k+k) : ℕ) = m*(m-k) := by
    rw [Nat.sub_add_cancel hk, Nat.mul_comm]
  rw [show m-k+k+1 = m+1 from by omega, e1] at h
  exact h

/-! ## `qpNat` splitting -/

lemma qpNat_self_add (q : ℂ) (m n : ℕ) :
    qpNat q q (n+m) = qpNat q q m * qpNat (q^(m+1)) q n := by
  have h := qpNat_mul_qpNat q q m n
  rw [show q * q^m = q^(m+1) from by rw [pow_succ'], Nat.add_comm m n] at h
  exact h.symm

lemma qpNat_self_sub (q : ℂ) (m k : ℕ) (hk : k ≤ m) :
    qpNat q q m = qpNat q q (m-k) * qpNat (q^(m-k+1)) q k := by
  have h := qpNat_mul_qpNat q q (m-k) k
  rw [show q * q^(m-k) = q^(m-k+1) from by rw [pow_succ']] at h
  rw [Nat.sub_add_cancel hk] at h
  exact h.symm

/-! ## integer powers -/

lemma zpow_neg_mul_self (q : ℂ) (hq : q ≠ 0) (n : ℤ) : q^(-n) * q^n = 1 := by
  rw [zpow_neg, inv_mul_cancel₀]
  exact zpow_ne_zero n hq

lemma zpow_self_mul_neg (q : ℂ) (hq : q ≠ 0) (n : ℤ) : q^n * q^(-n) = 1 := by
  rw [mul_comm, zpow_neg_mul_self q hq]

lemma qhalf_ne_zero {q : ℂ} (hq : q ≠ 0) (n : ℕ) : qhalf q n ≠ 0 := by
  rw [qhalf]
  exact Finset.prod_ne_zero_iff.mpr (fun j _ => pow_ne_zero j hq)

end Work.Haupt
