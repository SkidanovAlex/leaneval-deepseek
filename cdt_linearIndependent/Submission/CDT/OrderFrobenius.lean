import Mathlib
import Submission.Commons.RingTheory.PowerSeries.order_iterate_derivative
import Submission.Commons.RingTheory.PowerSeries.order_finset_sum_eq_of_forall_lt

/-!
# Leading-term (Frobenius) calculus for polynomial-coefficient operators

This module builds the elementary "leading term" layer used by the
Frobenius/indicial analysis of a polynomial-coefficient linear differential
operator `L = Σ_{j ≤ m} Q_j · (d/dX)^j` acting on a formal power series `f`.

The main result is `order_sum_mul_iterate_derivative_eq`: if `j₀` is the
*unique* index minimizing `order(Q_j) + (order f - j)` (and `j₀ ≤ order f`),
then the order of `L(f)` is exactly `order(Q_{j₀}) + (order f - j₀)` — the
leading term of the sum is exactly the leading term of the term `j₀`.

All declarations are fully proved (no axioms, no `sorry`).
-/

noncomputable section

open scoped BigOperators

namespace Submission.CDT

/-- The `j`-th formal derivative lowers the order by at most `j`
(truncated at `0`). -/
theorem order_iterate_derivative_ge {K : Type*} [Field K] [CharZero K]
    (f : PowerSeries K) (j : ℕ) :
    PowerSeries.order f - (j : ℕ∞) ≤ PowerSeries.order ((PowerSeries.derivative (R := K))^[j] f) := by
  rcases eq_or_ne f 0 with rfl | hf
  · have hz : ((PowerSeries.derivative (R := K))^[j] (0 : PowerSeries K)) = 0 := by
      induction j with
      | zero => rfl
      | succ j ih => rw [Function.iterate_succ_apply', ih]; exact map_zero _
    rw [hz, PowerSeries.order_zero]
    exact le_top
  · obtain ⟨N, hN⟩ : ∃ N : ℕ, PowerSeries.order f = (N : ℕ∞) :=
      ⟨(PowerSeries.order f).toNat, by rw [PowerSeries.coe_toNat_order hf]⟩
    rw [hN]
    by_cases h : j ≤ N
    · rw [Commons.RingTheory.PowerSeries.order_iterate_derivative f j N hN h,
        ← ENat.natCast_sub]
    · have hc : ((N : ℕ∞) - (j : ℕ∞)) = 0 :=
        tsub_eq_zero_of_le (by exact_mod_cast (not_le.mp h).le)
      rw [hc]
      exact bot_le

/-- **The leading-term lemma.** If `j₀ ≤ m` is the unique index minimizing
`order (Q j) + (N - j)` over `j ≤ m` (where `N = order f`), and `j₀ ≤ N`,
then the polynomial-coefficient operator `Σ_{j ≤ m} Q_j (d/dX)^j` applied to
`f` has order exactly `order (Q j₀) + (N - j₀)`. -/
theorem order_sum_mul_iterate_derivative_eq {K : Type*} [Field K] [CharZero K]
    (f : PowerSeries K) (Q : ℕ → PowerSeries K) (m N j₀ : ℕ)
    (hN : PowerSeries.order f = (N : ℕ∞)) (hj₀ : j₀ ≤ m) (hj₀N : j₀ ≤ N)
    (hmin : ∀ j, j ≤ m → j ≠ j₀ →
      PowerSeries.order (Q j₀) + ((N - j₀ : ℕ) : ℕ∞)
        < PowerSeries.order (Q j) + ((N - j : ℕ) : ℕ∞)) :
    PowerSeries.order (∑ j ∈ Finset.range (m + 1),
        Q j * (PowerSeries.derivative (R := K))^[j] f)
      = PowerSeries.order (Q j₀) + ((N - j₀ : ℕ) : ℕ∞) := by
  have hkey : PowerSeries.order (Q j₀ * (PowerSeries.derivative (R := K))^[j₀] f)
      = PowerSeries.order (Q j₀) + ((N - j₀ : ℕ) : ℕ∞) := by
    rw [PowerSeries.order_mul,
      Commons.RingTheory.PowerSeries.order_iterate_derivative f j₀ N hN hj₀N]
  rw [← hkey]
  refine Commons.RingTheory.PowerSeries.order_finset_sum_eq_of_forall_lt
    (Finset.range (m + 1)) (fun j => Q j * (PowerSeries.derivative (R := K))^[j] f) j₀
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hj₀)) ?_
  intro j hj hji
  have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hge : PowerSeries.order (Q j) + ((N - j : ℕ) : ℕ∞)
      ≤ PowerSeries.order (Q j * (PowerSeries.derivative (R := K))^[j] f) := by
    rw [PowerSeries.order_mul]
    have h1 := order_iterate_derivative_ge f j
    have h2 : ((N - j : ℕ) : ℕ∞) = ((N : ℕ∞) - (j : ℕ∞)) := by
      by_cases h : j ≤ N
      · rw [ENat.natCast_sub]
      · have h0 : N - j = 0 := Nat.sub_eq_zero_of_le (not_le.mp h).le
        rw [h0, Nat.cast_zero]
        exact (tsub_eq_zero_of_le (by exact_mod_cast (not_le.mp h).le)).symm
    rw [h2, ← hN]
    exact add_le_add le_rfl h1
  rw [hkey]
  exact lt_of_lt_of_le (hmin j hjm hji) hge

/-- The polynomial-coefficient special case: `P : ℕ → K[X]` with
`order (P m) = 0` (equivalently `(P m).eval 0 ≠ 0`) and `m ≤ N = order f`. -/
theorem order_sum_poly_mul_iterate_derivative_eq {K : Type*} [Field K] [CharZero K]
    (f : PowerSeries K) (P : ℕ → Polynomial K) (m N : ℕ)
    (hN : PowerSeries.order f = (N : ℕ∞))
    (hP : PowerSeries.order ((P m : PowerSeries K)) = 0) (hmN : m ≤ N) :
    PowerSeries.order (∑ j ∈ Finset.range (m + 1),
        ((P j : Polynomial K) : PowerSeries K) * (PowerSeries.derivative (R := K))^[j] f)
      = ((N - m : ℕ) : ℕ∞) := by
  have hmain := order_sum_mul_iterate_derivative_eq f
    (fun j => ((P j : Polynomial K) : PowerSeries K)) m N m hN le_rfl hmN ?_
  · rw [hmain, hP, zero_add]
  · intro j hjm hjmne
    have hjm' : j < m := lt_of_le_of_ne hjm hjmne
    have hsub : N - m < N - j :=
      Nat.sub_lt_sub_left (lt_of_lt_of_le hjm' hmN) hjm'
    calc PowerSeries.order (((P m : Polynomial K) : PowerSeries K))
            + ((N - m : ℕ) : ℕ∞)
          = ((N - m : ℕ) : ℕ∞) := by rw [hP, zero_add]
      _ < ((N - j : ℕ) : ℕ∞) := by exact_mod_cast hsub
      _ ≤ PowerSeries.order (((P j : Polynomial K) : PowerSeries K))
            + ((N - j : ℕ) : ℕ∞) := le_add_left le_rfl

end Submission.CDT
