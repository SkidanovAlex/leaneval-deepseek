import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.bigW_log_eq
import Submission.Work.HP.clog_mul_log_le

/-!
# The size of `W = ∏_{p ≤ w} p^{r_p(w)}`

We bound `log W` from above.  Expanding the product (lemma `bigW_log_eq`),

  `log W = ∑_{p ≤ w, p prime} r_p(w) log p`,   with `r_p(w) = clog p ⌈w⌉ + 1`,

and each prime `p ≤ w` contributes at most `log ⌈w⌉ + 2 log p`, because
`p^(clog p ⌈w⌉ - 1) < ⌈w⌉`.  There are `π(⌊w⌋)` such primes and
`∑_{p ≤ ⌊w⌋} log p = θ(⌊w⌋) ≤ (log 4) ⌊w⌋ ≤ (log 4) w`.  Hence

  `log W ≤ π(⌊w⌋) log ⌈w⌉ + 2 (log 4) w`.

This is the elementary input to `w_bound`/`bigW_le_pow`.
-/

set_option autoImplicit false

namespace Work.HP

/-- `log W` is dominated by `π(⌊w⌋) · log ⌈w⌉ + 2 (log 4) w`. -/
theorem log_bigW_le (w : ℝ) (hw : 2 ≤ w) :
    Real.log ((bigW w : ℕ) : ℝ) ≤
      (Nat.primeCounting ⌊w⌋₊ : ℝ) * Real.log ⌈w⌉₊ + 2 * Real.log 4 * w := by
  rw [bigW_log_eq]
  set N := ⌊w⌋₊ with hN
  set M := ⌈w⌉₊ with hM
  have hM2 : 2 ≤ M := by
    rw [hM]
    have : (2 : ℝ) ≤ (⌈w⌉₊ : ℝ) := le_trans hw (Nat.le_ceil w)
    exact_mod_cast this
  have hNw : (N : ℝ) ≤ w := by rw [hN]; exact Nat.floor_le (by linarith)
  have hterm : ∀ p ∈ Nat.primesLE N,
      (rOf p w : ℝ) * Real.log (p : ℝ) ≤ Real.log M + 2 * Real.log (p : ℝ) := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primesLE hp
    have h1 : (Nat.clog p M : ℝ) * Real.log (p : ℝ) ≤ Real.log M + Real.log (p : ℝ) :=
      clog_mul_log_le p M hpp hM2
    have hr : (rOf p w : ℝ) = (Nat.clog p M : ℝ) + 1 := by
      simp only [rOf, hM, Nat.cast_add, Nat.cast_one]
    rw [hr]
    linarith
  have hsum : ∑ p ∈ Nat.primesLE N, (rOf p w : ℝ) * Real.log (p : ℝ)
      ≤ (Nat.primeCounting N : ℝ) * Real.log M + 2 * Chebyshev.theta (N : ℝ) := by
    calc ∑ p ∈ Nat.primesLE N, (rOf p w : ℝ) * Real.log (p : ℝ)
        ≤ ∑ p ∈ Nat.primesLE N, (Real.log M + 2 * Real.log (p : ℝ)) :=
          Finset.sum_le_sum hterm
      _ = (Nat.primeCounting N : ℝ) * Real.log M + 2 * Chebyshev.theta (N : ℝ) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum,
            Nat.primesLE_card_eq_primeCounting, ← Chebyshev.theta_eq_sum_primesLE_log,
            nsmul_eq_mul]
  refine le_trans hsum ?_
  have hth : Chebyshev.theta (N : ℝ) ≤ Real.log 4 * (N : ℝ) :=
    Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg N)
  have hfin : 2 * Chebyshev.theta (N : ℝ) ≤ 2 * Real.log 4 * w := by
    calc 2 * Chebyshev.theta (N : ℝ) ≤ 2 * (Real.log 4 * (N : ℝ)) := by linarith
      _ = 2 * Real.log 4 * (N : ℝ) := by ring
      _ ≤ 2 * Real.log 4 * w := by
          apply mul_le_mul_of_nonneg_left hNw; positivity
  linarith

end Work.HP
