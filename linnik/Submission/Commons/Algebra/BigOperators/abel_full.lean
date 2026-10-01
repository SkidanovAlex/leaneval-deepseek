import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Complex.Basic

open Finset
open scoped BigOperators

namespace Commons.Algebra.BigOperators

/-- Initial sums `S a k = Σ_{1 ≤ n ≤ k} a n` (empty sum for `k = 0`). -/
private noncomputable def abelS (a : ℕ → ℂ) (k : ℕ) : ℂ := ∑ n ∈ Finset.Icc 1 k, a n

private lemma abelS_zero (a : ℕ → ℂ) : abelS a 0 = 0 := by
  unfold abelS
  simp

private lemma abelS_succ (a : ℕ → ℂ) (k : ℕ) : abelS a (k + 1) = abelS a k + a (k + 1) := by
  unfold abelS
  rw [Finset.sum_Icc_succ_top (a := 1) (b := k) (by omega : 1 ≤ k + 1)]

/-- Abel summation (by parts) for full sums `Σ_{n ∈ Icc 1 K} a n * w n`, in terms of
the initial sums `abelS a n`. -/
private lemma abel_full_aux (a : ℕ → ℂ) (w : ℕ → ℂ) (K : ℕ) :
    (∑ n ∈ Finset.Icc 1 K, a n * w n) =
      abelS a K * w K +
        (∑ n ∈ Finset.Icc 1 (K - 1), abelS a n * (w n - w (n + 1)))
        - abelS a 0 * w 1 := by
  induction K with
  | zero =>
      simp [abelS_zero]
  | succ K ih =>
      have hstep : (∑ n ∈ Finset.Icc 1 (K + 1), a n * w n)
          = (∑ n ∈ Finset.Icc 1 K, a n * w n) + a (K + 1) * w (K + 1) := by
            rw [Finset.sum_Icc_succ_top (a := 1) (b := K) (by omega : 1 ≤ K + 1)]
      have hsplit : (∑ n ∈ Finset.Icc 1 K, abelS a n * (w n - w (n + 1)))
          = (∑ n ∈ Finset.Icc 1 (K - 1), abelS a n * (w n - w (n + 1)))
              + abelS a K * (w K - w (K + 1)) := by
            by_cases hK0 : K = 0
            · subst K
              simp [abelS_zero]
            · have hb : (K - 1) + 1 = K := by omega
              calc
                (∑ n ∈ Finset.Icc 1 K, abelS a n * (w n - w (n + 1)))
                    = (∑ n ∈ Finset.Icc 1 ((K - 1) + 1), abelS a n * (w n - w (n + 1))) := by
                        congr 1
                        rw [hb]
                _ = (∑ n ∈ Finset.Icc 1 (K - 1), abelS a n * (w n - w (n + 1)))
                      + abelS a K * (w K - w (K + 1)) := by
                        rw [Finset.sum_Icc_succ_top (a := 1) (b := K - 1)
                          (by omega : 1 ≤ (K - 1) + 1)]
                        simp [hb]
      calc
        (∑ n ∈ Finset.Icc 1 (K + 1), a n * w n)
            = (∑ n ∈ Finset.Icc 1 K, a n * w n) + a (K + 1) * w (K + 1) := hstep
        _ = (abelS a K * w K + (∑ n ∈ Finset.Icc 1 (K - 1), abelS a n * (w n - w (n + 1)))
                - abelS a 0 * w 1) + a (K + 1) * w (K + 1) := by rw [ih]
        _ = abelS a K * w K + (∑ n ∈ Finset.Icc 1 (K - 1), abelS a n * (w n - w (n + 1)))
                + a (K + 1) * w (K + 1) - abelS a 0 * w 1 := by ring
        _ = (abelS a K + a (K + 1)) * w (K + 1) + abelS a K * (w K - w (K + 1))
                + (∑ n ∈ Finset.Icc 1 (K - 1), abelS a n * (w n - w (n + 1)))
                - abelS a 0 * w 1 := by ring
        _ = abelS a (K + 1) * w (K + 1) + (abelS a K * (w K - w (K + 1))
                + (∑ n ∈ Finset.Icc 1 (K - 1), abelS a n * (w n - w (n + 1))))
                - abelS a 0 * w 1 := by rw [abelS_succ a K]; ring
        _ = abelS a (K + 1) * w (K + 1) + (∑ n ∈ Finset.Icc 1 K, abelS a n * (w n - w (n + 1)))
                - abelS a 0 * w 1 := by rw [hsplit]; ring

/-- Abel (summation by parts) for full sums over `Icc 1 K`:
`Σ_{n=1}^{K} a n * w n = (Σ_{m=1}^{K} a m) * w K
   + Σ_{n=1}^{K-1} (Σ_{m=1}^{n} a m) * (w n - w (n+1))
   - (Σ_{m ∈ Icc 1 0} a m) * w 1`. -/
theorem abel_full (a : ℕ → ℂ) (w : ℕ → ℂ) (K : ℕ) :
    (∑ n ∈ Finset.Icc 1 K, a n * w n) =
      (∑ m ∈ Finset.Icc 1 K, a m) * w K +
        (∑ n ∈ Finset.Icc 1 (K - 1), ((∑ m ∈ Finset.Icc 1 n, a m) * (w n - w (n + 1))))
        - (∑ m ∈ Finset.Icc 1 0, a m) * w 1 := by
  simpa [abelS] using abel_full_aux a w K

end Commons.Algebra.BigOperators