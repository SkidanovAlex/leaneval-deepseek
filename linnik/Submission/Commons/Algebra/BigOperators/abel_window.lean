import Mathlib
import Submission.Commons.Algebra.BigOperators.abel_full

open Finset
open scoped BigOperators

namespace Commons.Algebra.BigOperators

/-- `Icc 1 M = Icc 1 (N-1) ∪ Icc N M` for `1 ≤ N ≤ M`. -/
private lemma Icc_union_prefix (N M : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) :
    Finset.Icc 1 M = Finset.Icc 1 (N - 1) ∪ Finset.Icc N M := by
  ext n
  rw [Finset.mem_Icc, Finset.mem_union, Finset.mem_Icc, Finset.mem_Icc]
  omega

/-- Split `Σ_{n ∈ Icc 1 M}` at `N`: for `1 ≤ N ≤ M`,
`Σ_{n ∈ Icc N M} f n = Σ_{n ∈ Icc 1 M} f n − Σ_{n ∈ Icc 1 (N−1)} f n`. -/
private lemma sum_Icc_window (f : ℕ → ℂ) {N M : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) :
    (∑ n ∈ Finset.Icc N M, f n) = (∑ n ∈ Finset.Icc 1 M, f n) - (∑ n ∈ Finset.Icc 1 (N - 1), f n) := by
  have hun := Icc_union_prefix N M hN hNM
  have hdisj : Disjoint (Finset.Icc 1 (N - 1)) (Finset.Icc N M) := by
    rw [Finset.disjoint_left]
    intro n hn1 hn2
    have h1 : n ≤ N - 1 := (Finset.mem_Icc.mp hn1).2
    have h2 : N ≤ n := (Finset.mem_Icc.mp hn2).1
    omega
  calc
    (∑ n ∈ Finset.Icc N M, f n)
        = (∑ n ∈ Finset.Icc 1 (N - 1) ∪ Finset.Icc N M, f n) - (∑ n ∈ Finset.Icc 1 (N - 1), f n) := by
            rw [Finset.sum_union hdisj]
            ring
    _ = (∑ n ∈ Finset.Icc 1 M, f n) - (∑ n ∈ Finset.Icc 1 (N - 1), f n) := by rw [← hun]

/-- Peel off the left endpoint of an interval sum:
`Σ_{n ∈ Icc a b} g n = g a + Σ_{n ∈ Icc (a+1) b} g n` for `a ≤ b`. -/
private lemma sum_Icc_peel_bot (g : ℕ → ℂ) {a b : ℕ} (hab : a ≤ b) :
    (∑ n ∈ Finset.Icc a b, g n) = g a + ∑ n ∈ Finset.Icc (a + 1) b, g n := by
  have hb1 : a < b + 1 := by omega
  calc
    (∑ n ∈ Finset.Icc a b, g n)
        = ∑ n ∈ Finset.Ico a (b + 1), g n := by
            rw [← Finset.Ico_add_one_right_eq_Icc a b]
    _ = g a + ∑ n ∈ Finset.Ico (a + 1) (b + 1), g n := by
            rw [Finset.sum_eq_sum_Ico_succ_bot hb1 g]
    _ = g a + ∑ n ∈ Finset.Icc (a + 1) b, g n := by
            rw [Finset.Ico_add_one_right_eq_Icc (a + 1) b]

theorem abel_window (a : ℕ → ℂ) (w : ℕ → ℂ) {N M : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) :
    (∑ n ∈ Finset.Icc N M, a n * w n) =
      (∑ m ∈ Finset.Icc 1 M, a m) * w M +
        (∑ n ∈ Finset.Icc N (M - 1), ((∑ m ∈ Finset.Icc 1 n, a m) * (w n - w (n + 1))))
        - (∑ m ∈ Finset.Icc 1 (N - 1), a m) * w N := by
  by_cases hN2 : 2 ≤ N
  · have hL : (∑ n ∈ Finset.Icc N M, a n * w n)
        = (∑ n ∈ Finset.Icc 1 M, a n * w n) - (∑ n ∈ Finset.Icc 1 (N - 1), a n * w n) :=
          sum_Icc_window (fun n => a n * w n) hN hNM
    calc
      (∑ n ∈ Finset.Icc N M, a n * w n)
          = (∑ n ∈ Finset.Icc 1 M, a n * w n) - (∑ n ∈ Finset.Icc 1 (N - 1), a n * w n) := hL
      _ = ((∑ m ∈ Finset.Icc 1 M, a m) * w M
            + (∑ n ∈ Finset.Icc 1 (M - 1), ((∑ m ∈ Finset.Icc 1 n, a m) * (w n - w (n + 1))))
            - (∑ m ∈ Finset.Icc 1 0, a m) * w 1)
          - ((∑ m ∈ Finset.Icc 1 (N - 1), a m) * w (N - 1)
            + (∑ n ∈ Finset.Icc 1 ((N - 1) - 1), ((∑ m ∈ Finset.Icc 1 n, a m) * (w n - w (n + 1))))
            - (∑ m ∈ Finset.Icc 1 0, a m) * w 1) := by
            rw [Commons.Algebra.BigOperators.abel_full a w M,
                Commons.Algebra.BigOperators.abel_full a w (N - 1)]
      _ = (∑ m ∈ Finset.Icc 1 M, a m) * w M - (∑ m ∈ Finset.Icc 1 (N - 1), a m) * w (N - 1)
            + ((∑ n ∈ Finset.Icc 1 (M - 1), ((∑ m ∈ Finset.Icc 1 n, a m) * (w n - w (n + 1))))
              - (∑ n ∈ Finset.Icc 1 ((N - 1) - 1), ((∑ m ∈ Finset.Icc 1 n, a m) * (w n - w (n + 1))))) := by
            ring
      _ = (∑ m ∈ Finset.Icc 1 M, a m) * w M - (∑ m ∈ Finset.Icc 1 (N - 1), a m) * w (N - 1)
            + (∑ n ∈ Finset.Icc (N - 1) (M - 1), ((∑ m ∈ Finset.Icc 1 n, a m) * (w n - w (n + 1)))) := by
            have hsp : (∑ n ∈ Finset.Icc (N - 1) (M - 1), ((∑ m ∈ Finset.Icc 1 n, a m) * (w n - w (n + 1))))
                = (∑ n ∈ Finset.Icc 1 (M - 1), ((∑ m ∈ Finset.Icc 1 n, a m) * (w n - w (n + 1))))
                    - (∑ n ∈ Finset.Icc 1 ((N - 1) - 1), ((∑ m ∈ Finset.Icc 1 n, a m) * (w n - w (n + 1)))) := by
              exact sum_Icc_window (fun n => (∑ m ∈ Finset.Icc 1 n, a m) * (w n - w (n + 1)))
                (N := N - 1) (M := M - 1) (by omega : 1 ≤ N - 1) (by omega : N - 1 ≤ M - 1)
            rw [← hsp]
      _ = (∑ m ∈ Finset.Icc 1 M, a m) * w M
            + (∑ n ∈ Finset.Icc N (M - 1), ((∑ m ∈ Finset.Icc 1 n, a m) * (w n - w (n + 1))))
            - (∑ m ∈ Finset.Icc 1 (N - 1), a m) * w N := by
            have hpeel := sum_Icc_peel_bot (fun n => (∑ m ∈ Finset.Icc 1 n, a m) * (w n - w (n + 1)))
              (a := N - 1) (b := M - 1) (by omega : N - 1 ≤ M - 1)
            have hk : (N - 1) + 1 = N := by omega
            rw [hpeel, hk]
            ring
  · have hN1 : N = 1 := by omega
    subst N
    exact Commons.Algebra.BigOperators.abel_full a w M

end Commons.Algebra.BigOperators
