/-
# Area 4 — Abel-summation envelope inequality for the diagonal evaluation

Given `a : ℕ → ℝ` with `a 1 ≥ 1` and `a n ≥ 0`, whose partial sums `S N = Σ_{k ≤ N} a k`
are bounded by the envelope `1 + F N` (`F := tdF ε C₁ M`), this proves that the weighted
sum against the majorant `H := tdH σ A` is bounded by the sum of the *increments* of the
envelope, i.e. the usual "summation by parts against the primitive" estimate used to
reduce HB (11.17) to an integral estimate for `H`.

The proof is a two-sided Abel summation:

* `thetaDiag_abel_diag X H N` (delegated) is the exact identity
  `Σ_{n ∈ Icc 2 N} (X n - X (n-1)) H n + X 1 H 2 = X N H N + Σ_{n ∈ Icc 2 (N-1)} X n (H n - H (n+1))`.
* Apply it to `X = S` (using `S n - S (n-1) = a n`) and to `X = F`.
* Bound `S N H N ≤ (1 + F N) H N`, `-S 1 H 2 ≤ -H 2` (since `S 1 = a 1 ≥ 1` and `H ≥ 0`)
  and each `S n (H n - H (n+1)) ≤ (1 + F n) (H n - H (n+1))` (using `H` antitone).
* The extra `1 · (H n - H (n+1))` terms telescope to `H 2 - H N`, cancelling the boundary
  terms and leaving exactly the asserted right-hand side.
-/
import Mathlib
import Submission.Work.LinnikAreas.Density4.thetaDiag_eval_defs
import Submission.Work.LinnikAreas.Density4.thetaDiag_abel_diag
import Submission.Work.LinnikAreas.Density4.thetaDiag_tdH_antitone
import Submission.Work.LinnikAreas.Density4.thetaDiag_tdH_nonneg
import Submission.Work.LinnikAreas.Density4.thetaDiag_telescope_Icc

open scoped BigOperators
noncomputable section

namespace Work.LinnikAreas.Density4

theorem thetaDiag_abel_env (ε C₁ M σ A : ℝ) (a : ℕ → ℝ)
    (hM : 0 < M) (hσ : σ ≤ 1) (hA : 0 < A) (ha1 : 1 ≤ a 1) (ha : ∀ n, 0 ≤ a n)
    (hS : ∀ n : ℕ, 1 ≤ n → (∑ k ∈ Finset.Icc 1 n, a k) ≤ 1 + Work.LinnikAreas.Density4.tdF ε C₁ M n) :
    ∀ N : ℕ, 2 ≤ N →
      (∑ n ∈ Finset.Icc 2 N, a n * Work.LinnikAreas.Density4.tdH σ A n)
        ≤ (∑ n ∈ Finset.Icc 2 N,
            (Work.LinnikAreas.Density4.tdF ε C₁ M n - Work.LinnikAreas.Density4.tdF ε C₁ M (n - 1))
              * Work.LinnikAreas.Density4.tdH σ A n)
          + Work.LinnikAreas.Density4.tdF ε C₁ M 1 * Work.LinnikAreas.Density4.tdH σ A 2 := by
  intro N hN
  set F : ℕ → ℝ := (fun n => tdF ε C₁ M n) with hF
  set H : ℕ → ℝ := (fun n => tdH σ A n) with hH
  set S : ℕ → ℝ := (fun n => ∑ k ∈ Finset.Icc 1 n, a k) with hSdef
  -- The partial sums are bounded by the envelope.
  have hSle : ∀ n, 1 ≤ n → S n ≤ 1 + F n := by
    intro n hn; rw [hSdef, hF]; exact hS n hn
  have hS1 : S 1 = a 1 := by rw [hSdef]; simp
  have hSNN : 0 ≤ H N := by rw [hH]; exact thetaDiag_tdH_nonneg σ A N
  have hH2NN : 0 ≤ H 2 := by rw [hH]; exact thetaDiag_tdH_nonneg σ A 2
  have hHanti : ∀ n, 1 ≤ n → H (n+1) ≤ H n := by
    intro n hn; rw [hH]; exact thetaDiag_tdH_antitone σ A hσ hA n hn
  -- `a n` is the successive difference of the partial sums.
  have hSdiff : ∀ n, 1 ≤ n → S n - S (n-1) = a n := by
    intro n hn
    have hb : 1 ≤ n - 1 + 1 := by omega
    have hsum := Finset.sum_Icc_succ_top (a := 1) (b := n - 1) hb (fun k => a k)
    have hn' : n - 1 + 1 = n := by omega
    rw [hn'] at hsum
    rw [hSdef]
    linarith [hsum]
  -- The two Abel identities.
  have hdiag := thetaDiag_abel_diag S H N hN
  have hdiagF := thetaDiag_abel_diag F H N hN
  have hLHS : ∑ n ∈ Finset.Icc 2 N, (S n - S (n-1)) * H n
      = ∑ n ∈ Finset.Icc 2 N, a n * H n := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [hSdiff n (by rw [Finset.mem_Icc] at hn; omega)]
  rw [hLHS] at hdiag
  have hA' : ∑ n ∈ Finset.Icc 2 N, a n * H n
      = S N * H N + ∑ n ∈ Finset.Icc 2 (N-1), S n * (H n - H (n+1)) - S 1 * H 2 := by
    linarith [hdiag]
  -- Term-by-term bounds.
  have hSN_le : S N * H N ≤ (1 + F N) * H N :=
    mul_le_mul_of_nonneg_right (hSle N (by omega)) hSNN
  have hS1_le : (1:ℝ) * H 2 ≤ S 1 * H 2 := by
    have : (1:ℝ) ≤ S 1 := by rw [hS1]; exact ha1
    exact mul_le_mul_of_nonneg_right this hH2NN
  have hG_le : ∑ n ∈ Finset.Icc 2 (N-1), S n * (H n - H (n+1))
      ≤ ∑ n ∈ Finset.Icc 2 (N-1), (1 + F n) * (H n - H (n+1)) := by
    apply Finset.sum_le_sum
    intro n hn
    have hn1 : 1 ≤ n := by rw [Finset.mem_Icc] at hn; omega
    have hdiff : 0 ≤ H n - H (n+1) := by have := hHanti n hn1; linarith
    exact mul_le_mul_of_nonneg_right (hSle n hn1) hdiff
  -- Telescoping and splitting of the constant `1` part.
  have htel : ∑ n ∈ Finset.Icc 2 (N-1), (H n - H (n+1)) = H 2 - H N :=
    thetaDiag_telescope_Icc H N hN
  have hsplit : ∑ n ∈ Finset.Icc 2 (N-1), (1 + F n) * (H n - H (n+1))
      = (H 2 - H N) + ∑ n ∈ Finset.Icc 2 (N-1), F n * (H n - H (n+1)) := by
    rw [← htel, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn; ring
  have hmain : ∑ n ∈ Finset.Icc 2 N, a n * H n
      ≤ F N * H N + ∑ n ∈ Finset.Icc 2 (N-1), F n * (H n - H (n+1)) := by
    rw [hA']
    calc S N * H N + (∑ n ∈ Finset.Icc 2 (N-1), S n * (H n - H (n+1))) - S 1 * H 2
        ≤ (1 + F N) * H N + (∑ n ∈ Finset.Icc 2 (N-1), (1 + F n) * (H n - H (n+1))) - 1 * H 2 := by
          linarith [hSN_le, hS1_le, hG_le]
      _ = F N * H N + ∑ n ∈ Finset.Icc 2 (N-1), F n * (H n - H (n+1)) := by
          rw [hsplit]; ring
  refine le_trans hmain ?_
  simp only [hF, hH] at hdiagF ⊢
  linarith [hdiagF]

end Work.LinnikAreas.Density4
