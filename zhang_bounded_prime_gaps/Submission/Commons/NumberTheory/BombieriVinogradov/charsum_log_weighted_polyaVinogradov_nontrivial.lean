import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.polya_vinogradov
import Submission.Commons.Analysis.Summation.abel_prefix_bound
import Submission.Commons.Analysis.Summation.sum_Icc_one_eq_range

namespace Commons.NumberTheory.BombieriVinogradov

open Finset
open scoped BigOperators

set_option autoImplicit false
set_option linter.style.haveILetI false

/-- For `n : ℕ`, the interval `Icc 1 n` is `range (n+1)` with `0` removed. -/
private lemma Icc_one_eq_erase_range (n : ℕ) :
    Finset.Icc 1 n = (Finset.range (n + 1)).erase 0 := by
  ext k
  simp only [Finset.mem_Icc, Finset.mem_erase, Finset.mem_range]
  omega

/-- The interval sum over `Icc 1 n` is the `range (n+1)` sum minus the `0`-th term. -/
private lemma sum_Icc_one_eq_sum_range_sub (f : ℕ → ℂ) (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, f k) = (∑ k ∈ Finset.range (n + 1), f k) - f 0 := by
  rw [Icc_one_eq_erase_range]
  have hmem : 0 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  have h := Finset.sum_erase_add (Finset.range (n + 1)) f hmem
  rw [← h]; ring

/-- Telescoping the logarithm over the interval `Icc 1 (M-1)`. -/
private lemma sum_Icc_pred_log (M : ℕ) :
    (∑ n ∈ Finset.Icc 1 (M - 1), (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)))
      = Real.log (M : ℝ) := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM; simp
  · rw [Commons.Analysis.Summation.sum_Icc_one_eq_range (M - 1)
        (fun n => Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ))]
    have htel : (∑ k ∈ Finset.range (M - 1),
        (Real.log (((k + 1) + 1 : ℕ) : ℝ) - Real.log ((k + 1 : ℕ) : ℝ)))
        = Real.log (M : ℝ) := by
      have hsub := Finset.sum_range_sub (f := fun i : ℕ => Real.log ((i + 1 : ℕ) : ℝ)) (M - 1)
      rw [hsub]
      have hMm : (M - 1) + 1 = M := Nat.sub_add_cancel hM
      rw [hMm]
      simp
    exact htel

/-- Abel summation applied to the Pólya–Vinogradov bound: for a **nontrivial**
Dirichlet character `χ mod q` the logarithmically weighted character sum is
`≪ √q · log q · log N`.

The nontriviality hypothesis `χ ≠ 1` is essential: for the principal character
the sum is `∑_{n ≤ N, (n,q) = 1} log n`, which grows like `N log N` and hence
exceeds any `C √q log q log N`.  Proof: summation by parts
(`Commons.Analysis.Summation.abel_prefix_bound`) against the partial sums of `χ`,
each of which is `≤ C₀ √q log q` by
`Commons.NumberTheory.DirichletCharacter.polya_vinogradov`, together with
`∑_{n < N} (log (n+1) - log n) = log N`. -/
theorem charsum_log_weighted_polyaVinogradov_nontrivial :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ (N : ℕ),
      ‖∑ n ∈ Finset.Icc 1 N, ((Real.log (n : ℝ) : ℂ)) * χ (n : ZMod q)‖
        ≤ C * Real.sqrt q * Real.log (2 * (q : ℝ) + 2) * (Real.log (2 * (N : ℝ) + 2)) := by
  obtain ⟨C0, hC0pos, hC0⟩ := Commons.NumberTheory.DirichletCharacter.polya_vinogradov
  refine ⟨2 * C0 + 1, by positivity, ?_⟩
  intro q hq χ hχ N
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · -- `N = 0`: the sum is empty.
    subst hN0
    have hIcc : (Finset.Icc 1 0 : Finset ℕ) = ∅ := by simp
    rw [hIcc, Finset.sum_empty, norm_zero]
    have hlog2 : 0 ≤ Real.log (2 * ((0 : ℕ) : ℝ) + 2) := by
      rw [show (2 * ((0 : ℕ) : ℝ) + 2) = 2 by norm_num]
      exact (Real.log_pos (by norm_num)).le
    have hsqrt : 0 ≤ Real.sqrt (q : ℝ) := Real.sqrt_nonneg _
    have hlogq : 0 ≤ Real.log (2 * (q : ℝ) + 2) := by
      apply Real.log_nonneg
      have : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
      linarith
    have hCpos : 0 ≤ 2 * C0 + 1 := le_of_lt (by positivity)
    exact mul_nonneg (mul_nonneg (mul_nonneg hCpos hsqrt) hlogq) hlog2
  · -- `N ≥ 1`
    have hq2 : 2 ≤ q := by
      rcases Nat.lt_or_ge q 2 with h | h
      · have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
        have hq1 : q = 1 := by omega
        subst hq1
        exact absurd (Subsingleton.elim χ 1) hχ
      · exact h
    haveI hnt : Nontrivial (ZMod q) := ZMod.nontrivial_iff.mpr (by omega)
    have hchi0 : χ ((0 : ℕ) : ZMod q) = 0 := by
      simpa using (MulChar.map_nonunit χ (a := (0 : ZMod q)) not_isUnit_zero)
    -- basic non-negativity facts
    have hqRpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
    have hsqrtnn : 0 ≤ Real.sqrt (q : ℝ) := Real.sqrt_nonneg _
    have hlogqnn : 0 ≤ Real.log (q : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
    have hBnn : 0 ≤ C0 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by positivity
    have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
    have hlogNnn : 0 ≤ Real.log (2 * (N : ℝ) + 2) := Real.log_nonneg (by linarith)
    -- prefix bound from Pólya–Vinogradov
    have hprefix : ∀ n, 1 ≤ n → n ≤ N →
        ‖∑ k ∈ Finset.Icc 1 n, χ (k : ZMod q)‖ ≤ C0 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
      intro n _ _
      rw [sum_Icc_one_eq_sum_range_sub (fun k => χ (k : ZMod q)) n, hchi0, sub_zero]
      exact hC0 q hq2 χ hχ n
    -- Abel summation
    have habel := Commons.Analysis.Summation.abel_prefix_bound
      (fun k : ℕ => χ (k : ZMod q)) (fun k : ℕ => (Real.log (k : ℝ) : ℂ))
      (C0 * Real.sqrt (q : ℝ) * Real.log (q : ℝ)) (by omega) le_rfl hprefix
    have hlhs : (∑ k ∈ Finset.Icc 1 N, χ (k : ZMod q) * (Real.log (k : ℝ) : ℂ))
        = ∑ k ∈ Finset.Icc 1 N, (Real.log (k : ℝ) : ℂ) * χ (k : ZMod q) :=
      Finset.sum_congr rfl (fun k _ => mul_comm _ _)
    rw [hlhs] at habel
    -- bound the endpoint term
    have hbN : ‖((Real.log (N : ℝ) : ℝ) : ℂ)‖ ≤ Real.log (2 * (N : ℝ) + 2) :=
      calc ‖((Real.log (N : ℝ) : ℝ) : ℂ)‖ = Real.log (N : ℝ) :=
            @RCLike.norm_of_nonneg ℂ _ (Real.log (N : ℝ))
              (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega)))
        _ ≤ Real.log (2 * (N : ℝ) + 2) :=
            Real.log_le_log hNposR (by linarith)
    -- bound the telescoping term
    have hb2 : (∑ n ∈ Finset.Icc 1 (N - 1),
          ‖((Real.log (n : ℝ) : ℝ) : ℂ) - ((Real.log ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ)‖)
        ≤ Real.log (2 * (N : ℝ) + 2) := by
      have hterm : ∀ n ∈ Finset.Icc 1 (N - 1),
          ‖((Real.log (n : ℝ) : ℝ) : ℂ) - ((Real.log ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ)‖
            = Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) := by
        intro n hn
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
        have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
        have hle : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
        have hlog : Real.log (n : ℝ) ≤ Real.log ((n + 1 : ℕ) : ℝ) := Real.log_le_log hnpos hle
        have hkey : ((Real.log (n : ℝ) : ℝ) : ℂ) - ((Real.log ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ)
            = - (((Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)) : ℝ) : ℂ) := by
          rw [Complex.ofReal_sub]; ring
        rw [hkey, norm_neg]
        exact @RCLike.norm_of_nonneg ℂ _ _ (sub_nonneg.mpr hlog)
      calc (∑ n ∈ Finset.Icc 1 (N - 1),
            ‖((Real.log (n : ℝ) : ℝ) : ℂ) - ((Real.log ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ)‖)
          = ∑ n ∈ Finset.Icc 1 (N - 1),
              (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)) := Finset.sum_congr rfl hterm
        _ = Real.log (N : ℝ) := sum_Icc_pred_log N
        _ ≤ Real.log (2 * (N : ℝ) + 2) := Real.log_le_log hNposR (by linarith)
    -- glue
    have hstep : ‖∑ k ∈ Finset.Icc 1 N, (Real.log (k : ℝ) : ℂ) * χ (k : ZMod q)‖
        ≤ 2 * (C0 * Real.sqrt (q : ℝ) * Real.log (q : ℝ)) * Real.log (2 * (N : ℝ) + 2) := by
      refine habel.trans ?_
      have h1 : (C0 * Real.sqrt (q : ℝ) * Real.log (q : ℝ)) * ‖((Real.log (N : ℝ) : ℝ) : ℂ)‖
          ≤ (C0 * Real.sqrt (q : ℝ) * Real.log (q : ℝ)) * Real.log (2 * (N : ℝ) + 2) :=
        mul_le_mul_of_nonneg_left hbN hBnn
      have h2 : (C0 * Real.sqrt (q : ℝ) * Real.log (q : ℝ)) *
            (∑ n ∈ Finset.Icc 1 (N - 1),
              ‖((Real.log (n : ℝ) : ℝ) : ℂ) - ((Real.log ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ)‖)
          ≤ (C0 * Real.sqrt (q : ℝ) * Real.log (q : ℝ)) * Real.log (2 * (N : ℝ) + 2) :=
        mul_le_mul_of_nonneg_left hb2 hBnn
      linarith [h1, h2]
    -- final numeric comparison
    have hlogq_le : Real.log (q : ℝ) ≤ Real.log (2 * (q : ℝ) + 2) :=
      Real.log_le_log hqRpos (by linarith)
    have hlogqq_nn : 0 ≤ Real.log (2 * (q : ℝ) + 2) := by
      apply Real.log_nonneg
      have hqnn : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
      linarith
    have hSA' : (0 : ℝ) ≤ Real.sqrt (q : ℝ) * Real.log (2 * (q : ℝ) + 2) :=
      mul_nonneg hsqrtnn hlogqq_nn
    have hSA : (0 : ℝ) ≤ Real.sqrt (q : ℝ) * Real.log (q : ℝ) :=
      mul_nonneg hsqrtnn hlogqnn
    have hSAle : Real.sqrt (q : ℝ) * Real.log (q : ℝ)
        ≤ Real.sqrt (q : ℝ) * Real.log (2 * (q : ℝ) + 2) :=
      mul_le_mul_of_nonneg_left hlogq_le hsqrtnn
    have hle1 : 2 * C0 * Real.sqrt (q : ℝ) * Real.log (q : ℝ)
        ≤ (2 * C0 + 1) * Real.sqrt (q : ℝ) * Real.log (2 * (q : ℝ) + 2) := by
      nlinarith [hSA, hSA', hSAle, hC0pos]
    calc ‖∑ k ∈ Finset.Icc 1 N, (Real.log (k : ℝ) : ℂ) * χ (k : ZMod q)‖
        ≤ 2 * (C0 * Real.sqrt (q : ℝ) * Real.log (q : ℝ)) * Real.log (2 * (N : ℝ) + 2) := hstep
      _ = 2 * C0 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) * Real.log (2 * (N : ℝ) + 2) := by ring
      _ ≤ (2 * C0 + 1) * Real.sqrt (q : ℝ) * Real.log (2 * (q : ℝ) + 2)
            * Real.log (2 * (N : ℝ) + 2) :=
          mul_le_mul_of_nonneg_right hle1 hlogNnn

end Commons.NumberTheory.BombieriVinogradov
