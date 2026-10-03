/-
# Discrete Abel summation with the weight `log`

A tool file for the low part of the Möbius-log split (`Work.FIArea7.t2psi_low`):
summation by parts with the logarithmic weight, for complex-valued sequences, in the
"supremum of partial sums" form.

If every partial sum `S t = ∑_{m ≤ t} b m` (`t ≤ M`) is bounded by `B` in norm, then
`∑_{m ≤ M} log m · b m` is bounded by `8 · log(M+2) · B` (the constant is irrelevant; the true
size is `2 log M · B`).

The proof is the exact discrete Abel transformation
`∑_{m≤M} L m (S m - S m-1) = L M · S M - ∑_{m<M} (L(m+1) - L m) · S m`
(`Finset.sum_range_by_parts`) followed by a telescoping (`Finset.sum_range_sub`).
-/
import Mathlib

open Finset

set_option autoImplicit false

namespace Work.FIArea7

/-- **Discrete Abel summation with the weight `log`.**  If `‖∑_{m ≤ t} b m‖ ≤ B` for every
`t ≤ M` then `‖∑_{m ≤ M} log m · b m‖ ≤ 8 log(M+2) B`. -/
theorem abelLogSum (b : ℕ → ℂ) (M : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ t : ℕ, t ≤ M → ‖∑ m ∈ Finset.Icc 1 t, b m‖ ≤ B) :
    ‖∑ m ∈ Finset.Icc 1 M, ((Real.log m : ℝ) : ℂ) * b m‖
      ≤ 8 * Real.log ((M : ℝ) + 2) * B := by
  have hreindex : ∀ n : ℕ,
      (∑ m ∈ Finset.Icc 1 n, ((Real.log m : ℝ) : ℂ) * b m)
        = ∑ i ∈ Finset.range n, (Real.log (((i + 1 : ℕ) : ℝ))) • b (i + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega) (fun m => ((Real.log m : ℝ) : ℂ) * b m), ih,
        Finset.sum_range_succ]
      simp [Complex.real_smul]
  have hGreindex : ∀ n : ℕ, (∑ i ∈ Finset.range n, b (i + 1)) = ∑ m ∈ Finset.Icc 1 n, b m := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]
  have hbp : (∑ i ∈ Finset.range M, (Real.log (((i + 1 : ℕ) : ℝ))) • b (i + 1))
      = (Real.log ((((M - 1) + 1 : ℕ) : ℝ))) • (∑ i ∈ Finset.range M, b (i + 1))
        - ∑ i ∈ Finset.range (M - 1),
            (Real.log (((i + 1 + 1 : ℕ) : ℝ)) - Real.log (((i + 1 : ℕ) : ℝ)))
              • (∑ j ∈ Finset.range (i + 1), b (j + 1)) :=
    Finset.sum_range_by_parts (fun i : ℕ => Real.log (((i + 1 : ℕ) : ℝ)))
      (fun i : ℕ => b (i + 1)) M
  rw [hreindex M, hbp]
  have hfnn : ∀ i : ℕ, 0 ≤ Real.log (((i + 1 : ℕ) : ℝ)) := fun i =>
    Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le i))
  have hG : ∀ n : ℕ, n ≤ M → ‖∑ j ∈ Finset.range n, b (j + 1)‖ ≤ B := by
    intro n hn
    rw [hGreindex n]
    exact h n hn
  have hA : ‖(Real.log ((((M - 1) + 1 : ℕ) : ℝ))) • (∑ i ∈ Finset.range M, b (i + 1))‖
      ≤ Real.log ((((M - 1) + 1 : ℕ) : ℝ)) * B := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hfnn _)]
    exact mul_le_mul_of_nonneg_left (hG M le_rfl) (hfnn _)
  have hB2 : ‖∑ i ∈ Finset.range (M - 1),
        (Real.log (((i + 1 + 1 : ℕ) : ℝ)) - Real.log (((i + 1 : ℕ) : ℝ)))
          • (∑ j ∈ Finset.range (i + 1), b (j + 1))‖
      ≤ Real.log ((((M - 1) + 1 : ℕ) : ℝ)) * B := by
    have hstep : ‖∑ i ∈ Finset.range (M - 1),
        (Real.log (((i + 1 + 1 : ℕ) : ℝ)) - Real.log (((i + 1 : ℕ) : ℝ)))
          • (∑ j ∈ Finset.range (i + 1), b (j + 1))‖
        ≤ ∑ i ∈ Finset.range (M - 1),
            (Real.log (((i + 1 + 1 : ℕ) : ℝ)) - Real.log (((i + 1 : ℕ) : ℝ))) * B := by
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i hi => ?_)
      have hi' : i + 1 ≤ M := by
        simp only [Finset.mem_range] at hi
        omega
      have hlogmono : Real.log (((i + 1 : ℕ) : ℝ)) ≤ Real.log (((i + 1 + 1 : ℕ) : ℝ)) :=
        Real.log_le_log (by positivity) (by push_cast; linarith)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hlogmono)]
      exact mul_le_mul_of_nonneg_left (hG (i + 1) hi') (sub_nonneg.mpr hlogmono)
    have htel : (∑ i ∈ Finset.range (M - 1),
          (Real.log (((i + 1 + 1 : ℕ) : ℝ)) - Real.log (((i + 1 : ℕ) : ℝ))))
        = Real.log ((((M - 1) + 1 : ℕ) : ℝ)) := by
      have := Finset.sum_range_sub (fun i : ℕ => Real.log (((i + 1 : ℕ) : ℝ))) (M - 1)
      simpa using this
    calc ‖∑ i ∈ Finset.range (M - 1),
          (Real.log (((i + 1 + 1 : ℕ) : ℝ)) - Real.log (((i + 1 : ℕ) : ℝ)))
            • (∑ j ∈ Finset.range (i + 1), b (j + 1))‖
        ≤ ∑ i ∈ Finset.range (M - 1),
            (Real.log (((i + 1 + 1 : ℕ) : ℝ)) - Real.log (((i + 1 : ℕ) : ℝ))) * B := hstep
      _ = (∑ i ∈ Finset.range (M - 1),
            (Real.log (((i + 1 + 1 : ℕ) : ℝ)) - Real.log (((i + 1 : ℕ) : ℝ)))) * B := by
          rw [Finset.sum_mul]
      _ = Real.log ((((M - 1) + 1 : ℕ) : ℝ)) * B := by rw [htel]
  have hfM : Real.log ((((M - 1) + 1 : ℕ) : ℝ)) ≤ Real.log ((M : ℝ) + 2) := by
    refine Real.log_le_log (by positivity) ?_
    have : ((M - 1) + 1 : ℕ) ≤ M + 2 := by omega
    exact_mod_cast this
  have hlog2nn : 0 ≤ Real.log ((M : ℝ) + 2) := by
    refine Real.log_nonneg ?_
    have : (1 : ℕ) ≤ M + 2 := by omega
    exact_mod_cast this
  calc ‖(Real.log ((((M - 1) + 1 : ℕ) : ℝ))) • (∑ i ∈ Finset.range M, b (i + 1))
        - ∑ i ∈ Finset.range (M - 1),
            (Real.log (((i + 1 + 1 : ℕ) : ℝ)) - Real.log (((i + 1 : ℕ) : ℝ)))
              • (∑ j ∈ Finset.range (i + 1), b (j + 1))‖
      ≤ ‖(Real.log ((((M - 1) + 1 : ℕ) : ℝ))) • (∑ i ∈ Finset.range M, b (i + 1))‖
        + ‖∑ i ∈ Finset.range (M - 1),
            (Real.log (((i + 1 + 1 : ℕ) : ℝ)) - Real.log (((i + 1 : ℕ) : ℝ)))
              • (∑ j ∈ Finset.range (i + 1), b (j + 1))‖ := norm_sub_le _ _
    _ ≤ Real.log ((((M - 1) + 1 : ℕ) : ℝ)) * B + Real.log ((((M - 1) + 1 : ℕ) : ℝ)) * B :=
        add_le_add hA hB2
    _ ≤ 8 * Real.log ((M : ℝ) + 2) * B := by nlinarith [hfM, hlog2nn, hB, hfnn (M - 1)]

end Work.FIArea7
