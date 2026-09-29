import Mathlib
import Submission.Work.TMC7Core.Cocycle

namespace Work.TMC7Core.Scale

open Work.TMC7Core

set_option linter.style.haveILetI false

/-- Scalar arithmetic behind the telescoped recurrence: if `1 ≤ M` and `0 ≤ D` then
`M * (n * M^n * D) + D * M^n ≤ (n+1) * M^{n+1} * D`. -/
private lemma arith (n : ℕ) (M D : ℝ) (hM : 1 ≤ M) (hD : 0 ≤ D) :
    M * ((n : ℝ) * M ^ n * D) + D * M ^ n ≤ ((n + 1 : ℕ) : ℝ) * M ^ (n + 1) * D := by
  have hMnn : 0 ≤ M := le_trans zero_le_one hM
  have hMn : 0 ≤ M ^ n := pow_nonneg hMnn n
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hcast, pow_succ]
  have hprod : 0 ≤ M ^ n * D * (M - 1) :=
    mul_nonneg (mul_nonneg hMn hD) (by linarith)
  nlinarith [hprod]

/-- `frob` is the Frobenius (Hilbert–Schmidt) norm, hence submultiplicative on `2×2`
matrices. -/
lemma frob_mul_le (A B : Matrix (Fin 2) (Fin 2) ℂ) : frob (A * B) ≤ frob A * frob B := by
  letI := Matrix.frobeniusNormedAddCommGroup (m := Fin 2) (n := Fin 2) (α := ℂ)
  have hf : ∀ C : Matrix (Fin 2) (Fin 2) ℂ, frob C = ‖C‖ := by
    intro C
    rw [Matrix.frobenius_norm_def, frob, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two,
        Real.sqrt_eq_rpow]
    congr 1
    simp only [Real.rpow_two]
    ring
  rw [hf (A * B), hf A, hf B]
  exact Matrix.frobenius_norm_mul A B

/-- The Frobenius norm is subadditive. -/
lemma frob_add_le (A B : Matrix (Fin 2) (Fin 2) ℂ) : frob (A + B) ≤ frob A + frob B := by
  letI := Matrix.frobeniusNormedAddCommGroup (m := Fin 2) (n := Fin 2) (α := ℂ)
  have hf : ∀ C : Matrix (Fin 2) (Fin 2) ℂ, frob C = ‖C‖ := by
    intro C
    rw [Matrix.frobenius_norm_def, frob, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two,
        Real.sqrt_eq_rpow]
    congr 1
    simp only [Real.rpow_two]
    ring
  rw [hf (A + B), hf A, hf B]
  exact norm_add_le A B

/-- **Stability of ordered matrix products.** If two sequences of `2×2` matrices are
uniformly bounded by `M ≥ √2` in Frobenius norm and agree pointwise to within `D`, then
their length-`n` ordered products differ by at most `n * M^n * D`.

The proof telescopes the difference along the recurrence
`matProd A (n+1) = A n * matProd A n` and uses the submultiplicativity and
subadditivity of the Frobenius norm together with `frob (matProd B k) ≤ M^k` for `k ≥ 1`. -/
theorem frob_matProd_sub_le (A B : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (M D : ℝ)
    (hM : Real.sqrt 2 ≤ M) (hD : 0 ≤ D)
    (hA : ∀ j, Work.TMC7Core.frob (A j) ≤ M) (hB : ∀ j, Work.TMC7Core.frob (B j) ≤ M)
    (hAB : ∀ j, Work.TMC7Core.frob (A j - B j) ≤ D) (n : ℕ) :
    Work.TMC7Core.frob (Work.TMC7Core.matProd A n - Work.TMC7Core.matProd B n) ≤
      (n : ℝ) * M ^ n * D := by
  have hMnn : 0 ≤ M := le_trans (Real.sqrt_nonneg 2) hM
  have hM1 : 1 ≤ M := le_trans Real.one_lt_sqrt_two.le hM
  -- Products of `B` are bounded by the corresponding power of `M`.
  have hBpow : ∀ k, frob (matProd B (k + 1)) ≤ M ^ (k + 1) := by
    intro k
    induction k with
    | zero =>
      simpa [matProd_succ, matProd_zero] using hB 0
    | succ k ih =>
      rw [matProd_succ]
      calc frob (B (k + 1) * matProd B (k + 1))
          ≤ frob (B (k + 1)) * frob (matProd B (k + 1)) := frob_mul_le _ _
        _ ≤ M * M ^ (k + 1) := mul_le_mul (hB (k + 1)) ih (frob_nonneg _) hMnn
        _ = M ^ (k + 1 + 1) := by rw [pow_succ]; ring
  -- One-step recurrence for the difference of products.
  have hrec : ∀ j, frob (matProd A (j + 1) - matProd B (j + 1)) ≤
      M * frob (matProd A j - matProd B j) + D * frob (matProd B j) := by
    intro j
    have heq : matProd A (j + 1) - matProd B (j + 1)
        = A j * (matProd A j - matProd B j) + (A j - B j) * matProd B j := by
      rw [matProd_succ, matProd_succ]
      noncomm_ring
    rw [heq]
    calc frob (A j * (matProd A j - matProd B j) + (A j - B j) * matProd B j)
        ≤ frob (A j * (matProd A j - matProd B j)) + frob ((A j - B j) * matProd B j) :=
          frob_add_le _ _
      _ ≤ frob (A j) * frob (matProd A j - matProd B j) + frob (A j - B j) * frob (matProd B j) :=
          add_le_add (frob_mul_le _ _) (frob_mul_le _ _)
      _ ≤ M * frob (matProd A j - matProd B j) + D * frob (matProd B j) :=
          add_le_add (mul_le_mul_of_nonneg_right (hA j) (frob_nonneg _))
                     (mul_le_mul_of_nonneg_right (hAB j) (frob_nonneg _))
  induction n with
  | zero =>
    have h0 : frob (matProd A 0 - matProd B 0) = 0 := by
      simp only [matProd_zero, sub_self]
      simp [frob]
    rw [h0]
    simp
  | succ m ih =>
    cases m with
    | zero =>
      have h1 : frob (matProd A 1 - matProd B 1) ≤ D := by
        rw [matProd_succ, matProd_zero, mul_one, matProd_succ, matProd_zero, mul_one]
        exact hAB 0
      calc frob (matProd A 1 - matProd B 1) ≤ D := h1
        _ = 1 * D := (one_mul D).symm
        _ ≤ M * D := mul_le_mul_of_nonneg_right hM1 hD
        _ = ((0 + 1 : ℕ) : ℝ) * M ^ (0 + 1) * D := by norm_num
    | succ k =>
      have h1 : M * frob (matProd A (k + 1) - matProd B (k + 1))
          ≤ M * (((k + 1 : ℕ) : ℝ) * M ^ (k + 1) * D) :=
        mul_le_mul_of_nonneg_left ih hMnn
      have h2 : D * frob (matProd B (k + 1)) ≤ D * M ^ (k + 1) :=
        mul_le_mul_of_nonneg_left (hBpow k) hD
      calc frob (matProd A (k + 1 + 1) - matProd B (k + 1 + 1))
          ≤ M * frob (matProd A (k + 1) - matProd B (k + 1)) + D * frob (matProd B (k + 1)) :=
            hrec (k + 1)
        _ ≤ M * (((k + 1 : ℕ) : ℝ) * M ^ (k + 1) * D) + D * M ^ (k + 1) := add_le_add h1 h2
        _ ≤ ((k + 1 + 1 : ℕ) : ℝ) * M ^ (k + 1 + 1) * D := arith (k + 1) M D hM1 hD

end Work.TMC7Core.Scale
