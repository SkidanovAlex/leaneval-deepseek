import Mathlib
import Submission.Work.Asymptotics.OddSigmaMatrices
import Submission.Work.Asymptotics.oddSigma_matrices

open Matrix Polynomial

namespace Work.Asymptotics

noncomputable section

/-!
# Polynomial growth of the powers of `oddMT` and `oddMTi`

The explicit matrices `oddMT`, `oddMTi = oddMT⁻¹` of
`Submission.Work.Asymptotics.OddSigmaMatrices` and
`Submission.Work.Asymptotics.oddSigma_matrices` satisfy the polynomial identity
`(A - 1)^2 * (A^2 + 1) = 0` (a finite check on explicit integral matrices).  Consequently the
powers `A^m` grow at most linearly in `m`: writing `E = (A - 1)^2`, `W = A^2 + 1`, the
remainder of `x^m` modulo `(x - 1)^2 (x^2 + 1)` is
`(1/2) x^{m+1} (x-1)^2 + (((m-1)/2) x + (2-m)/2) (x^2+1)`, whose evaluation at `A` gives the
decomposition `2 • A^m = A^{m+1} E + ((m-1) • A + (2-m) • 1) * W` proved below by reducing it
to a polynomial divisibility statement in `ℂ[X]`.  The first summand is periodic of period two
up to sign because `A^2 E = -E`, and the second is manifestly `O(m)`.

Everything is reduced to the general lemma `mat_pow_growth`, which is then applied to `oddMT`
and `oddMTi`. -/

/-- The matrix `(A - 1)^2`, the first factor of the minimal polynomial of `oddMT`. -/
def matE (A : Matrix (Fin 6) (Fin 6) ℂ) : Matrix (Fin 6) (Fin 6) ℂ := (A - 1)^2

/-- The matrix `A^2 + 1`, the second factor of the minimal polynomial of `oddMT`. -/
def matW (A : Matrix (Fin 6) (Fin 6) ℂ) : Matrix (Fin 6) (Fin 6) ℂ := A^2 + 1

/-- The polynomial `2 X^m - X^{m+1} (X-1)^2 - ((m-1) X + (2-m)) (X^2 + 1)` whose evaluation at
any matrix `A` with `(A-1)^2 (A^2+1) = 0` is `(2 • A^m) - A^{m+1}(A-1)^2 - ((m-1)•A + (2-m)•1)(A^2+1)`. -/
noncomputable def oddJt (m : ℕ) : ℂ[X] :=
  (2:ℂ[X]) * X^m - X^(m+1) * (X - 1)^2 - (C ((m:ℂ) - 1) * X + C (2 - (m:ℂ))) * (X^2 + 1)

lemma oddJt_zero : oddJt 0 = 0 := by
  unfold oddJt
  simp only [pow_zero, Nat.cast_zero, sub_zero, zero_sub, map_neg, map_ofNat, map_one]
  ring_nf

lemma oddJt_succ (m : ℕ) :
    oddJt (m+1) = X * oddJt m + C ((m:ℂ) - 1) * ((X-1)^2 * (X^2+1)) := by
  unfold oddJt
  push_cast
  simp only [pow_succ', map_sub, map_add, map_natCast, map_one, map_ofNat]
  ring_nf

lemma oddJt_dvd (m : ℕ) : ((X-1)^2 * (X^2+1) : ℂ[X]) ∣ oddJt m := by
  induction m with
  | zero => rw [oddJt_zero]; exact dvd_zero _
  | succ m ih =>
    rw [oddJt_succ]
    exact dvd_add (dvd_mul_of_dvd_right ih X) (dvd_mul_of_dvd_right (dvd_refl _) _)

/-- The explicit closed form for the powers of a matrix satisfying `(A-1)^2 (A^2+1) = 0`:
`2 • A^m = A^{m+1} (A-1)^2 + ((m-1) • A + (2-m) • 1) (A^2+1)`. -/
lemma oddMat_decomp (A : Matrix (Fin 6) (Fin 6) ℂ) (h : matE A * matW A = 0) (m : ℕ) :
    (2:ℂ) • A^m = A^(m+1) * matE A + ((((m:ℂ) - 1)) • A + ((2 - (m:ℂ))) • 1) * matW A := by
  rw [matE, matW]
  have hP : Polynomial.aeval A (((X-1)^2 * (X^2+1)) : ℂ[X]) = 0 := by
    simpa [matE, matW] using h
  have hJ : Polynomial.aeval A (oddJt m) = 0 := by
    obtain ⟨q, hq⟩ := oddJt_dvd m
    rw [hq, map_mul, hP, zero_mul]
  simp only [oddJt, Polynomial.aeval_X, Polynomial.aeval_C, map_sub, map_mul, map_pow, map_add,
    map_ofNat, map_one] at hJ
  simp only [Algebra.smul_def, map_sub, map_one, map_ofNat, mul_one]
  rw [sub_eq_zero, sub_eq_iff_eq_add] at hJ
  rw [add_comm] at hJ
  exact hJ

/-- **Polynomial growth of powers.**  A matrix `A` over `ℂ` with `(A-1)^2 (A^2+1) = 0` has
entrywise at most linear growth of its powers. -/
lemma mat_pow_growth (A : Matrix (Fin 6) (Fin 6) ℂ) (h : matE A * matW A = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, ∀ i j : Fin 6, ‖(A^m) i j‖ ≤ C * (1 + (m:ℝ)) := by
  classical
  -- `A ^ k * matE A` only takes the four values `±matE A`, `±(A * matE A)`.
  have hEA2 : matE A * A^2 = -(matE A) := by
    have hh := h
    rw [matW, mul_add, mul_one] at hh
    exact add_eq_zero_iff_eq_neg.mp hh
  have hcomm : matE A * A^2 = A^2 * matE A := by rw [matE]; noncomm_ring
  have hA2E : A^2 * matE A = -(matE A) := by rw [← hcomm, hEA2]
  have hpow : ∀ k : ℕ, A^k * matE A = matE A ∨ A^k * matE A = -(matE A) ∨
      A^k * matE A = A * matE A ∨ A^k * matE A = -(A * matE A) := by
    intro k
    induction k with
    | zero => left; simp
    | succ k ih =>
      rw [pow_succ', mul_assoc]
      rcases ih with h1|h2|h3|h4
      · right; right; left; rw [h1]
      · right; right; right; rw [h2, mul_neg]
      · right; left; rw [h3, ← mul_assoc, ← pow_two, hA2E]
      · left; rw [h4, mul_neg, ← mul_assoc, ← pow_two, hA2E, neg_neg]
  have hE : ∀ k : ℕ, ∀ i j : Fin 6,
      ‖(A^k * matE A) i j‖ ≤ ‖(matE A) i j‖ + ‖(A * matE A) i j‖ := by
    intro k i j
    rcases hpow k with h1|h2|h3|h4
    · rw [h1]; linarith [norm_nonneg ((A * matE A) i j)]
    · rw [h2, Matrix.neg_apply, norm_neg]; linarith [norm_nonneg ((A * matE A) i j)]
    · rw [h3]; linarith [norm_nonneg ((matE A) i j)]
    · rw [h4, Matrix.neg_apply, norm_neg]; linarith [norm_nonneg ((matE A) i j)]
  -- the `O(m)` term
  have hT : ∀ m : ℕ, ∀ i j : Fin 6,
      ‖((((m:ℂ) - 1) • A + (2 - (m:ℂ)) • 1) * matW A) i j‖ ≤
        (1 + (m:ℝ)) * (2 * (‖(A * matW A) i j‖ + ‖matW A i j‖)) := by
    intro m i j
    have hsplit : ((((m:ℂ) - 1) • A + (2 - (m:ℂ)) • 1) * matW A)
        = ((m:ℂ)-1) • (A * matW A) + (2 - (m:ℂ)) • matW A := by
      rw [add_mul, smul_mul_assoc, smul_mul_assoc, one_mul]
    rw [hsplit, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
    set f := (A * matW A) i j
    set gg := matW A i j
    have hf : 0 ≤ ‖f‖ := norm_nonneg f
    have hg : 0 ≤ ‖gg‖ := norm_nonneg gg
    have h1 : ‖(m:ℂ) - 1‖ ≤ (m:ℝ) + 1 := by
      have := norm_sub_le (m:ℂ) (1:ℂ); rw [Complex.norm_natCast, norm_one] at this; exact this
    have h2 : ‖(2:ℂ) - (m:ℂ)‖ ≤ (m:ℝ) + 2 := by
      have := norm_sub_le (2:ℂ) (m:ℂ)
      rw [Complex.norm_natCast, show ‖(2:ℂ)‖ = (2:ℝ) from by norm_num] at this; linarith
    calc ‖((m:ℂ)-1) * f + (2 - (m:ℂ)) * gg‖
        ≤ ‖((m:ℂ)-1) * f‖ + ‖(2 - (m:ℂ)) * gg‖ := norm_add_le _ _
      _ = ‖(m:ℂ)-1‖ * ‖f‖ + ‖(2 - (m:ℂ))‖ * ‖gg‖ := by rw [norm_mul, norm_mul]
      _ ≤ ((m:ℝ)+1) * ‖f‖ + ((m:ℝ)+2) * ‖gg‖ := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_right h1 hf
          · exact mul_le_mul_of_nonneg_right h2 hg
      _ ≤ (1 + (m:ℝ)) * (2 * (‖f‖ + ‖gg‖)) := by
          have e1 : (m:ℝ)+1 ≤ 2*(1+(m:ℝ)) := by linarith
          have e2 : (m:ℝ)+2 ≤ 2*(1+(m:ℝ)) := by linarith
          calc ((m:ℝ)+1) * ‖f‖ + ((m:ℝ)+2) * ‖gg‖
              ≤ 2*(1+(m:ℝ)) * ‖f‖ + 2*(1+(m:ℝ)) * ‖gg‖ :=
                add_le_add (mul_le_mul_of_nonneg_right e1 hf) (mul_le_mul_of_nonneg_right e2 hg)
            _ = (1 + (m:ℝ)) * (2 * (‖f‖ + ‖gg‖)) := by ring
  -- the uniform constant
  let g : Fin 6 → Fin 6 → ℝ := fun i j =>
    (1/2) * (‖matE A i j‖ + ‖(A * matE A) i j‖ + 2 * (‖(A * matW A) i j‖ + ‖matW A i j‖))
  have hgnn : ∀ i j, 0 ≤ g i j := fun i j => by simp only [g]; positivity
  have hgsum : ∀ a : Fin 6, 0 ≤ ∑ b : Fin 6, g a b := fun a => Finset.sum_nonneg (fun b _ => hgnn a b)
  refine ⟨∑ i : Fin 6, ∑ j : Fin 6, g i j, ?_, ?_⟩
  · exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hgnn i j))
  · intro m i j
    have hsum : g i j ≤ ∑ a : Fin 6, ∑ b : Fin 6, g a b := by
      calc g i j ≤ ∑ b : Fin 6, g i b := Finset.single_le_sum (fun b _ => hgnn i b) (Finset.mem_univ j)
        _ ≤ ∑ a : Fin 6, ∑ b : Fin 6, g a b := Finset.single_le_sum (fun a _ => hgsum a) (Finset.mem_univ i)
    have hentry := congrArg (fun M : Matrix (Fin 6) (Fin 6) ℂ => M i j) (oddMat_decomp A h m)
    simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul] at hentry
    have hz : (A^m) i j = (1/2) * ((A^(m+1) * matE A) i j + ((((m:ℂ)-1) • A + (2-(m:ℂ)) • 1) * matW A) i j) := by
      rw [← hentry]; ring
    have hB : 0 ≤ ‖matE A i j‖ + ‖(A * matE A) i j‖ := by positivity
    have hD : 0 ≤ 2 * (‖(A * matW A) i j‖ + ‖matW A i j‖) := by positivity
    have hm : (0:ℝ) ≤ (m:ℝ) := by positivity
    calc ‖(A^m) i j‖
        = ‖(1/2) * ((A^(m+1) * matE A) i j + ((((m:ℂ)-1) • A + (2-(m:ℂ)) • 1) * matW A) i j)‖ := by rw [hz]
      _ = (1/2) * ‖(A^(m+1) * matE A) i j + ((((m:ℂ)-1) • A + (2-(m:ℂ)) • 1) * matW A) i j‖ := by
            rw [norm_mul, show ‖(1/2:ℂ)‖ = (1/2:ℝ) from by norm_num]
      _ ≤ (1/2) * (‖(A^(m+1) * matE A) i j‖ + ‖((((m:ℂ)-1) • A + (2-(m:ℂ)) • 1) * matW A) i j‖) := by
            apply mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
      _ ≤ (1/2) * ((‖matE A i j‖ + ‖(A * matE A) i j‖) + (1 + (m:ℝ)) * (2 * (‖(A * matW A) i j‖ + ‖matW A i j‖))) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            exact add_le_add (hE (m+1) i j) (hT m i j)
      _ ≤ (1 + (m:ℝ)) * g i j := by simp only [g]; nlinarith [hB, hD, hm]
      _ ≤ (1 + (m:ℝ)) * (∑ a : Fin 6, ∑ b : Fin 6, g a b) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = (∑ a : Fin 6, ∑ b : Fin 6, g a b) * (1 + (m:ℝ)) := by ring

/-- The minimal-polynomial identity `(oddMT - 1)^2 * (oddMT^2 + 1) = 0`. -/
lemma oddMT_minpoly : matE oddMT * matW oddMT = 0 := by
  rw [matE, matW]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, pow_succ, oddMT, Fin.sum_univ_six] <;> norm_num

/-- The minimal-polynomial identity `(oddMTi - 1)^2 * (oddMTi^2 + 1) = 0`. -/
lemma oddMTi_minpoly : matE oddMTi * matW oddMTi = 0 := by
  rw [matE, matW]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, pow_succ, oddMTi, Fin.sum_univ_six] <;> norm_num

/-- Polynomial growth of the powers of the explicit odd-weight matrices `oddMT` and
`oddMTi = oddMT⁻¹` of `Submission.Work.Asymptotics.OddSigmaMatrices` and
`Submission.Work.Asymptotics.oddSigma_matrices` (the matrices of `T` and `T⁻¹` in the
odd-weight representation in the basis `(1, T⁻¹, STS, S, ST⁻¹, TS)`).

The minimal polynomial of `oddMT` is `(x-1)^2 (x^2+1)`: both matrices satisfy
`(M - 1)^2 * (M^2 + 1) = 0` (finite check on explicit integral matrices), so `M^m` is a
`ℂ`-linear combination, with coefficients of size at most `C (1+|m|)`, of `1, M, M^2, M^3`.
The expected proof verifies the identity `(oddMT - 1)^2 * (oddMT^2 + 1) = 0` (and the same for
`oddMTi`) by `ext i j <;> fin_cases i <;> fin_cases j <;> norm_num`, and then uses the explicit
remainder of `x^m` modulo `(x-1)^2 (x^2+1)`. -/
theorem oddMT_pow_entry_bound :
    ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      (∀ m : ℕ, ∀ i j : Fin 6,
        ‖((Work.Asymptotics.oddMT ^ m) i j)‖ ≤ C * (1 + (m : ℝ)) ^ N) ∧
      (∀ m : ℕ, ∀ i j : Fin 6,
        ‖((Work.Asymptotics.oddMTi ^ m) i j)‖ ≤ C * (1 + (m : ℝ)) ^ N) := by
  obtain ⟨C1, hC1, h1⟩ := mat_pow_growth oddMT oddMT_minpoly
  obtain ⟨C2, hC2, h2⟩ := mat_pow_growth oddMTi oddMTi_minpoly
  refine ⟨max C1 C2, 1, le_max_of_le_left hC1, zero_le_one, ?_, ?_⟩
  · intro m i j
    rw [Real.rpow_one]
    exact le_trans (h1 m i j) (mul_le_mul_of_nonneg_right (le_max_left C1 C2) (by positivity))
  · intro m i j
    rw [Real.rpow_one]
    exact le_trans (h2 m i j) (mul_le_mul_of_nonneg_right (le_max_right C1 C2) (by positivity))

end

end Work.Asymptotics
