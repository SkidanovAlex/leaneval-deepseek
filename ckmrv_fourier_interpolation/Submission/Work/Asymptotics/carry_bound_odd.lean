import Mathlib
import Submission.Work.Asymptotics.PropagateBounds.Defs
import Submission.Work.Asymptotics.OddIdeal
import Submission.Work.Asymptotics.exists_sigma_odd
import Submission.Work.Asymptotics.mem_idealIOdd_exists
import Submission.Work.Asymptotics.linearIndependent_Mp_idealIOdd
import Submission.Work.Asymptotics.OddSigmaMatrices
import Submission.Work.Asymptotics.block_factorization
import Submission.Work.Asymptotics.PropagateCarriesOdd
import Submission.Work.Asymptotics.PropagateBounds.Reduce
import Submission.Work.Asymptotics.OddCocycle
import Submission.Work.Asymptotics.CarryBoundDefs
import Submission.Work.Asymptotics.CarryBoundBasic
import Submission.Work.Asymptotics.CarryBoundGlobal
import Submission.Work.Asymptotics.indep_Mp_idealIOdd
import Submission.Work.Asymptotics.oddSigma_matrices
import Submission.Work.GroupTheory.SL2Z_lift
import Submission.Work.Asymptotics.idealI_direct_augIdealOdd
import Submission.Work.Asymptotics.spanning_Mp_idealIOdd
import Submission.Work.Asymptotics.TwistOddDefs

namespace Work.Asymptotics

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups MonoidAlgebra ModularForm
open Work.Kernels

set_option maxHeartbeats 4000000

/-! ## Growth of the powers of the explicit odd matrices `oddMT`, `oddMTi` -/

/-- A matrix `M` with `(M - 1)^2 (M^2 + 1) = 0` satisfies an explicit "two-projector"
decomposition: writing `E1 = M(M-1)^2` and `E2 = ((1+1) - M)(M^2+1)`, one has `E1 + E2 = 1 + 1`,
`M^2 E1 = -E1` (so `E1 M^k` is periodic) and `E2 M^k = E2 + k • (E2 (M-1))` (linear).  Each
entry of `M^k` is therefore bounded by a constant times `1 + k`. -/
lemma pow_entry_bound_of_rel (M : Matrix (Fin 6) (Fin 6) ℂ)
    (hrel : (M - 1)^2 * (M*M + 1) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, ∀ i j : Fin 6, ‖(M^k) i j‖ ≤ C * (1 + (k:ℝ)) := by
  classical
  set E1 : Matrix (Fin 6) (Fin 6) ℂ := M * (M - 1)^2 with hE1def
  set E2 : Matrix (Fin 6) (Fin 6) ℂ := (((1:Matrix (Fin 6) (Fin 6) ℂ) + 1) - M) * (M*M + 1) with hE2def
  have hE12 : E1 + E2 = (1:Matrix (Fin 6) (Fin 6) ℂ) + 1 := by
    rw [hE1def, hE2def]; noncomm_ring
  have hM2E1 : (M*M) * E1 = -E1 := by
    have h : (M*M + 1) * E1 = 0 := by
      rw [hE1def]
      rw [show (M*M+1) * (M*(M-1)^2) = M * ((M-1)^2*(M*M+1)) from by noncomm_ring, hrel, mul_zero]
    rw [add_mul, one_mul] at h
    exact (add_eq_zero_iff_eq_neg.mp h)
  have hE1M2 : E1 * (M*M) = -E1 := by
    rw [show E1 * (M*M) = (M*M) * E1 from by rw [hE1def]; noncomm_ring, hM2E1]
  have hE2N : (M - 1)^2 * E2 = 0 := by
    rw [hE2def]
    rw [show (M-1)^2 * ((((1:Matrix (Fin 6) (Fin 6) ℂ)+1) - M) * (M*M+1))
        = ((((1:Matrix (Fin 6) (Fin 6) ℂ)+1) - M)) * ((M-1)^2*(M*M+1)) from by noncomm_ring,
      hrel, mul_zero]
  have hE2N2 : E2 * (M-1)^2 = 0 := by
    have hc : E2 * (M-1)^2 = (M-1)^2 * E2 := by rw [hE2def]; noncomm_ring
    rw [hc, hE2N]
  have hE2M : E2 * M = E2 + E2*(M-1) := by
    have hm : (1:Matrix (Fin 6) (Fin 6) ℂ) + (M-1) = M := by noncomm_ring
    calc E2 * M = E2 * ((1:Matrix (Fin 6) (Fin 6) ℂ) + (M-1)) := by rw [hm]
      _ = E2 + E2*(M-1) := by rw [mul_add, mul_one]
  have hEM : E2 * (M-1) * M = E2*(M-1) := by
    have hm : (1:Matrix (Fin 6) (Fin 6) ℂ) + (M-1) = M := by noncomm_ring
    have h2 : E2 * (M-1) * (M-1) = E2*(M-1)^2 := by rw [pow_two, mul_assoc]
    rw [show E2 * (M-1) * M
        = E2 * (M-1) * ((1:Matrix (Fin 6) (Fin 6) ℂ) + (M-1)) from by rw [hm]]
    rw [mul_add, mul_one, h2, hE2N2, add_zero]
  have hE2pow : ∀ k : ℕ, E2 * M^k = E2 + (k:ℂ) • (E2*(M-1)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← mul_assoc, ih, add_mul, smul_mul_assoc, hEM, hE2M]
      have hc : ((k:ℂ) + 1) • (E2*(M-1)) = (↑(k+1):ℂ) • (E2*(M-1)) := by
        congr 1; push_cast; ring
      rw [← hc, add_smul, one_smul]
      abel
  have hE1pow : ∀ k, E1 * M^k = E1 ∨ E1 * M^k = -E1 ∨ E1 * M^k = E1*M ∨ E1 * M^k = -(E1*M) := by
    intro k
    induction k with
    | zero => left; rw [pow_zero, mul_one]
    | succ k ih =>
      rw [pow_succ, ← mul_assoc]
      rcases ih with h | h | h | h
      · rw [h]; exact Or.inr (Or.inr (Or.inl rfl))
      · rw [h, neg_mul]; exact Or.inr (Or.inr (Or.inr rfl))
      · rw [h, mul_assoc, hE1M2]; exact Or.inr (Or.inl rfl)
      · rw [h, neg_mul, mul_assoc, hE1M2, neg_neg]; exact Or.inl rfl
  have hmk : ∀ k, M^k + M^k = E1*M^k + E2*M^k := by
    intro k
    have h : (E1 + E2) * M^k = E1*M^k + E2*M^k := add_mul _ _ _
    rw [hE12, add_mul, one_mul] at h
    exact h
  set B : ℝ := 1 + ∑ i : Fin 6, ∑ j : Fin 6,
      (‖E1 i j‖ + ‖(E1*M) i j‖ + ‖E2 i j‖ + ‖(E2*(M-1)) i j‖) with hB
  have hB0 : 0 ≤ B := by
    rw [hB]; positivity
  refine ⟨B, hB0, ?_⟩
  intro k i j
  have hsum : 2 * ‖(M^k) i j‖ ≤ ‖(E1*M^k) i j‖ + ‖(E2*M^k) i j‖ := by
    have h := hmk k
    have hentry : (M^k) i j + (M^k) i j = (E1*M^k) i j + (E2*M^k) i j := by
      have h2 := congrArg (fun X : Matrix (Fin 6) (Fin 6) ℂ => X i j) h
      simpa only [Matrix.add_apply] using h2
    have h3 : ‖(M^k) i j + (M^k) i j‖ ≤ ‖(E1*M^k) i j‖ + ‖(E2*M^k) i j‖ := by
      rw [hentry]; exact norm_add_le _ _
    have h4 : (M^k) i j + (M^k) i j = (2:ℂ) * ((M^k) i j) := by ring
    rw [h4, norm_mul] at h3
    have h5 : ‖(2:ℂ)‖ = 2 := by norm_num
    rw [h5] at h3
    linarith [norm_nonneg ((M^k) i j)]
  have hB1 : ‖(E1*M^k) i j‖ ≤ ‖E1 i j‖ + ‖(E1*M) i j‖ := by
    rcases hE1pow k with h | h | h | h
    · rw [h]; linarith [norm_nonneg ((E1*M) i j)]
    · rw [h, Matrix.neg_apply, norm_neg]; linarith [norm_nonneg ((E1*M) i j)]
    · rw [h]; linarith [norm_nonneg (E1 i j)]
    · rw [h, Matrix.neg_apply, norm_neg]; linarith [norm_nonneg (E1 i j)]
  have hB2 : ‖(E2*M^k) i j‖ ≤ ‖E2 i j‖ + (k:ℝ) * ‖(E2*(M-1)) i j‖ := by
    rw [hE2pow k]
    have hentry : (E2 + (k:ℂ) • (E2*(M-1))) i j = E2 i j + (k:ℂ) • ((E2*(M-1)) i j) := by
      simp only [Matrix.add_apply, Matrix.smul_apply]
    rw [hentry]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_smul, Complex.norm_natCast]
  have hBij : ‖E1 i j‖ + ‖(E1*M) i j‖ + ‖E2 i j‖ + ‖(E2*(M-1)) i j‖ ≤ B := by
    have hle : ‖E1 i j‖ + ‖(E1*M) i j‖ + ‖E2 i j‖ + ‖(E2*(M-1)) i j‖
        ≤ ∑ i : Fin 6, ∑ j : Fin 6,
          (‖E1 i j‖ + ‖(E1*M) i j‖ + ‖E2 i j‖ + ‖(E2*(M-1)) i j‖) := by
      refine le_trans ?_ (Finset.single_le_sum (f := fun i : Fin 6 => ∑ j : Fin 6,
          (‖E1 i j‖ + ‖(E1*M) i j‖ + ‖E2 i j‖ + ‖(E2*(M-1)) i j‖))
        (fun i _ => Finset.sum_nonneg (fun j _ => by positivity)) (Finset.mem_univ i))
      exact Finset.single_le_sum (f := fun j : Fin 6 =>
          (‖E1 i j‖ + ‖(E1*M) i j‖ + ‖E2 i j‖ + ‖(E2*(M-1)) i j‖))
        (fun j _ => by positivity) (Finset.mem_univ j)
    rw [hB]; linarith
  have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
  have h1k : (1:ℝ) ≤ 1 + (k:ℝ) := by linarith
  calc ‖(M^k) i j‖
      ≤ (‖E1 i j‖ + ‖(E1*M) i j‖ + ‖E2 i j‖ + (k:ℝ) * ‖(E2*(M-1)) i j‖) / 2 := by
        have hh := le_trans hsum (add_le_add hB1 hB2)
        linarith
    _ ≤ (‖E1 i j‖ + ‖(E1*M) i j‖ + ‖E2 i j‖ + ‖(E2*(M-1)) i j‖) * (1 + (k:ℝ)) / 2 := by
        have h3 : (k:ℝ) * ‖(E2*(M-1)) i j‖ ≤ ‖(E2*(M-1)) i j‖ * (1 + (k:ℝ)) := by
          nlinarith [norm_nonneg ((E2*(M-1)) i j), hk0]
        nlinarith [h3, norm_nonneg (E1 i j), norm_nonneg ((E1*M) i j), norm_nonneg (E2 i j)]
    _ ≤ B * (1 + (k:ℝ)) := by
        have h4 : (‖E1 i j‖ + ‖(E1*M) i j‖ + ‖E2 i j‖ + ‖(E2*(M-1)) i j‖) * (1 + (k:ℝ)) / 2
            ≤ (‖E1 i j‖ + ‖(E1*M) i j‖ + ‖E2 i j‖ + ‖(E2*(M-1)) i j‖) * (1 + (k:ℝ)) := by
          nlinarith [h1k, norm_nonneg (E1 i j), norm_nonneg ((E1*M) i j), norm_nonneg (E2 i j),
            norm_nonneg ((E2*(M-1)) i j)]
        exact le_trans h4 (mul_le_mul_of_nonneg_right hBij (by linarith))

lemma oddMT_rel :
    (oddMT - 1)^2 * (oddMT * oddMT + 1) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, pow_succ, oddMT, Fin.sum_univ_six] <;> norm_num

lemma oddMTi_rel :
    (oddMTi - 1)^2 * (oddMTi * oddMTi + 1) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, pow_succ, oddMTi, Fin.sum_univ_six] <;> norm_num

lemma pow_entry_bound_of_rel' (M : Matrix (Fin 6) (Fin 6) ℂ)
    (hrel : (M - 1)^2 * (M*M + 1) = 0) (B : ℝ) (hB1 : 1 ≤ B)
    (h1 : ∀ i j : Fin 6, ‖((M * (M - 1)^2 : Matrix (Fin 6) (Fin 6) ℂ)) i j‖ ≤ B)
    (h2 : ∀ i j : Fin 6, ‖(((M * (M - 1)^2) * M : Matrix (Fin 6) (Fin 6) ℂ)) i j‖ ≤ B)
    (h3 : ∀ i j : Fin 6,
      ‖((((1:Matrix (Fin 6) (Fin 6) ℂ) + 1 - M) * (M*M + 1) : Matrix (Fin 6) (Fin 6) ℂ)) i j‖ ≤ B)
    (h4 : ∀ i j : Fin 6,
      ‖(((((1:Matrix (Fin 6) (Fin 6) ℂ) + 1 - M) * (M*M + 1)) * (M - 1) : Matrix (Fin 6) (Fin 6) ℂ)) i j‖ ≤ B) :
    ∀ k : ℕ, ∀ i j : Fin 6, ‖(M^k) i j‖ ≤ (4*B) * (1 + (k:ℝ)) := by
  classical
  set E1 : Matrix (Fin 6) (Fin 6) ℂ := M * (M - 1)^2 with hE1def
  set E2 : Matrix (Fin 6) (Fin 6) ℂ := (((1:Matrix (Fin 6) (Fin 6) ℂ) + 1) - M) * (M*M + 1) with hE2def
  have h1' : ∀ i j, ‖E1 i j‖ ≤ B := by intro i j; rw [hE1def]; exact h1 i j
  have h2' : ∀ i j, ‖(E1 * M) i j‖ ≤ B := by intro i j; rw [hE1def]; exact h2 i j
  have h3' : ∀ i j, ‖E2 i j‖ ≤ B := by intro i j; rw [hE2def]; exact h3 i j
  have h4' : ∀ i j, ‖(E2 * (M - 1)) i j‖ ≤ B := by intro i j; rw [hE2def]; exact h4 i j
  have hE12 : E1 + E2 = (1:Matrix (Fin 6) (Fin 6) ℂ) + 1 := by
    rw [hE1def, hE2def]; noncomm_ring
  have hM2E1 : (M*M) * E1 = -E1 := by
    have h : (M*M + 1) * E1 = 0 := by
      rw [hE1def]
      rw [show (M*M+1) * (M*(M-1)^2) = M * ((M-1)^2*(M*M+1)) from by noncomm_ring, hrel, mul_zero]
    rw [add_mul, one_mul] at h
    exact (add_eq_zero_iff_eq_neg.mp h)
  have hE1M2 : E1 * (M*M) = -E1 := by
    rw [show E1 * (M*M) = (M*M) * E1 from by rw [hE1def]; noncomm_ring, hM2E1]
  have hE2N : (M - 1)^2 * E2 = 0 := by
    rw [hE2def]
    rw [show (M-1)^2 * ((((1:Matrix (Fin 6) (Fin 6) ℂ)+1) - M) * (M*M+1))
        = ((((1:Matrix (Fin 6) (Fin 6) ℂ)+1) - M)) * ((M-1)^2*(M*M+1)) from by noncomm_ring,
      hrel, mul_zero]
  have hE2N2 : E2 * (M-1)^2 = 0 := by
    have hc : E2 * (M-1)^2 = (M-1)^2 * E2 := by rw [hE2def]; noncomm_ring
    rw [hc, hE2N]
  have hE2M : E2 * M = E2 + E2*(M-1) := by
    have hm : (1:Matrix (Fin 6) (Fin 6) ℂ) + (M-1) = M := by noncomm_ring
    calc E2 * M = E2 * ((1:Matrix (Fin 6) (Fin 6) ℂ) + (M-1)) := by rw [hm]
      _ = E2 + E2*(M-1) := by rw [mul_add, mul_one]
  have hEM : E2 * (M-1) * M = E2*(M-1) := by
    have hm : (1:Matrix (Fin 6) (Fin 6) ℂ) + (M-1) = M := by noncomm_ring
    have h2 : E2 * (M-1) * (M-1) = E2*(M-1)^2 := by rw [pow_two, mul_assoc]
    rw [show E2 * (M-1) * M
        = E2 * (M-1) * ((1:Matrix (Fin 6) (Fin 6) ℂ) + (M-1)) from by rw [hm]]
    rw [mul_add, mul_one, h2, hE2N2, add_zero]
  have hE2pow : ∀ k : ℕ, E2 * M^k = E2 + (k:ℂ) • (E2*(M-1)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← mul_assoc, ih, add_mul, smul_mul_assoc, hEM, hE2M]
      have hc : ((k:ℂ) + 1) • (E2*(M-1)) = (↑(k+1):ℂ) • (E2*(M-1)) := by
        congr 1; push_cast; ring
      rw [← hc, add_smul, one_smul]
      abel
  have hE1pow : ∀ k, E1 * M^k = E1 ∨ E1 * M^k = -E1 ∨ E1 * M^k = E1*M ∨ E1 * M^k = -(E1*M) := by
    intro k
    induction k with
    | zero => left; rw [pow_zero, mul_one]
    | succ k ih =>
      rw [pow_succ, ← mul_assoc]
      rcases ih with h | h | h | h
      · rw [h]; exact Or.inr (Or.inr (Or.inl rfl))
      · rw [h, neg_mul]; exact Or.inr (Or.inr (Or.inr rfl))
      · rw [h, mul_assoc, hE1M2]; exact Or.inr (Or.inl rfl)
      · rw [h, neg_mul, mul_assoc, hE1M2, neg_neg]; exact Or.inl rfl
  have hmk : ∀ k, M^k + M^k = E1*M^k + E2*M^k := by
    intro k
    have h : (E1 + E2) * M^k = E1*M^k + E2*M^k := add_mul _ _ _
    rw [hE12, add_mul, one_mul] at h
    exact h
  intro k i j
  have hsum : 2 * ‖(M^k) i j‖ ≤ ‖(E1*M^k) i j‖ + ‖(E2*M^k) i j‖ := by
    have h := hmk k
    have hentry : (M^k) i j + (M^k) i j = (E1*M^k) i j + (E2*M^k) i j := by
      have h2 := congrArg (fun X : Matrix (Fin 6) (Fin 6) ℂ => X i j) h
      simpa only [Matrix.add_apply] using h2
    have h3 : ‖(M^k) i j + (M^k) i j‖ ≤ ‖(E1*M^k) i j‖ + ‖(E2*M^k) i j‖ := by
      rw [hentry]; exact norm_add_le _ _
    have h4 : (M^k) i j + (M^k) i j = (2:ℂ) * ((M^k) i j) := by ring
    rw [h4, norm_mul] at h3
    have h5 : ‖(2:ℂ)‖ = 2 := by norm_num
    rw [h5] at h3
    linarith [norm_nonneg ((M^k) i j)]
  have hB1 : ‖(E1*M^k) i j‖ ≤ B := by
    rcases hE1pow k with h | h | h | h
    · rw [h]; exact h1' i j
    · rw [h, Matrix.neg_apply, norm_neg]; exact h1' i j
    · rw [h]; exact h2' i j
    · rw [h, Matrix.neg_apply, norm_neg]; exact h2' i j
  have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
  have hB2 : ‖(E2*M^k) i j‖ ≤ B + (k:ℝ) * B := by
    rw [hE2pow k]
    have hentry : (E2 + (k:ℂ) • (E2*(M-1))) i j = E2 i j + (k:ℂ) • ((E2*(M-1)) i j) := by
      simp only [Matrix.add_apply, Matrix.smul_apply]
    rw [hentry]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_smul, Complex.norm_natCast]
    exact add_le_add (h3' i j) (mul_le_mul_of_nonneg_left (h4' i j) hk0)
  have h1k : (1:ℝ) ≤ 1 + (k:ℝ) := by linarith
  have hB0 : (0:ℝ) ≤ B := by linarith
  have hfin : 2 * ‖(M^k) i j‖ ≤ B + (B + (k:ℝ)*B) := le_trans hsum (add_le_add hB1 hB2)
  nlinarith [norm_nonneg ((M^k) i j), hk0, hB0, hfin]


private lemma oddMT_b1 : ∀ i j : Fin 6,
    ‖((oddMT * (oddMT - 1)^2) : Matrix (Fin 6) (Fin 6) ℂ) i j‖ ≤ 2 := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, pow_succ, oddMT, Fin.sum_univ_six, Matrix.vecMul, Matrix.vecHead, Matrix.vecTail] <;> norm_num

private lemma oddMT_b2 : ∀ i j : Fin 6,
    ‖(((oddMT * (oddMT - 1)^2) * oddMT) : Matrix (Fin 6) (Fin 6) ℂ) i j‖ ≤ 2 := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, pow_succ, oddMT, Fin.sum_univ_six, Matrix.vecMul, Matrix.vecHead, Matrix.vecTail] <;> norm_num

private lemma oddMT_b3 : ∀ i j : Fin 6,
    ‖((((1:Matrix (Fin 6) (Fin 6) ℂ) + 1 - oddMT) * (oddMT*oddMT + 1)) : Matrix (Fin 6) (Fin 6) ℂ) i j‖ ≤ 2 := by
  intro i j
  rw [sub_mul, add_mul, one_mul]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, pow_succ, oddMT, Fin.sum_univ_six, Matrix.vecMul, Matrix.vecHead, Matrix.vecTail] <;> norm_num

private lemma oddMT_b4 : ∀ i j : Fin 6,
    ‖(((((1:Matrix (Fin 6) (Fin 6) ℂ) + 1 - oddMT) * (oddMT*oddMT + 1)) * (oddMT - 1)) : Matrix (Fin 6) (Fin 6) ℂ) i j‖ ≤ 2 := by
  intro i j
  rw [sub_mul, add_mul, one_mul]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, pow_succ, oddMT, Fin.sum_univ_six, Matrix.vecMul, Matrix.vecHead, Matrix.vecTail] <;> norm_num

private lemma oddMTi_b1 : ∀ i j : Fin 6,
    ‖((oddMTi * (oddMTi - 1)^2) : Matrix (Fin 6) (Fin 6) ℂ) i j‖ ≤ 2 := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, pow_succ, oddMTi, Fin.sum_univ_six, Matrix.vecMul, Matrix.vecHead, Matrix.vecTail] <;> norm_num

private lemma oddMTi_b2 : ∀ i j : Fin 6,
    ‖(((oddMTi * (oddMTi - 1)^2) * oddMTi) : Matrix (Fin 6) (Fin 6) ℂ) i j‖ ≤ 2 := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, pow_succ, oddMTi, Fin.sum_univ_six, Matrix.vecMul, Matrix.vecHead, Matrix.vecTail] <;> norm_num

private lemma oddMTi_b3 : ∀ i j : Fin 6,
    ‖((((1:Matrix (Fin 6) (Fin 6) ℂ) + 1 - oddMTi) * (oddMTi*oddMTi + 1)) : Matrix (Fin 6) (Fin 6) ℂ) i j‖ ≤ 2 := by
  intro i j
  rw [sub_mul, add_mul, one_mul]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, pow_succ, oddMTi, Fin.sum_univ_six, Matrix.vecMul, Matrix.vecHead, Matrix.vecTail] <;> norm_num

private lemma oddMTi_b4 : ∀ i j : Fin 6,
    ‖(((((1:Matrix (Fin 6) (Fin 6) ℂ) + 1 - oddMTi) * (oddMTi*oddMTi + 1)) * (oddMTi - 1)) : Matrix (Fin 6) (Fin 6) ℂ) i j‖ ≤ 2 := by
  intro i j
  rw [sub_mul, add_mul, one_mul]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, pow_succ, oddMTi, Fin.sum_univ_six, Matrix.vecMul, Matrix.vecHead, Matrix.vecTail] <;> norm_num

/-- **The entries of `oddMT^k` and `oddMTi^k` grow at most linearly** (with constant `8`). -/
theorem oddMT_pow_le (k : ℕ) (i j : Fin 6) :
    ‖(oddMT ^ k) i j‖ ≤ 8 * (1 + (k:ℝ)) := by
  have h := pow_entry_bound_of_rel' oddMT oddMT_rel 2 (by norm_num)
    oddMT_b1 oddMT_b2 oddMT_b3 oddMT_b4 k i j
  have h2 : ((4:ℝ) * 2) = 8 := by norm_num
  rwa [h2] at h

theorem oddMTi_pow_le (k : ℕ) (i j : Fin 6) :
    ‖(oddMTi ^ k) i j‖ ≤ 8 * (1 + (k:ℝ)) := by
  have h := pow_entry_bound_of_rel' oddMTi oddMTi_rel 2 (by norm_num)
    oddMTi_b1 oddMTi_b2 oddMTi_b3 oddMTi_b4 k i j
  have h2 : ((4:ℝ) * 2) = 8 := by norm_num
  rwa [h2] at h


/-- `sigmaHom` maps the standard generators to the explicit matrices `oddMT`, `oddMS`. -/
theorem sigmaHom_odd_generators :
    sigmaHom ModularGroup.T = oddMT ∧ sigmaHom ModularGroup.S = oddMS := by
  obtain ⟨hmm, hcube, hrow1, hrow2, hrow3⟩ := oddSigma_matrices
  have h4 : oddMS ^ 4 = (1 : Matrix (Fin 6) (Fin 6) ℂ) := by
    rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, pow_two oddMS, hmm]; simp
  have h2 : oddMS ^ 2 = (oddMS * oddMT) ^ 3 := by rw [pow_two oddMS, hmm, hcube]
  obtain ⟨f, hfS, hfT⟩ := Work.GroupTheory.SL2Z_lift oddMS oddMT h4 h2
  constructor
  · ext i k
    have h0 : (Sigma f (MpElem i * ofSL ModularGroup.T
        - ∑ j : Fin 6, (sigmaHom ModularGroup.T) i j • MpElem j)) 0 k = 0 := by
      have hh := congr_fun (Sigma_idealIOdd_row0 (rowDiffOdd ModularGroup.T i) hfS hfT
        (rowDiffOdd_mem_idealIOdd ModularGroup.T i) hrow1 hrow2 hmm) k
      simpa only [rowDiffOdd, Pi.zero_apply] using hh
    have h1 := h0
    rw [map_sub, map_sum] at h1
    simp only [map_smul, Matrix.sub_apply, Pi.zero_apply] at h1
    have key : (Sigma f (MpElem i * ofSL ModularGroup.T)) 0 k
        = (∑ x : Fin 6, (sigmaHom ModularGroup.T) i x • (Sigma f (MpElem x))) 0 k :=
      sub_eq_zero.mp h1
    have hA : (Sigma f (MpElem i * ofSL ModularGroup.T)) 0 k = (oddMu i * oddMT) 0 k := by
      rw [map_mul, Sigma_ofSL, hfT, Sigma_Mp i hfS hfT]
    have hB : (∑ x : Fin 6, (sigmaHom ModularGroup.T) i x • (Sigma f (MpElem x))) 0 k
        = (sigmaHom ModularGroup.T) i k := by
      rw [Matrix.sum_apply]
      simp only [Matrix.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single k]
      · rw [Sigma_Mp_row k k hfS hfT hrow3]; simp
      · intro b _ hb
        rw [Sigma_Mp_row b k hfS hfT hrow3, if_neg (fun h : k = b => hb h.symm), mul_zero]
      · intro hk; exact absurd (Finset.mem_univ k) hk
    have hC : (oddMu i * oddMT) 0 k = oddMT i k := by
      rw [Matrix.mul_apply, Finset.sum_eq_single i]
      · rw [hrow3 i i]; simp
      · intro b _ hb
        rw [hrow3 i b, if_neg hb, zero_mul]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    rw [← hB, ← key, hA, hC]
  · ext i k
    have h0 : (Sigma f (MpElem i * ofSL ModularGroup.S
        - ∑ j : Fin 6, (sigmaHom ModularGroup.S) i j • MpElem j)) 0 k = 0 := by
      have hh := congr_fun (Sigma_idealIOdd_row0 (rowDiffOdd ModularGroup.S i) hfS hfT
        (rowDiffOdd_mem_idealIOdd ModularGroup.S i) hrow1 hrow2 hmm) k
      simpa only [rowDiffOdd, Pi.zero_apply] using hh
    have h1 := h0
    rw [map_sub, map_sum] at h1
    simp only [map_smul, Matrix.sub_apply, Pi.zero_apply] at h1
    have key : (Sigma f (MpElem i * ofSL ModularGroup.S)) 0 k
        = (∑ x : Fin 6, (sigmaHom ModularGroup.S) i x • (Sigma f (MpElem x))) 0 k :=
      sub_eq_zero.mp h1
    have hA : (Sigma f (MpElem i * ofSL ModularGroup.S)) 0 k = (oddMu i * oddMS) 0 k := by
      rw [map_mul, Sigma_ofSL, hfS, Sigma_Mp i hfS hfT]
    have hB : (∑ x : Fin 6, (sigmaHom ModularGroup.S) i x • (Sigma f (MpElem x))) 0 k
        = (sigmaHom ModularGroup.S) i k := by
      rw [Matrix.sum_apply]
      simp only [Matrix.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single k]
      · rw [Sigma_Mp_row k k hfS hfT hrow3]; simp
      · intro b _ hb
        rw [Sigma_Mp_row b k hfS hfT hrow3, if_neg (fun h : k = b => hb h.symm), mul_zero]
      · intro hk; exact absurd (Finset.mem_univ k) hk
    have hC : (oddMu i * oddMS) 0 k = oddMS i k := by
      rw [Matrix.mul_apply, Finset.sum_eq_single i]
      · rw [hrow3 i i]; simp
      · intro b _ hb
        rw [hrow3 i b, if_neg hb, zero_mul]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    rw [← hB, ← key, hA, hC]

/-! ## The odd carry combination -/

/-- `(T-1)² a + S (T-1)² b + (1+z) c` as an element of `R`, the odd-weight companion of
`Work.Asymptotics.carryComb`. -/
noncomputable def carryCombO (a b c : R) : R :=
  (R_T - 1) ^ 2 * a + R_S * (R_T - 1) ^ 2 * b + (Rneg + 1) * c

lemma carryCombO_add (a b c a' b' c' : R) :
    carryCombO (a + a') (b + b') (c + c') = carryCombO a b c + carryCombO a' b' c' := by
  simp only [carryCombO]; noncomm_ring

lemma carryCombO_smul (x : ℂ) (a b c : R) :
    carryCombO (x • a) (x • b) (x • c) = x • carryCombO a b c := by
  simp only [carryCombO, mul_smul_comm, smul_add]

lemma carryCombO_triSum {ι : Type*} (s : Finset ι) (f : ι → R × R × R) :
    carryCombO (triSum s f).1 (triSum s f).2.1 (triSum s f).2.2
      = ∑ i ∈ s, carryCombO (f i).1 (f i).2.1 (f i).2.2 := by
  simp only [triSum_fst, triSum_snd, triSum_thd, carryCombO, Finset.mul_sum,
    Finset.sum_add_distrib]

lemma carryCombO_triSmul (x : ℂ) (p : R × R × R) :
    carryCombO (triSmul x p).1 (triSmul x p).2.1 (triSmul x p).2.2
      = x • carryCombO p.1 p.2.1 p.2.2 := carryCombO_smul x _ _ _

lemma carryCombO_triAdd (p q : R × R × R) :
    carryCombO (triAdd p q).1 (triAdd p q).2.1 (triAdd p q).2.2
      = carryCombO p.1 p.2.1 p.2.2 + carryCombO q.1 q.2.1 q.2.2 :=
  carryCombO_add _ _ _ _ _ _

lemma carryCombO_triMulOf (p : R × R × R) (g : SL(2,ℤ)) :
    carryCombO (triMulOf p g).1 (triMulOf p g).2.1 (triMulOf p g).2.2
      = carryCombO p.1 p.2.1 p.2.2 * MonoidAlgebra.of ℂ SL(2,ℤ) g := by
  simp only [carryCombO, triMulOf]
  noncomm_ring

/-! ## The atom carries -/

lemma row0T : (∑ j : Fin 6, oddMT 0 j • MpElem j) = (2:ℂ) • MpElem 0 - MpElem 1 := by
  rw [Fin.sum_univ_six]; simp [oddMT, sub_eq_add_neg]
lemma row1T : (∑ j : Fin 6, oddMT 1 j • MpElem j) = MpElem 0 := by
  rw [Fin.sum_univ_six]; simp [oddMT, sub_eq_add_neg]
lemma row2T : (∑ j : Fin 6, oddMT 2 j • MpElem j) = (2:ℂ) • MpElem 3 - MpElem 5 := by
  rw [Fin.sum_univ_six]; simp [oddMT, sub_eq_add_neg]
lemma row3T : (∑ j : Fin 6, oddMT 3 j • MpElem j) = (2:ℂ) • MpElem 3 - MpElem 4 := by
  rw [Fin.sum_univ_six]; simp [oddMT, sub_eq_add_neg]
lemma row4T : (∑ j : Fin 6, oddMT 4 j • MpElem j) = MpElem 3 := by
  rw [Fin.sum_univ_six]; simp [oddMT, sub_eq_add_neg]
lemma row5T : (∑ j : Fin 6, oddMT 5 j • MpElem j) = (2:ℂ) • MpElem 0 + MpElem 2 := by
  rw [Fin.sum_univ_six]; simp [oddMT, sub_eq_add_neg]
lemma row0S : (∑ j : Fin 6, oddMS 0 j • MpElem j) = MpElem 3 := by
  rw [Fin.sum_univ_six]; simp [oddMS, sub_eq_add_neg]
lemma row1S : (∑ j : Fin 6, oddMS 1 j • MpElem j) = (2:ℂ) • MpElem 3 - MpElem 5 := by
  rw [Fin.sum_univ_six]; simp [oddMS, sub_eq_add_neg]
lemma row2S : (∑ j : Fin 6, oddMS 2 j • MpElem j) = (-2:ℂ) • MpElem 3 + MpElem 4 := by
  rw [Fin.sum_univ_six]; simp [oddMS, sub_eq_add_neg]
lemma row3S : (∑ j : Fin 6, oddMS 3 j • MpElem j) = -MpElem 0 := by
  rw [Fin.sum_univ_six]; simp [oddMS, sub_eq_add_neg]
lemma row4S : (∑ j : Fin 6, oddMS 4 j • MpElem j) = (-2:ℂ) • MpElem 0 - MpElem 2 := by
  rw [Fin.sum_univ_six]; simp [oddMS, sub_eq_add_neg]
lemma row5S : (∑ j : Fin 6, oddMS 5 j • MpElem j) = (-2:ℂ) • MpElem 0 + MpElem 1 := by
  rw [Fin.sum_univ_six]; simp [oddMS, sub_eq_add_neg]

/-- The carries of the atom `T` in each of the six rows. -/
noncomputable def atomT : Fin 6 → R × R × R
  | 0 => (R_Tinv, 0, 0)
  | 1 => (0, 0, 0)
  | 2 => (R_Tinv * R_S, 0, 0)
  | 3 => (0, R_Tinv, 0)
  | 4 => (0, 0, 0)
  | 5 => (0, -(R_Tinv * R_S), R_T * R_S * R_T - 2)

/-- The carries of the atom `S` in each of the six rows. -/
noncomputable def atomS : Fin 6 → R × R × R
  | 0 => (0, 0, 0)
  | 1 => (R_Tinv * R_S, 0, 0)
  | 2 => (0, -R_Tinv, R_S * R_T)
  | 3 => (0, 0, 1)
  | 4 => (0, R_Tinv * R_S, 2)
  | 5 => (-R_Tinv, 0, R_T)


private lemma two_smul_R (x : R) : (2:ℂ) • x = x + x := by
  rw [show (2:ℂ) = ((2:ℕ):ℂ) from by norm_num, Nat.cast_smul_eq_nsmul, two_nsmul]
private lemma neg_two_smul_R (x : R) : (-2:ℂ) • x = -(x + x) := by
  rw [neg_smul 2 x, two_smul_R]
private lemma neg_one_smul_R (x : R) : (-1:ℂ) • x = -x := by
  rw [neg_smul 1 x, one_smul]

private lemma atomT_spec_0 : carryCombO R_Tinv 0 0 = rowDiffOdd ModularGroup.T 0 := by
  rw [rowDiffOdd, sigmaHom_odd_generators.1, row0T]
  simp only [show ofSL ModularGroup.T = R_T from rfl, spMp_MpElem_zero, spMp_MpElem_one,
    carryCombO, two_smul_R, neg_one_smul_R, mul_zero, add_zero, zero_mul, mul_one, one_mul,
    zero_add]
  rw [spMp_T2_mul_RTi]
  noncomm_ring

private lemma atomT_spec_1 : carryCombO 0 0 0 = rowDiffOdd ModularGroup.T 1 := by
  rw [rowDiffOdd, sigmaHom_odd_generators.1, row1T]
  simp only [show ofSL ModularGroup.T = R_T from rfl, spMp_MpElem_zero, spMp_MpElem_one,
    carryCombO, two_smul_R, neg_one_smul_R, mul_zero, add_zero, zero_mul, mul_one, one_mul,
    zero_add]
  rw [spMp_R_Tinv_mul_R_T]
  noncomm_ring

private lemma atomT_spec_2 : carryCombO (R_Tinv * R_S) 0 0 = rowDiffOdd ModularGroup.T 2 := by
  rw [rowDiffOdd, sigmaHom_odd_generators.1, row2T]
  simp only [show ofSL ModularGroup.T = R_T from rfl, spMp_MpElem_two, spMp_MpElem_three,
    spMp_MpElem_five, spMp_STST, carryCombO, two_smul_R, neg_one_smul_R, mul_zero, add_zero,
    zero_mul, mul_one, one_mul, zero_add]
  rw [show (R_T - 1)^2 * (R_Tinv * R_S) = ((R_T - 1)^2 * R_Tinv) * R_S from by noncomm_ring,
    spMp_T2_mul_RTi]
  noncomm_ring

private lemma atomT_spec_3 : carryCombO 0 R_Tinv 0 = rowDiffOdd ModularGroup.T 3 := by
  rw [rowDiffOdd, sigmaHom_odd_generators.1, row3T]
  simp only [show ofSL ModularGroup.T = R_T from rfl, spMp_MpElem_three, spMp_MpElem_four,
    carryCombO, two_smul_R, neg_one_smul_R, mul_zero, add_zero, zero_mul, mul_one, one_mul,
    zero_add]
  rw [spMp_S_T2_Tinv]
  noncomm_ring

private lemma atomT_spec_4 : carryCombO 0 0 0 = rowDiffOdd ModularGroup.T 4 := by
  rw [rowDiffOdd, sigmaHom_odd_generators.1, row4T]
  simp only [show ofSL ModularGroup.T = R_T from rfl, spMp_MpElem_three, spMp_MpElem_four,
    carryCombO, two_smul_R, neg_one_smul_R, mul_zero, add_zero, zero_mul, mul_one, one_mul,
    zero_add]
  rw [mul_assoc, spMp_R_Tinv_mul_R_T, mul_one]
  noncomm_ring

private lemma atomT_spec_5 : carryCombO 0 (-(R_Tinv * R_S)) (R_T * R_S * R_T - 2) =
    rowDiffOdd ModularGroup.T 5 := by
  rw [rowDiffOdd, sigmaHom_odd_generators.1, row5T]
  simp only [show ofSL ModularGroup.T = R_T from rfl, spMp_MpElem_zero, spMp_MpElem_two,
    spMp_MpElem_five, carryCombO, two_smul_R, neg_one_smul_R, mul_zero, add_zero, zero_mul,
    mul_one, one_mul, zero_add]
  rw [show R_S * (R_T - 1)^2 * (-(R_Tinv * R_S))
      = -((R_S * (R_T - 1)^2 * R_Tinv) * R_S) from by noncomm_ring, spMp_i_mul_S]
  noncomm_ring

private lemma atomS_spec_0 : carryCombO 0 0 0 = rowDiffOdd ModularGroup.S 0 := by
  rw [rowDiffOdd, sigmaHom_odd_generators.2, row0S]
  simp only [show ofSL ModularGroup.S = R_S from rfl, spMp_MpElem_zero, spMp_MpElem_three,
    carryCombO, two_smul_R, neg_one_smul_R, mul_zero, add_zero, zero_mul, mul_one, one_mul,
    zero_add]
  noncomm_ring

private lemma atomS_spec_1 : carryCombO (R_Tinv * R_S) 0 0 = rowDiffOdd ModularGroup.S 1 := by
  rw [rowDiffOdd, sigmaHom_odd_generators.2, row1S]
  simp only [show ofSL ModularGroup.S = R_S from rfl, spMp_MpElem_one, spMp_MpElem_three,
    spMp_MpElem_five, carryCombO, two_smul_R, neg_one_smul_R, mul_zero, add_zero, zero_mul,
    mul_one, one_mul, zero_add]
  rw [show (R_T - 1)^2 * (R_Tinv * R_S) = ((R_T - 1)^2 * R_Tinv) * R_S from by noncomm_ring,
    spMp_T2_mul_RTi]
  noncomm_ring

private lemma atomS_spec_2 : carryCombO 0 (-R_Tinv) (R_S * R_T) = rowDiffOdd ModularGroup.S 2 := by
  rw [rowDiffOdd, sigmaHom_odd_generators.2, row2S]
  simp only [show ofSL ModularGroup.S = R_S from rfl, spMp_MpElem_two, spMp_MpElem_three,
    spMp_MpElem_four, spMp_R_S_mul_R_S, carryCombO, two_smul_R, neg_two_smul_R, neg_one_smul_R,
    mul_zero, add_zero, zero_mul, mul_one, one_mul, zero_add]
  rw [show R_S * R_T * R_S * R_S = (R_S * R_T) * (R_S * R_S) from by noncomm_ring,
    spMp_R_S_mul_R_S, ← spMp_Rneg_comm (R_S * R_T),
    show R_S * (R_T - 1)^2 * (-R_Tinv) = -(R_S * (R_T - 1)^2 * R_Tinv) from by noncomm_ring,
    spMp_S_T2_Tinv]
  noncomm_ring

private lemma atomS_spec_3 : carryCombO 0 0 1 = rowDiffOdd ModularGroup.S 3 := by
  rw [rowDiffOdd, sigmaHom_odd_generators.2, row3S]
  simp only [show ofSL ModularGroup.S = R_S from rfl, spMp_MpElem_zero, spMp_MpElem_three,
    spMp_R_S_mul_R_S, carryCombO, two_smul_R,
    neg_one_smul_R, mul_zero, add_zero, zero_mul, mul_one, one_mul, zero_add]
  noncomm_ring

private lemma atomS_spec_4 : carryCombO 0 (R_Tinv * R_S) 2 = rowDiffOdd ModularGroup.S 4 := by
  rw [rowDiffOdd, sigmaHom_odd_generators.2, row4S]
  simp only [show ofSL ModularGroup.S = R_S from rfl, spMp_MpElem_four, spMp_MpElem_zero,
    spMp_MpElem_two, spMp_STiS, carryCombO, two_smul_R, neg_two_smul_R, neg_one_smul_R,
    mul_zero, add_zero, zero_mul, mul_one, one_mul, zero_add]
  rw [show R_S * (R_T - 1)^2 * (R_Tinv * R_S)
      = (R_S * (R_T - 1)^2 * R_Tinv) * R_S from by noncomm_ring, spMp_i_mul_S]
  noncomm_ring

private lemma atomS_spec_5 : carryCombO (-R_Tinv) 0 R_T = rowDiffOdd ModularGroup.S 5 := by
  rw [rowDiffOdd, sigmaHom_odd_generators.2, row5S]
  simp only [show ofSL ModularGroup.S = R_S from rfl, spMp_MpElem_zero, spMp_MpElem_one,
    spMp_MpElem_five, spMp_R_S_mul_R_S, carryCombO, two_smul_R, neg_two_smul_R,
    neg_one_smul_R, mul_zero, add_zero, zero_mul, mul_one, one_mul, zero_add]
  rw [show R_T * R_S * R_S = R_T * (R_S * R_S) from by noncomm_ring,
    show R_S * R_S = Rneg from spMp_R_S_mul_R_S, ← spMp_Rneg_comm R_T,
    show (R_T - 1)^2 * (-R_Tinv) = -((R_T - 1)^2 * R_Tinv) from by noncomm_ring,
    spMp_T2_mul_RTi]
  noncomm_ring

private lemma Frob_T_le : Frob (ModularGroup.T : SL(2,ℤ)) ≤ 4 := by
  rw [Frob_T]; rw [Real.sqrt_le_iff]; norm_num
private lemma Frob_S_le : Frob (ModularGroup.S : SL(2,ℤ)) ≤ 4 := by
  rw [Frob_S]; rw [Real.sqrt_le_iff]; norm_num
private lemma Frob_Tinv_le : Frob ((ModularGroup.T)⁻¹ : SL(2,ℤ)) ≤ 4 := by
  rw [Frob_inv, Frob_T]; rw [Real.sqrt_le_iff]; norm_num

private lemma cN_one_1 : coeffNorm (1 : R) ≤ 1 := by
  rw [MonoidAlgebra.one_def]
  exact coeffNorm_of_le (1 : SL(2,ℤ))
private lemma cN_RT_1 : coeffNorm (R_T : R) ≤ 1 := coeffNorm_of_le ModularGroup.T
private lemma cN_RS_1 : coeffNorm (R_S : R) ≤ 1 := coeffNorm_of_le ModularGroup.S
private lemma cN_Tinv_1 : coeffNorm (R_Tinv : R) ≤ 1 := coeffNorm_of_le (ModularGroup.T)⁻¹
private lemma cN_two_2 : coeffNorm (2 : R) ≤ 2 := by
  have h : (2:R) = (1:R) + (1:R) := by norm_num
  rw [h]
  refine le_trans (coeffNorm_add_le _ _) ?_
  linarith [cN_one_1]
private lemma cN_one : coeffNorm (1 : R) ≤ 3 := le_trans cN_one_1 (by norm_num)
private lemma cN_RT : coeffNorm (R_T : R) ≤ 3 := le_trans cN_RT_1 (by norm_num)
private lemma cN_Tinv : coeffNorm (R_Tinv : R) ≤ 3 := le_trans cN_Tinv_1 (by norm_num)
private lemma cN_Tinv_RS : coeffNorm (R_Tinv * R_S : R) ≤ 3 :=
  le_trans (le_trans (coeffNorm_mul_of_le R_Tinv ModularGroup.S) cN_Tinv_1) (by norm_num)
private lemma cN_RS_RT : coeffNorm (R_S * R_T : R) ≤ 3 :=
  le_trans (le_trans (coeffNorm_mul_of_le R_S ModularGroup.T) cN_RS_1) (by norm_num)
private lemma cN_TST_1 : coeffNorm (R_T * R_S * R_T : R) ≤ 1 :=
  le_trans (coeffNorm_mul_of_le (R_T * R_S) ModularGroup.T)
    (le_trans (coeffNorm_mul_of_le R_T ModularGroup.S) cN_RT_1)
private lemma cN_TST_sub_two : coeffNorm (R_T * R_S * R_T - 2 : R) ≤ 3 := by
  have h : (R_T * R_S * R_T - 2 : R) = R_T * R_S * R_T + -(2:R) := by simp [sub_eq_add_neg]
  rw [h]
  refine le_trans (coeffNorm_add_le _ _) ?_
  linarith [cN_TST_1, coeffNorm_neg_le (2:R), cN_two_2]
private lemma cN_two : coeffNorm (2 : R) ≤ 3 := le_trans cN_two_2 (by norm_num)
private lemma cN_Tinv_RS_neg : coeffNorm (-(R_Tinv * R_S) : R) ≤ 3 :=
  le_trans (le_trans (coeffNorm_neg_le _) cN_Tinv_RS) (by norm_num)

private lemma sF_RS_RT : supportFrobLe (R_S * R_T : R) 100 :=
  supportFrobLe_mono (supportFrobLe_mul_of (supportFrobLe_of_le ModularGroup.S) ModularGroup.T)
    (by nlinarith [Frob_S_le, Frob_T_le, Frob_nonneg (ModularGroup.S), Frob_nonneg (ModularGroup.T)])
private lemma sF_Tinv_RS : supportFrobLe (R_Tinv * R_S : R) 100 :=
  supportFrobLe_mono
    (supportFrobLe_mul_of (supportFrobLe_of_le (ModularGroup.T)⁻¹) ModularGroup.S)
    (by nlinarith [Frob_Tinv_le, Frob_S_le, Frob_nonneg (ModularGroup.S)])
private lemma sF_TST : supportFrobLe (R_T * R_S * R_T : R) 100 := by
  refine supportFrobLe_mono
    (supportFrobLe_mul_of (supportFrobLe_mul_of (supportFrobLe_of_le ModularGroup.T)
      ModularGroup.S) ModularGroup.T) ?_
  have h1 : Frob (ModularGroup.T) * Frob (ModularGroup.S) * Frob (ModularGroup.T)
      ≤ 4 * 4 * 4 :=
    mul_le_mul (mul_le_mul Frob_T_le Frob_S_le (Frob_nonneg _) (by norm_num)) Frob_T_le
      (Frob_nonneg _) (by norm_num)
  linarith
private lemma sF_one : supportFrobLe (1 : R) 100 :=
  supportFrobLe_mono (supportFrobLe_of_le (1 : SL(2,ℤ))) (by
    rw [show Frob (1 : SL(2,ℤ)) = Real.sqrt 2 from Frob_one]
    rw [Real.sqrt_le_iff]; norm_num)
private lemma sF_Tinv : supportFrobLe (R_Tinv : R) 100 :=
  supportFrobLe_mono (supportFrobLe_of_le (ModularGroup.T)⁻¹)
    (le_trans Frob_Tinv_le (by norm_num))
private lemma sF_RT : supportFrobLe (R_T : R) 100 :=
  supportFrobLe_mono (supportFrobLe_of_le ModularGroup.T) (le_trans Frob_T_le (by norm_num))
private lemma sF_RS : supportFrobLe (R_S : R) 100 :=
  supportFrobLe_mono (supportFrobLe_of_le ModularGroup.S) (le_trans Frob_S_le (by norm_num))
private lemma sF_two : supportFrobLe (2 : R) 100 := by
  have h : (2:R) = (1:R) + (1:R) := by norm_num
  rw [h]
  exact supportFrobLe_mono (supportFrobLe_add sF_one sF_one) (by norm_num : max (100:ℝ) 100 ≤ 100)
private lemma sF_TST_sub_two : supportFrobLe (R_T * R_S * R_T - 2 : R) 100 := by
  have h : (R_T * R_S * R_T - 2 : R) = R_T * R_S * R_T + -(2:R) := by simp [sub_eq_add_neg]
  rw [h]
  exact supportFrobLe_mono (supportFrobLe_add sF_TST (supportFrobLe_neg sF_two)) (by norm_num : max (100:ℝ) 100 ≤ 100)
private lemma sF_Tinv_RS_neg : supportFrobLe (-(R_Tinv * R_S) : R) 100 :=
  supportFrobLe_neg sF_Tinv_RS

lemma atomT_spec (i : Fin 6) :
    carryCombO (atomT i).1 (atomT i).2.1 (atomT i).2.2 = rowDiffOdd ModularGroup.T i := by
  fin_cases i
  · convert atomT_spec_0 using 2 <;> simp [atomT]
  · convert atomT_spec_1 using 2 <;> simp [atomT]
  · convert atomT_spec_2 using 2 <;> simp [atomT]
  · convert atomT_spec_3 using 2 <;> simp [atomT]
  · convert atomT_spec_4 using 2 <;> simp [atomT]
  · convert atomT_spec_5 using 2 <;> simp [atomT]

lemma atomS_spec (i : Fin 6) :
    carryCombO (atomS i).1 (atomS i).2.1 (atomS i).2.2 = rowDiffOdd ModularGroup.S i := by
  fin_cases i
  · convert atomS_spec_0 using 2 <;> simp [atomS]
  · convert atomS_spec_1 using 2 <;> simp [atomS]
  · convert atomS_spec_2 using 2 <;> simp [atomS]
  · convert atomS_spec_3 using 2 <;> simp [atomS]
  · convert atomS_spec_4 using 2 <;> simp [atomS]
  · convert atomS_spec_5 using 2 <;> simp [atomS]

private lemma cN_zero_c : coeffNorm (0 : R) ≤ 3 := by rw [coeffNorm_zero]; norm_num
private lemma sF_zero_c : supportFrobLe (0 : R) 100 := supportFrobLe_zero 100
private lemma cN_neg_Tinv : coeffNorm (-R_Tinv : R) ≤ 3 :=
  le_trans (coeffNorm_neg_le _) (le_trans cN_Tinv (by norm_num))
private lemma sF_neg_Tinv : supportFrobLe (-R_Tinv : R) 100 := supportFrobLe_neg sF_Tinv

lemma atomT_bound (i : Fin 6) : CB (atomT i) 3 100 := by
  fin_cases i <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [atomT] <;>
    first
      | exact cN_Tinv | exact cN_zero_c | exact cN_Tinv_RS | exact cN_Tinv_RS_neg
      | exact cN_TST_sub_two
      | exact sF_Tinv | exact sF_zero_c | exact sF_Tinv_RS
      | exact sF_Tinv_RS_neg | exact sF_TST_sub_two

lemma atomS_bound (i : Fin 6) : CB (atomS i) 3 100 := by
  fin_cases i <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [atomS] <;>
    first
      | exact cN_zero_c | exact cN_Tinv_RS | exact cN_neg_Tinv | exact cN_RS_RT
      | exact cN_one | exact cN_two | exact cN_RT | exact cN_TST_sub_two
      | exact sF_zero_c | exact sF_Tinv_RS | exact sF_neg_Tinv | exact sF_RS_RT
      | exact sF_one | exact sF_two | exact sF_RT | exact sF_TST_sub_two




end Work.Asymptotics

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups MonoidAlgebra ModularForm
open Work.Kernels

namespace Work.Asymptotics

set_option maxHeartbeats 4000000

lemma rowDiffOdd_one (i : Fin 6) : rowDiffOdd (1 : SL(2,ℤ)) i = 0 := by
  rw [rowDiffOdd, ofSL_one, map_one, mul_one]
  have hsum : (∑ j : Fin 6, (1 : Matrix (Fin 6) (Fin 6) ℂ) i j • MpElem j) = MpElem i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      rw [Matrix.one_apply, if_neg (fun h : i = b => hb h.symm), zero_smul]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  rw [hsum, sub_self]

lemma sigmaHom_T_pow (n : ℕ) : sigmaHom (ModularGroup.T ^ n) = oddMT ^ n := by
  rw [map_pow, sigmaHom_odd_generators.1]

lemma sigmaHom_Tinv_eq : sigmaHom (ModularGroup.T⁻¹) = oddMTi := by
  have h : oddMT * sigmaHom (ModularGroup.T⁻¹) = 1 := by
    have h0 : sigmaHom ((ModularGroup.T) * ModularGroup.T⁻¹) = 1 := by
      rw [mul_inv_cancel, map_one]
    rw [map_mul, sigmaHom_odd_generators.1] at h0
    exact h0
  have h2 : oddMT⁻¹ = sigmaHom (ModularGroup.T⁻¹) := Matrix.inv_eq_right_inv h
  rw [← h2, oddMT_inv]

lemma sigmaHom_Tinv_pow (m : ℕ) : sigmaHom ((ModularGroup.T⁻¹) ^ m) = oddMTi ^ m := by
  rw [map_pow, sigmaHom_Tinv_eq]

noncomputable def sigmaOfTO (k : ℤ) : Matrix (Fin 6) (Fin 6) ℂ :=
  if 0 ≤ k then oddMT ^ k.toNat else oddMTi ^ (-k).toNat

lemma zpow_eq_inv_pow {k : ℤ} (h : ¬ 0 ≤ k) :
    (ModularGroup.T : SL(2,ℤ)) ^ k = (ModularGroup.T⁻¹) ^ (-k).toNat := by
  have hpos : (0:ℤ) ≤ -k := by omega
  have hm : ((-k).toNat : ℤ) = -k := Int.toNat_of_nonneg hpos
  have h1 : (ModularGroup.T⁻¹ : SL(2,ℤ)) ^ ((-k).toNat : ℤ) = (ModularGroup.T⁻¹) ^ (-k) := by
    rw [hm]
  have h2 : (ModularGroup.T⁻¹ : SL(2,ℤ)) ^ (-k) = (ModularGroup.T) ^ k := by
    rw [_root_.inv_zpow, ← _root_.zpow_neg, neg_neg]
  rw [← h2, ← h1]
  exact zpow_natCast (ModularGroup.T⁻¹ : SL(2,ℤ)) ((-k).toNat)

lemma sigmaOfTO_nonneg {k : ℤ} (h : 0 ≤ k) :
    sigmaOfTO k = sigmaHom (ModularGroup.T ^ k) := by
  rw [sigmaOfTO, if_pos h,
    show (ModularGroup.T : SL(2,ℤ)) ^ k = ModularGroup.T ^ k.toNat from by
      rw [← zpow_natCast, Int.toNat_of_nonneg h],
    sigmaHom_T_pow]

lemma sigmaOfTO_neg {k : ℤ} (h : ¬ 0 ≤ k) :
    sigmaOfTO k = sigmaHom (ModularGroup.T ^ k) := by
  rw [sigmaOfTO, if_neg h, zpow_eq_inv_pow h, sigmaHom_Tinv_pow]

lemma sigmaOfTO_eq (k : ℤ) : sigmaOfTO k = sigmaHom (ModularGroup.T ^ k) := by
  by_cases h : 0 ≤ k
  · exact sigmaOfTO_nonneg h
  · exact sigmaOfTO_neg h

lemma sigmaOfTO_entry_le (k : ℤ) (i j : Fin 6) :
    ‖sigmaOfTO k i j‖ ≤ 8 * (1 + |(k:ℝ)|) := by
  by_cases h : 0 ≤ k
  · rw [sigmaOfTO, if_pos h]
    refine le_trans (oddMT_pow_le k.toNat i j) ?_
    have h1 : (((k.toNat : ℕ)) : ℝ) = (k : ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg h : (((k.toNat : ℕ)) : ℤ) = k)
    rw [h1, abs_of_nonneg (by exact_mod_cast h)]
  · rw [sigmaOfTO, if_neg h]
    refine le_trans (oddMTi_pow_le (-k).toNat i j) ?_
    have h1 : ((((-k).toNat : ℕ)) : ℝ) = (-k : ℤ) := by
      exact_mod_cast (Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ -k) : ((((-k).toNat : ℕ)) : ℤ) = -k)
    rw [h1, Int.cast_neg, abs_of_nonpos (by exact_mod_cast le_of_lt (not_le.mp h))]

/-! ## The carries of `T^n` -/

noncomputable def carryTpowO (n : ℕ) (i : Fin 6) : R × R × R :=
  triSum (Finset.univ : Finset (Fin n)) (fun m =>
    triSum (Finset.univ : Finset (Fin 6)) (fun j =>
      triSmul ((oddMT ^ (n - 1 - (m : ℕ))) i j)
        (triMulOf (atomT j) (ModularGroup.T ^ (m : ℕ)))))

noncomputable def tpowHeadO (n : ℕ) (i : Fin 6) : R × R × R :=
  triSum (Finset.univ : Finset (Fin 6))
    (fun j => triSmul ((oddMT ^ n) i j) (atomT j))

lemma carryTpowO_succ_comp (cc : Comp) (n : ℕ) (i : Fin 6) :
    cc.toFun (carryTpowO (n + 1) i)
      = cc.toFun (triAdd (tpowHeadO n i) (triMulOf (carryTpowO n i) ModularGroup.T)) := by
  classical
  have hL : carryTpowO (n + 1) i = triSum (Finset.univ : Finset (Fin (n + 1))) (fun m =>
      triSum (Finset.univ : Finset (Fin 6)) (fun j =>
        triSmul ((oddMT ^ (n + 1 - 1 - (m : ℕ))) i j)
          (triMulOf (atomT j) (ModularGroup.T ^ (m : ℕ))))) := rfl
  rw [hL, cc.sum, Fin.sum_univ_succ, cc.add]
  have hhead : cc.toFun (triSum (Finset.univ : Finset (Fin 6)) (fun j =>
        triSmul ((oddMT ^ (n + 1 - 1 - ((0 : Fin (n + 1)) : ℕ))) i j)
          (triMulOf (atomT j) (ModularGroup.T ^ ((0 : Fin (n + 1)) : ℕ)))))
      = cc.toFun (tpowHeadO n i) := by
    rw [show tpowHeadO n i = triSum (Finset.univ : Finset (Fin 6))
        (fun j => triSmul ((oddMT ^ n) i j) (atomT j)) from rfl]
    simp only [cc.sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hexp : n + 1 - 1 - ((0 : Fin (n + 1)) : ℕ) = n := by
      simp only [Fin.val_zero, Nat.sub_zero, Nat.add_sub_cancel]
    rw [hexp, cc.smul, cc.mul, cc.smul]
    rw [show (ModularGroup.T : SL(2,ℤ)) ^ ((0 : Fin (n + 1)) : ℕ) = 1 from by
      rw [show ((0 : Fin (n + 1)) : ℕ) = 0 from Fin.val_zero _, pow_zero], map_one, mul_one]
  have htail : (∑ m ∈ (Finset.univ : Finset (Fin n)),
        cc.toFun (triSum (Finset.univ : Finset (Fin 6)) (fun j =>
          triSmul ((oddMT ^ (n + 1 - 1 - ((Fin.succ m : Fin (n + 1)) : ℕ))) i j)
            (triMulOf (atomT j) (ModularGroup.T ^ ((Fin.succ m : Fin (n + 1)) : ℕ))))))
      = cc.toFun (triMulOf (carryTpowO n i) ModularGroup.T) := by
    rw [cc.mul]
    rw [show carryTpowO n i = triSum (Finset.univ : Finset (Fin n)) (fun m =>
        triSum (Finset.univ : Finset (Fin 6)) (fun j =>
          triSmul ((oddMT ^ (n - 1 - (m : ℕ))) i j)
            (triMulOf (atomT j) (ModularGroup.T ^ (m : ℕ))))) from rfl]
    simp only [cc.sum]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [cc.smul, cc.mul, cc.smul, cc.mul]
    have hexp : n + 1 - 1 - ((Fin.succ m : Fin (n + 1)) : ℕ) = n - 1 - (m : ℕ) := by
      simp only [Fin.val_succ]; omega
    rw [hexp]
    have hg : (ModularGroup.T : SL(2,ℤ)) ^ (((Fin.succ m : Fin (n + 1)) : ℕ))
        = ModularGroup.T ^ (m : ℕ) * ModularGroup.T := by
      rw [Fin.val_succ, pow_succ]
    rw [hg, map_mul, smul_mul_assoc, mul_assoc]
  rw [← hhead, ← htail]

lemma carryTpowO_succ (n : ℕ) (i : Fin 6) :
    carryTpowO (n + 1) i = triAdd (tpowHeadO n i) (triMulOf (carryTpowO n i) ModularGroup.T) := by
  have h1 := carryTpowO_succ_comp Comp.fst n i
  have h2 := carryTpowO_succ_comp Comp.snd n i
  have h3 := carryTpowO_succ_comp Comp.thd n i
  exact tri_ext h1 h2 h3

end Work.Asymptotics

namespace Work.Asymptotics

theorem carryTpowO_spec (n : ℕ) : ∀ i : Fin 6,
    carryCombO (carryTpowO n i).1 (carryTpowO n i).2.1 (carryTpowO n i).2.2
      = rowDiffOdd (ModularGroup.T ^ n) i := by
  induction n with
  | zero =>
    intro i
    have h0 : carryTpowO 0 i = ((0, 0, 0) : R × R × R) := by
      refine tri_ext ?_ ?_ ?_ <;> simp [carryTpowO, triSum]
    rw [h0, pow_zero, rowDiffOdd_one]
    simp [carryCombO]
  | succ n ih =>
    intro i
    rw [carryTpowO_succ, carryCombO_triAdd]
    have hhead : carryCombO (tpowHeadO n i).1 (tpowHeadO n i).2.1 (tpowHeadO n i).2.2
        = ∑ j : Fin 6, ((oddMT ^ n) i j)
            • carryCombO (atomT j).1 (atomT j).2.1 (atomT j).2.2 := by
      rw [show tpowHeadO n i = triSum (Finset.univ : Finset (Fin 6))
          (fun j => triSmul ((oddMT ^ n) i j) (atomT j)) from rfl]
      rw [carryCombO_triSum]
      exact Finset.sum_congr rfl fun j _ => carryCombO_triSmul _ _
    rw [hhead, carryCombO_triMulOf]
    rw [show (∑ j : Fin 6, ((oddMT ^ n) i j)
          • carryCombO (atomT j).1 (atomT j).2.1 (atomT j).2.2)
        = ∑ j : Fin 6, ((oddMT ^ n) i j) • rowDiffOdd ModularGroup.T j from
      Finset.sum_congr rfl fun j _ => by rw [atomT_spec j]]
    rw [ih i]
    rw [show (oddMT ^ n) = sigmaHom (ModularGroup.T ^ n) from (sigmaHom_T_pow n).symm]
    rw [show rowDiffOdd (ModularGroup.T ^ (n + 1)) i
        = (∑ j : Fin 6, sigmaHom (ModularGroup.T ^ n) i j • rowDiffOdd ModularGroup.T j)
          + rowDiffOdd (ModularGroup.T ^ n) i * ofSL ModularGroup.T from by
      rw [pow_succ, rowDiffOdd_mul]]
    rw [MonoidAlgebra.of_apply]

theorem carryTpowO_bound (n : ℕ) (i : Fin 6) :
    CB (carryTpowO n i) (1000 * (1 + (n:ℝ)) ^ 3) (1000 * (1 + (n:ℝ))) := by
  classical
  have hF : ∀ m ∈ (Finset.univ : Finset (Fin n)),
      CB (triSum (Finset.univ : Finset (Fin 6)) (fun j =>
          triSmul ((oddMT ^ (n - 1 - (m : ℕ))) i j)
            (triMulOf (atomT j) (ModularGroup.T ^ (m : ℕ)))))
        (6 * (24 * (1 + (n:ℝ)))) (300 * (1 + (n:ℝ))) := by
    intro m _
    refine CB_triSum (Finset.univ : Finset (Fin 6)) _
      (Cb := 24 * (1 + (n:ℝ))) (K := 300 * (1 + (n:ℝ))) ?_
    intro j _
    refine CB_mono (CB_triSmul ((oddMT ^ (n - 1 - (m : ℕ))) i j)
      (CB_triMulOf (ModularGroup.T ^ (m : ℕ)) (atomT_bound j))) ?_ ?_
    · have h1 := oddMT_pow_le (n - 1 - (m : ℕ)) i j
      have h2 : (((n - 1 - (m : ℕ) : ℕ)) : ℝ) ≤ (n:ℝ) := by
        have : n - 1 - (m : ℕ) ≤ n := by omega
        exact_mod_cast this
      have h3 : (1 + (n:ℝ)) ≤ 2 * (1 + (n:ℝ)) := by linarith
      calc ‖(oddMT ^ (n - 1 - (m : ℕ))) i j‖ * 3
          ≤ (8 * (1 + (((n - 1 - (m : ℕ) : ℕ)) : ℝ))) * 3 :=
            mul_le_mul_of_nonneg_right h1 (by norm_num)
        _ ≤ 24 * (1 + (n:ℝ)) := by nlinarith [h2]
    · have h3 : Frob (ModularGroup.T ^ (m:ℕ)) ≤ (n:ℝ) + 2 := by
        refine le_trans (Frob_T_pow_nat_le (m:ℕ)) ?_
        have : ((m:ℕ):ℝ) ≤ (n:ℝ) := by exact_mod_cast le_of_lt m.isLt
        linarith
      calc 100 * Frob (ModularGroup.T ^ (m:ℕ)) ≤ 100 * ((n:ℝ) + 2) :=
            mul_le_mul_of_nonneg_left h3 (by norm_num)
        _ ≤ 300 * (1 + (n:ℝ)) := by nlinarith
  refine CB_mono (CB_triSum (Finset.univ : Finset (Fin n)) _
      (Cb := 6 * (24 * (1 + (n:ℝ)))) (K := 300 * (1 + (n:ℝ))) (fun m hm => hF m hm)) ?_ ?_
  · have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    have h1 : (1:ℝ) ≤ 1 + (n:ℝ) := by linarith
    have hcard : (((Finset.univ : Finset (Fin n)).card : ℕ) : ℝ) * (6 * (24 * (1 + (n:ℝ))))
        = (n:ℝ) * (144 * (1 + (n:ℝ))) := by
      rw [Finset.card_univ, Fintype.card_fin]; ring
    rw [hcard]
    nlinarith [hn0, h1, sq_nonneg ((1:ℝ) + n)]
  · have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    nlinarith

end Work.Asymptotics

namespace Work.Asymptotics

/-! ## The carries of the blocks `T^k` and `S T^k` -/

noncomputable def carryTO (k : ℤ) (i : Fin 6) : R × R × R :=
  if 0 ≤ k then carryTpowO k.toNat i
  else triMulOf (triSmul (-1) (triSum (Finset.univ : Finset (Fin 6))
    (fun j => triSmul ((sigmaOfTO k) i j) (carryTpowO (-k).toNat j)))) (ModularGroup.T ^ k)

lemma carryTO_of_pos {k : ℤ} (h : 0 ≤ k) : carryTO k = carryTpowO k.toNat := by
  funext i; rw [carryTO, if_pos h]

theorem carryTO_spec (k : ℤ) (i : Fin 6) :
    carryCombO (carryTO k i).1 (carryTO k i).2.1 (carryTO k i).2.2
      = rowDiffOdd ((ModularGroup.T) ^ k) i := by
  by_cases h : 0 ≤ k
  · rw [carryTO_of_pos h]
    have hT : ((ModularGroup.T : SL(2,ℤ)) ^ k) = (ModularGroup.T) ^ k.toNat := by
      rw [← zpow_natCast, Int.toNat_of_nonneg h]
    rw [hT]
    exact carryTpowO_spec k.toNat i
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, m = (-k).toNat := ⟨_, rfl⟩
    have hmZ : ((m : ℕ) : ℤ) = -k := by rw [hm]; exact Int.toNat_of_nonneg (by omega)
    have hkey : carryTO k i
        = triMulOf (triSmul (-1) (triSum (Finset.univ : Finset (Fin 6))
            (fun j => triSmul ((sigmaOfTO k) i j) (carryTpowO m j)))) (ModularGroup.T ^ k) := by
      rw [carryTO, if_neg h, hm]
    rw [hkey, carryCombO_triMulOf, carryCombO_triSmul, carryCombO_triSum]
    have hinner : ∀ j : Fin 6,
        carryCombO (triSmul ((sigmaOfTO k) i j) (carryTpowO m j)).1
          (triSmul ((sigmaOfTO k) i j) (carryTpowO m j)).2.1
          (triSmul ((sigmaOfTO k) i j) (carryTpowO m j)).2.2
        = (sigmaHom ((ModularGroup.T) ^ k)) i j
            • rowDiffOdd ((ModularGroup.T) ^ m) j := fun j => by
      rw [carryCombO_triSmul, sigmaOfTO_eq, carryTpowO_spec m j]
    rw [Finset.sum_congr rfl (fun j _ => hinner j)]
    set S : R := ∑ j : Fin 6, (sigmaHom ((ModularGroup.T) ^ k)) i j
        • rowDiffOdd ((ModularGroup.T) ^ m) j with hS
    have hTmul : (ModularGroup.T : SL(2,ℤ)) ^ k * ModularGroup.T ^ m = 1 := by
      rw [← zpow_natCast (ModularGroup.T) m, ← _root_.zpow_add, hmZ, add_neg_cancel, zpow_zero]
    have h1 : MonoidAlgebra.of ℂ (SL(2,ℤ)) (ModularGroup.T ^ k)
        * MonoidAlgebra.of ℂ (SL(2,ℤ)) (ModularGroup.T ^ m) = 1 := by
      rw [← map_mul, hTmul, map_one]
    have h2 : MonoidAlgebra.of ℂ (SL(2,ℤ)) (ModularGroup.T ^ m)
        * MonoidAlgebra.of ℂ (SL(2,ℤ)) (ModularGroup.T ^ k) = 1 := by
      rw [← map_mul,
        show ((ModularGroup.T : SL(2, ℤ)) ^ m * ModularGroup.T ^ k) = 1 from by
          rw [← zpow_natCast (ModularGroup.T) m, ← _root_.zpow_add, hmZ, neg_add_cancel, zpow_zero],
        map_one]
    have hcyc := rowDiffOdd_mul (ModularGroup.T ^ k) (ModularGroup.T ^ m) i
    rw [hTmul, rowDiffOdd_one] at hcyc
    have hzero : S + rowDiffOdd ((ModularGroup.T) ^ k) i
          * MonoidAlgebra.of ℂ (SL(2,ℤ)) (ModularGroup.T ^ m) = 0 := hcyc.symm
    have hr : rowDiffOdd ((ModularGroup.T) ^ k) i
          * MonoidAlgebra.of ℂ (SL(2,ℤ)) (ModularGroup.T ^ m) = -S := by
      have hz := hzero
      rw [add_comm] at hz
      exact eq_neg_of_add_eq_zero_left hz
    rw [show ((-1 : ℂ) • S) = -S from by rw [_root_.neg_smul, one_smul]]
    rw [← hr]
    rw [mul_assoc, h2, mul_one]

noncomputable def cbTO (k : ℤ) : ℝ := 300000 * (1 + |(k : ℝ)|) ^ 5
noncomputable def cbSTO (k : ℤ) : ℝ := 10000000 * (1 + |(k : ℝ)|) ^ 5
noncomputable def kbuO (k : ℤ) : ℝ := 10000 * (1 + |(k : ℝ)|) ^ 2

lemma cbTO_nonneg (k : ℤ) : 0 ≤ cbTO k := by
  rw [cbTO]; positivity
lemma kbuO_nonneg (k : ℤ) : 0 ≤ kbuO k := by
  rw [kbuO]; positivity
lemma one_le_one_add_absO (k : ℤ) : (1:ℝ) ≤ 1 + |(k : ℝ)| := by
  have := abs_nonneg (k : ℝ); linarith
lemma abs_add_two_le_threeO (k : ℤ) : |(k : ℝ)| + 2 ≤ 3 * (1 + |(k : ℝ)|) := by
  have := abs_nonneg (k : ℝ); linarith
lemma Frob_T_zpow_leO (k : ℤ) : Frob (ModularGroup.T ^ k) ≤ |(k : ℝ)| + 2 :=
  Frob_T_zpow_le k

theorem carryTO_bound (k : ℤ) (i : Fin 6) : CB (carryTO k i) (cbTO k) (kbuO k) := by
  by_cases h : 0 ≤ k
  · rw [carryTO_of_pos h]
    have hk : (((k.toNat : ℕ)) : ℝ) = |(k : ℝ)| := by
      have h1 : (((k.toNat : ℕ)) : ℝ) = (k : ℝ) := by
        exact_mod_cast (Int.toNat_of_nonneg h : (((k.toNat : ℕ)) : ℤ) = k)
      rw [h1, abs_of_nonneg (by exact_mod_cast h)]
    have h1 := carryTpowO_bound k.toNat i
    rw [hk] at h1
    refine CB_mono h1 ?_ ?_
    · rw [cbTO]
      have ha := one_le_one_add_absO k
      have hp : (1 + |(k : ℝ)|) ^ (3 : ℕ) ≤ (1 + |(k : ℝ)|) ^ (5 : ℕ) :=
        pow_le_pow_right₀ ha (by norm_num)
      have h0 : (0 : ℝ) ≤ (1 + |(k : ℝ)|) ^ (5 : ℕ) := pow_nonneg (by linarith [abs_nonneg (k:ℝ)]) 5
      nlinarith [hp, h0]
    · rw [kbuO]
      have ha := one_le_one_add_absO k
      have hp : (1 + |(k : ℝ)|) ^ (1 : ℕ) ≤ (1 + |(k : ℝ)|) ^ (2 : ℕ) :=
        pow_le_pow_right₀ ha (by norm_num)
      nlinarith [hp]
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, m = (-k).toNat := ⟨_, rfl⟩
    have hmZ : ((m : ℕ) : ℤ) = -k := by rw [hm]; exact Int.toNat_of_nonneg (by omega)
    have hkey : carryTO k i
        = triMulOf (triSmul (-1) (triSum (Finset.univ : Finset (Fin 6))
            (fun j => triSmul ((sigmaOfTO k) i j) (carryTpowO m j)))) (ModularGroup.T ^ k) := by
      rw [carryTO, if_neg h, hm]
    rw [hkey]
    have hmR : ((m : ℕ) : ℝ) = |(k : ℝ)| := by
      have h1 : (((m : ℕ)) : ℝ) = ((-k : ℤ) : ℝ) := by exact_mod_cast hmZ
      rw [h1, Int.cast_neg, abs_of_nonpos (by exact_mod_cast le_of_lt (not_le.mp h))]
    have hinner : ∀ j : Fin 6,
        CB (triSmul ((sigmaOfTO k) i j) (carryTpowO m j))
          (8 * (1 + |(k : ℝ)|) * (1000 * (1 + (m : ℝ)) ^ 3)) (1000 * (1 + (m : ℝ))) := by
      intro j
      refine CB_mono (CB_triSmul ((sigmaOfTO k) i j) (carryTpowO_bound m j)) ?_ (le_refl _)
      have hb := sigmaOfTO_entry_le k i j
      have h0 : (0 : ℝ) ≤ 1000 * (1 + (m : ℝ)) ^ 3 := by positivity
      calc ‖(sigmaOfTO k) i j‖ * (1000 * (1 + (m : ℝ)) ^ 3)
          ≤ (8 * (1 + |(k : ℝ)|)) * (1000 * (1 + (m : ℝ)) ^ 3) :=
            mul_le_mul_of_nonneg_right hb h0
        _ = 8 * (1 + |(k : ℝ)|) * (1000 * (1 + (m : ℝ)) ^ 3) := by ring
    have hsum : CB (triSum (Finset.univ : Finset (Fin 6))
        (fun j => triSmul ((sigmaOfTO k) i j) (carryTpowO m j)))
        (6 * (8 * (1 + |(k : ℝ)|) * (1000 * (1 + (m : ℝ)) ^ 3))) (1000 * (1 + (m : ℝ))) :=
      CB_triSum (Finset.univ : Finset (Fin 6)) _ (fun j _ => hinner j)
    have hgoal : CB (triMulOf (triSmul (-1) (triSum (Finset.univ : Finset (Fin 6))
          (fun j => triSmul ((sigmaOfTO k) i j) (carryTpowO m j)))) (ModularGroup.T ^ k))
        (6 * (8 * (1 + |(k : ℝ)|) * (1000 * (1 + (m : ℝ)) ^ 3)))
        (1000 * (1 + (m : ℝ)) * Frob (ModularGroup.T ^ k)) := by
      have hh := CB_triMulOf (ModularGroup.T ^ k) (CB_triSmul (-1) hsum)
      simpa using hh
    refine CB_mono hgoal ?_ ?_
    · rw [cbTO, hmR]
      have ha : (0 : ℝ) ≤ 1 + |(k : ℝ)| := by linarith [abs_nonneg (k:ℝ)]
      have h5 : (0 : ℝ) ≤ (1 + |(k : ℝ)|) ^ (5 : ℕ) := pow_nonneg ha 5
      have hp : (1 + |(k : ℝ)|) ^ (4 : ℕ) ≤ (1 + |(k : ℝ)|) ^ (5 : ℕ) :=
        pow_le_pow_right₀ (one_le_one_add_absO k) (by norm_num)
      nlinarith [h5, hp]
    · rw [kbuO, hmR]
      have ha : (0 : ℝ) ≤ 1 + |(k : ℝ)| := by linarith [abs_nonneg (k:ℝ)]
      have hF := Frob_T_zpow_leO k
      have h2 := abs_add_two_le_threeO k
      have h4 : (0 : ℝ) ≤ 1000 * (1 + |(k : ℝ)|) := by linarith
      calc 1000 * (1 + |(k : ℝ)|) * Frob (ModularGroup.T ^ k)
          ≤ 1000 * (1 + |(k : ℝ)|) * (|(k : ℝ)| + 2) :=
            mul_le_mul_of_nonneg_left hF h4
        _ ≤ 1000 * (1 + |(k : ℝ)|) * (3 * (1 + |(k : ℝ)|)) :=
            mul_le_mul_of_nonneg_left h2 h4
        _ = 3000 * (1 + |(k : ℝ)|) ^ 2 := by ring
        _ ≤ 10000 * (1 + |(k : ℝ)|) ^ 2 := by
            nlinarith [pow_nonneg ha 2]

end Work.Asymptotics

namespace Work.Asymptotics

noncomputable def carrySTO (k : ℤ) (i : Fin 6) : R × R × R :=
  triAdd (triSum (Finset.univ : Finset (Fin 6)) (fun j => triSmul (oddMS i j) (carryTO k j)))
    (triMulOf (atomS i) (ModularGroup.T ^ k))

lemma oddMS_entry_le (i j : Fin 6) : ‖(oddMS i j : ℂ)‖ ≤ 2 := by
  fin_cases i <;> fin_cases j <;> norm_num [oddMS]

theorem carrySTO_spec (k : ℤ) (i : Fin 6) :
    carryCombO (carrySTO k i).1 (carrySTO k i).2.1 (carrySTO k i).2.2
      = rowDiffOdd (ModularGroup.S * ModularGroup.T ^ k) i := by
  unfold carrySTO
  rw [carryCombO_triAdd, carryCombO_triMulOf, carryCombO_triSum]
  have hinner : ∀ j : Fin 6,
      carryCombO (triSmul (oddMS i j) (carryTO k j)).1
        (triSmul (oddMS i j) (carryTO k j)).2.1
        (triSmul (oddMS i j) (carryTO k j)).2.2
      = (sigmaHom (ModularGroup.S)) i j • rowDiffOdd ((ModularGroup.T) ^ k) j := fun j => by
    rw [carryCombO_triSmul, carryTO_spec k j, sigmaHom_odd_generators.2]
  rw [Finset.sum_congr rfl (fun j _ => hinner j)]
  rw [atomS_spec i]
  have hcyc := rowDiffOdd_mul (ModularGroup.S) (ModularGroup.T ^ k) i
  rw [MonoidAlgebra.of_apply]
  exact hcyc.symm

theorem carrySTO_bound (k : ℤ) (i : Fin 6) : CB (carrySTO k i) (cbSTO k) (kbuO k) := by
  unfold carrySTO
  have hinner : ∀ j : Fin 6,
      CB (triSmul (oddMS i j) (carryTO k j)) (2 * cbTO k) (kbuO k) := by
    intro j
    have h0 : (0 : ℝ) ≤ cbTO k := cbTO_nonneg k
    refine CB_mono (CB_triSmul (oddMS i j) (carryTO_bound k j)) ?_ (le_refl _)
    exact mul_le_mul_of_nonneg_right (oddMS_entry_le i j) h0
  have hsum : CB (triSum (Finset.univ : Finset (Fin 6))
      (fun j => triSmul (oddMS i j) (carryTO k j))) (6 * (2 * cbTO k)) (kbuO k) :=
    CB_triSum (Finset.univ : Finset (Fin 6)) _ (fun j _ => hinner j)
  have htail : CB (triMulOf (atomS i) (ModularGroup.T ^ k)) 3
      (100 * Frob (ModularGroup.T ^ k)) := by
    have hh := CB_triMulOf (ModularGroup.T ^ k) (atomS_bound i)
    simpa using hh
  have hmain := CB_triAdd hsum htail
  have hCb : 6 * (2 * cbTO k) + 3 ≤ cbSTO k := by
    rw [cbSTO, cbTO]
    have ha : (0 : ℝ) ≤ 1 + |(k : ℝ)| := by linarith [abs_nonneg (k:ℝ)]
    have h1 : (1 : ℝ) ≤ (1 + |(k : ℝ)|) ^ (5 : ℕ) := one_le_pow₀ (one_le_one_add_absO k)
    nlinarith [h1]
  have hK : max (kbuO k) (100 * Frob (ModularGroup.T ^ k)) ≤ kbuO k := by
    refine max_le (le_refl _) ?_
    rw [kbuO]
    have ha : (0 : ℝ) ≤ 1 + |(k : ℝ)| := by linarith [abs_nonneg (k:ℝ)]
    have hF := Frob_T_zpow_leO k
    have h2 := abs_add_two_le_threeO k
    calc 100 * Frob (ModularGroup.T ^ k) ≤ 100 * (|(k : ℝ)| + 2) :=
          mul_le_mul_of_nonneg_left hF (by norm_num)
      _ ≤ 100 * (3 * (1 + |(k : ℝ)|)) := mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ ≤ 10000 * (1 + |(k : ℝ)|) ^ 2 := by nlinarith [ha]
  exact CB_mono hmain hCb hK

end Work.Asymptotics


namespace Work.Asymptotics

/-! ## The odd blocks `T^k`, `S T^k`, their carries and their bounds -/

noncomputable def carryBlkO : ℤ × Bool → Fin 6 → R × R × R
  | (k, false), i => carryTO k i
  | (k, true), i => carrySTO k i

noncomputable def BfO : ℤ × Bool → ℝ
  | (k, false) => cbTO k
  | (k, true) => cbSTO k

noncomputable def KfO : ℤ × Bool → ℝ
  | (k, false) => kbuO k
  | (k, true) => kbuO k

@[simp] lemma carryBlkO_false (k : ℤ) (i : Fin 6) : carryBlkO (k, false) i = carryTO k i := rfl
@[simp] lemma carryBlkO_true (k : ℤ) (i : Fin 6) : carryBlkO (k, true) i = carrySTO k i := rfl
@[simp] lemma BfO_false (k : ℤ) : BfO (k, false) = cbTO k := rfl
@[simp] lemma BfO_true (k : ℤ) : BfO (k, true) = cbSTO k := rfl
@[simp] lemma KfO_false (k : ℤ) : KfO (k, false) = kbuO k := rfl
@[simp] lemma KfO_true (k : ℤ) : KfO (k, true) = kbuO k := rfl

lemma BfO_nonneg (p : ℤ × Bool) : 0 ≤ BfO p := by
  rcases p with ⟨k, b⟩
  cases b
  · rw [BfO_false, cbTO]; positivity
  · rw [BfO_true, cbSTO]; positivity

lemma KfO_nonneg (p : ℤ × Bool) : 0 ≤ KfO p := by
  rcases p with ⟨k, b⟩
  cases b
  · rw [KfO_false, kbuO]; positivity
  · rw [KfO_true, kbuO]; positivity

lemma BfO_le (p : ℤ × Bool) : BfO p ≤ 10000000 * (1 + Frob (blk p)) ^ 5 := by
  rcases p with ⟨k, b⟩
  cases b
  · rw [BfO_false, blk_false, cbTO]
    have h1 : 1 + |(k : ℝ)| ≤ 1 + Frob (ModularGroup.T ^ k) := by
      have := abs_le_Frob_T_zpow k; linarith
    have h2 : (1 + |(k : ℝ)|) ^ 5 ≤ (1 + Frob (ModularGroup.T ^ k)) ^ 5 :=
      pow_le_pow_left₀ (by positivity) h1 5
    have h3 : (0 : ℝ) ≤ (1 + Frob (ModularGroup.T ^ k)) ^ 5 :=
      pow_nonneg (one_add_Frob_nonneg _) 5
    calc 300000 * (1 + |(k : ℝ)|) ^ 5
        ≤ 300000 * (1 + Frob (ModularGroup.T ^ k)) ^ 5 :=
          mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ ≤ 10000000 * (1 + Frob (ModularGroup.T ^ k)) ^ 5 :=
          mul_le_mul_of_nonneg_right (by norm_num) h3
  · rw [BfO_true, blk_true, cbSTO]
    have h1 : 1 + |(k : ℝ)| ≤ 1 + Frob (ModularGroup.S * ModularGroup.T ^ k) := by
      have := abs_le_Frob_ST_zpow k; linarith
    have h2 : (1 + |(k : ℝ)|) ^ 5
        ≤ (1 + Frob (ModularGroup.S * ModularGroup.T ^ k)) ^ 5 :=
      pow_le_pow_left₀ (by positivity) h1 5
    have h3 : (0 : ℝ) ≤ (1 + Frob (ModularGroup.S * ModularGroup.T ^ k)) ^ 5 :=
      pow_nonneg (one_add_Frob_nonneg _) 5
    calc 10000000 * (1 + |(k : ℝ)|) ^ 5
        ≤ 10000000 * (1 + Frob (ModularGroup.S * ModularGroup.T ^ k)) ^ 5 :=
          mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ ≤ 10000000 * (1 + Frob (ModularGroup.S * ModularGroup.T ^ k)) ^ 5 := le_refl _

lemma KfO_le (p : ℤ × Bool) : KfO p ≤ 10000 * (1 + Frob (blk p)) ^ 2 := by
  rcases p with ⟨k, b⟩
  cases b
  · rw [KfO_false, blk_false, kbuO]
    have h1 : 1 + |(k : ℝ)| ≤ 1 + Frob (ModularGroup.T ^ k) := by
      have := abs_le_Frob_T_zpow k; linarith
    have h2 : (1 + |(k : ℝ)|) ^ 2 ≤ (1 + Frob (ModularGroup.T ^ k)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    have h3 : (0 : ℝ) ≤ (1 + Frob (ModularGroup.T ^ k)) ^ 2 :=
      pow_nonneg (one_add_Frob_nonneg _) 2
    calc 10000 * (1 + |(k : ℝ)|) ^ 2
        ≤ 10000 * (1 + Frob (ModularGroup.T ^ k)) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ ≤ 10000 * (1 + Frob (ModularGroup.T ^ k)) ^ 2 := le_refl _
  · rw [KfO_true, blk_true, kbuO]
    have h1 : 1 + |(k : ℝ)| ≤ 1 + Frob (ModularGroup.S * ModularGroup.T ^ k) := by
      have := abs_le_Frob_ST_zpow k; linarith
    have h2 : (1 + |(k : ℝ)|) ^ 2
        ≤ (1 + Frob (ModularGroup.S * ModularGroup.T ^ k)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    have h3 : (0 : ℝ) ≤ (1 + Frob (ModularGroup.S * ModularGroup.T ^ k)) ^ 2 :=
      pow_nonneg (one_add_Frob_nonneg _) 2
    calc 10000 * (1 + |(k : ℝ)|) ^ 2
        ≤ 10000 * (1 + Frob (ModularGroup.S * ModularGroup.T ^ k)) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ ≤ 10000 * (1 + Frob (ModularGroup.S * ModularGroup.T ^ k)) ^ 2 := le_refl _

theorem carryBlkO_spec (p : ℤ × Bool) (i : Fin 6) :
    carryCombO (carryBlkO p i).1 (carryBlkO p i).2.1 (carryBlkO p i).2.2
      = rowDiffOdd (blk p) i := by
  rcases p with ⟨k, b⟩
  cases b
  · rw [carryBlkO_false, blk_false]; exact carryTO_spec k i
  · rw [carryBlkO_true, blk_true]; exact carrySTO_spec k i

theorem carryBlkO_bound (p : ℤ × Bool) (i : Fin 6) : CB (carryBlkO p i) (BfO p) (KfO p) := by
  rcases p with ⟨k, b⟩
  cases b
  · rw [carryBlkO_false, BfO_false, KfO_false]; exact carryTO_bound k i
  · rw [carryBlkO_true, BfO_true, KfO_true]; exact carrySTO_bound k i

lemma carryCombO_triMulOf_ofSL (p : R × R × R) (g : SL(2,ℤ)) :
    carryCombO (triMulOf p g).1 (triMulOf p g).2.1 (triMulOf p g).2.2
      = carryCombO p.1 p.2.1 p.2.2 * ofSL g := by
  rw [carryCombO_triMulOf, MonoidAlgebra.of_apply]

/-- Entrywise bound for `sigmaHom` of a block. -/
lemma sigma_blkO_entry_le (p : ℤ × Bool) (i j : Fin 6) :
    ‖(sigmaHom (blk p)) i j‖ ≤ 96 * (1 + Frob (blk p)) := by
  rcases p with ⟨k, b⟩
  cases b
  · rw [blk_false]
    have h := sigmaOfTO_entry_le k i j
    have h1 : 1 + |(k : ℝ)| ≤ 1 + Frob (ModularGroup.T ^ k) := by
      have := abs_le_Frob_T_zpow k; linarith
    calc ‖(sigmaHom (ModularGroup.T ^ k)) i j‖ = ‖sigmaOfTO k i j‖ := by
          rw [sigmaOfTO_eq]
      _ ≤ 8 * (1 + |(k : ℝ)|) := h
      _ ≤ 96 * (1 + Frob (ModularGroup.T ^ k)) := by nlinarith [h1, abs_nonneg (k : ℝ)]
  · rw [blk_true]
    rw [map_mul, Matrix.mul_apply]
    have h1 : 1 + |(k : ℝ)| ≤ 1 + Frob (ModularGroup.S * ModularGroup.T ^ k) := by
      have := abs_le_Frob_ST_zpow k; linarith
    have hS : ∀ m : Fin 6, ‖(sigmaHom ModularGroup.S) i m‖ ≤ 2 := by
      intro m
      rw [sigmaHom_odd_generators.2]
      exact oddMS_entry_le i m
    have hT : ∀ m : Fin 6, ‖(sigmaHom (ModularGroup.T ^ k)) m j‖ ≤ 8 * (1 + |(k : ℝ)|) := by
      intro m
      rw [← sigmaOfTO_eq k]
      exact sigmaOfTO_entry_le k m j
    calc ‖∑ m : Fin 6, (sigmaHom ModularGroup.S) i m
            * (sigmaHom (ModularGroup.T ^ k)) m j‖
        ≤ ∑ m : Fin 6, ‖(sigmaHom ModularGroup.S) i m‖
            * ‖(sigmaHom (ModularGroup.T ^ k)) m j‖ := by
          refine le_trans (norm_sum_le _ _) ?_
          exact Finset.sum_le_sum (fun m _ => by rw [norm_mul])
      _ ≤ ∑ _m : Fin 6, (2 : ℝ) * (8 * (1 + |(k : ℝ)|)) := by
          refine Finset.sum_le_sum (fun m _ => ?_)
          exact mul_le_mul (hS m) (hT m) (norm_nonneg _) (by norm_num)
      _ = 6 * (2 * (8 * (1 + |(k : ℝ)|))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; norm_num
      _ ≤ 96 * (1 + Frob (ModularGroup.S * ModularGroup.T ^ k)) := by nlinarith [h1]

lemma six_Np_le_O (p : ℤ × Bool) :
    6 * (96 * (1 + Frob (blk p))) ≤ (1 + Frob (blk p)) ^ 12 := by
  have h1 : (1 : ℝ) ≤ Frob (blk p) := one_le_Frob (blk p)
  have ha : (2 : ℝ) ≤ 1 + Frob (blk p) := by linarith
  have hs0 : (0 : ℝ) ≤ 1 + Frob (blk p) := one_add_Frob_nonneg (blk p)
  have h10 : (2048 : ℝ) ≤ (1 + Frob (blk p)) ^ 11 := by
    have h2 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) ha 11
    norm_num at h2
    linarith
  rw [show (12 : ℕ) = 11 + 1 from rfl, pow_add, pow_one]
  nlinarith [h10, hs0]

/-! ## The accumulated bounds along a word -/

noncomputable def SBO (L : List (ℤ × Bool)) : ℝ := (L.map BfO).sum
noncomputable def SKO (L : List (ℤ × Bool)) : ℝ := (L.map KfO).sum

@[simp] lemma SBO_nil : SBO [] = 0 := rfl
@[simp] lemma SBO_cons (p : ℤ × Bool) (L : List (ℤ × Bool)) :
    SBO (p :: L) = BfO p + SBO L := by simp [SBO]
@[simp] lemma SKO_nil : SKO [] = 0 := rfl
@[simp] lemma SKO_cons (p : ℤ × Bool) (L : List (ℤ × Bool)) :
    SKO (p :: L) = KfO p + SKO L := by simp [SKO]

lemma SBO_nonneg (L : List (ℤ × Bool)) : 0 ≤ SBO L := by
  induction L with
  | nil => simp
  | cons p L ih => rw [SBO_cons]; linarith [BfO_nonneg p]

lemma SKO_nonneg (L : List (ℤ × Bool)) : 0 ≤ SKO L := by
  induction L with
  | nil => simp
  | cons p L ih => rw [SKO_cons]; linarith [KfO_nonneg p]

lemma BfO_le_Amp {p : ℤ × Bool} {L : List (ℤ × Bool)} (hp : p ∈ L) :
    BfO p ≤ 10000000 * Amp L ^ 5 := by
  have h1 := BfO_le p
  have h2 := one_add_Frob_blk_le_Amp hp
  have h3 : (0 : ℝ) ≤ 1 + Frob (blk p) := one_add_Frob_nonneg (blk p)
  have h4 : (1 + Frob (blk p)) ^ 5 ≤ Amp L ^ 5 := pow_le_pow_left₀ h3 h2 5
  calc BfO p ≤ 10000000 * (1 + Frob (blk p)) ^ 5 := h1
    _ ≤ 10000000 * Amp L ^ 5 := mul_le_mul_of_nonneg_left h4 (by norm_num)

lemma KfO_le_Amp {p : ℤ × Bool} {L : List (ℤ × Bool)} (hp : p ∈ L) :
    KfO p ≤ 10000 * Amp L ^ 2 := by
  have h1 := KfO_le p
  have h2 := one_add_Frob_blk_le_Amp hp
  have h3 : (0 : ℝ) ≤ 1 + Frob (blk p) := one_add_Frob_nonneg (blk p)
  have h4 : (1 + Frob (blk p)) ^ 2 ≤ Amp L ^ 2 := pow_le_pow_left₀ h3 h2 2
  calc KfO p ≤ 10000 * (1 + Frob (blk p)) ^ 2 := h1
    _ ≤ 10000 * Amp L ^ 2 := mul_le_mul_of_nonneg_left h4 (by norm_num)

/-! ## The carry recursion along the word -/

noncomputable def bCarryO : List (ℤ × Bool) → Fin 6 → R × R × R
  | [], _ => (0, 0, 0)
  | p :: L, i =>
      triAdd (triSum (Finset.univ : Finset (Fin 6))
          (fun j => triSmul ((sigmaHom (blk p)) i j) (bCarryO L j)))
        (triMulOf (carryBlkO p i) ((L.map blk).prod))

@[simp] lemma bCarryO_nil (i : Fin 6) : bCarryO [] i = ((0, 0, 0) : R × R × R) := rfl

@[simp] lemma bCarryO_cons (p : ℤ × Bool) (L : List (ℤ × Bool)) (i : Fin 6) :
    bCarryO (p :: L) i =
      triAdd (triSum (Finset.univ : Finset (Fin 6))
          (fun j => triSmul ((sigmaHom (blk p)) i j) (bCarryO L j)))
        (triMulOf (carryBlkO p i) ((L.map blk).prod)) := rfl

theorem bCarryO_spec (L : List (ℤ × Bool)) (i : Fin 6) :
    carryCombO (bCarryO L i).1 (bCarryO L i).2.1 (bCarryO L i).2.2
      = rowDiffOdd ((L.map blk).prod) i := by
  induction L generalizing i with
  | nil =>
    rw [bCarryO_nil]
    show carryCombO (0 : R) 0 0 = _
    rw [show (([] : List (ℤ × Bool)).map blk).prod = (1 : SL(2,ℤ)) from rfl, rowDiffOdd_one]
    simp [carryCombO]
  | cons p L ih =>
    rw [bCarryO_cons, carryCombO_triAdd, carryCombO_triSum]
    rw [show (∑ j : Fin 6, carryCombO
          (triSmul ((sigmaHom (blk p)) i j) (bCarryO L j)).1
          (triSmul ((sigmaHom (blk p)) i j) (bCarryO L j)).2.1
          (triSmul ((sigmaHom (blk p)) i j) (bCarryO L j)).2.2)
        = ∑ j : Fin 6, (sigmaHom (blk p)) i j
          • carryCombO (bCarryO L j).1 (bCarryO L j).2.1 (bCarryO L j).2.2
      from Finset.sum_congr rfl (fun j _ => carryCombO_triSmul _ _)]
    rw [show (∑ j : Fin 6, (sigmaHom (blk p)) i j
          • carryCombO (bCarryO L j).1 (bCarryO L j).2.1 (bCarryO L j).2.2)
        = ∑ j : Fin 6, (sigmaHom (blk p)) i j
          • rowDiffOdd ((L.map blk).prod) j
      from Finset.sum_congr rfl (fun j _ => by rw [ih j])]
    rw [carryCombO_triMulOf_ofSL, carryBlkO_spec p i]
    rw [show ((p :: L).map blk).prod = blk p * (L.map blk).prod from by
      rw [List.map_cons, List.prod_cons]]
    exact (rowDiffOdd_mul (blk p) ((L.map blk).prod) i).symm

theorem bCarryO_bound (L : List (ℤ × Bool)) (i : Fin 6) :
    CB (bCarryO L i) (Amp L ^ 12 * (1 + SBO L)) (Amp L * (1 + SKO L)) := by
  induction L generalizing i with
  | nil =>
    rw [bCarryO_nil, Amp_nil, SBO_nil, SKO_nil]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [coeffNorm_zero, supportFrobLe_zero]
  | cons p L ih =>
    rw [bCarryO_cons]
    set CbL : ℝ := Amp L ^ 12 * (1 + SBO L) with hCbL
    set KbL : ℝ := Amp L * (1 + SKO L) with hKbL
    have hAmp1 : (1 : ℝ) ≤ Amp L := Amp_one_le L
    have hAmp0 : (0 : ℝ) ≤ Amp L := Amp_nonneg L
    have hSBO0 : (0 : ℝ) ≤ SBO L := SBO_nonneg L
    have hSKO0 : (0 : ℝ) ≤ SKO L := SKO_nonneg L
    have hBf0 : (0 : ℝ) ≤ BfO p := BfO_nonneg p
    have hKf0 : (0 : ℝ) ≤ KfO p := KfO_nonneg p
    have hCbL0 : (0 : ℝ) ≤ CbL := by rw [hCbL]; positivity
    have hKbL0 : (0 : ℝ) ≤ KbL := by rw [hKbL]; positivity
    have hF0 : (0 : ℝ) ≤ Frob (blk p) := Frob_nonneg (blk p)
    have hF1 : (1 : ℝ) ≤ 1 + Frob (blk p) := by linarith
    have hF2 : (2 : ℝ) ≤ 1 + Frob (blk p) := by
      have := one_le_Frob (blk p); linarith
    have hsumb : ∀ j : Fin 6,
        CB (triSmul ((sigmaHom (blk p)) i j) (bCarryO L j))
          (96 * (1 + Frob (blk p)) * CbL) KbL := by
      intro j
      refine CB_mono (CB_triSmul _ (ih j)) ?_ (le_refl _)
      calc ‖(sigmaHom (blk p)) i j‖ * CbL
          ≤ (96 * (1 + Frob (blk p))) * CbL :=
            mul_le_mul_of_nonneg_right (sigma_blkO_entry_le p i j) hCbL0
        _ = 96 * (1 + Frob (blk p)) * CbL := by ring
    have hsum : CB (triSum (Finset.univ : Finset (Fin 6))
        (fun j => triSmul ((sigmaHom (blk p)) i j) (bCarryO L j)))
        (6 * (96 * (1 + Frob (blk p)) * CbL)) KbL := by
      refine CB_triSum (Finset.univ : Finset (Fin 6)) _
        (Cb := 96 * (1 + Frob (blk p)) * CbL) (K := KbL) ?_
      intro j _
      exact hsumb j
    have hsum' : CB (triSum (Finset.univ : Finset (Fin 6))
        (fun j => triSmul ((sigmaHom (blk p)) i j) (bCarryO L j)))
        ((1 + Frob (blk p)) ^ 12 * CbL) KbL := by
      refine CB_mono hsum ?_ (le_refl _)
      calc 6 * (96 * (1 + Frob (blk p)) * CbL)
          = (6 * (96 * (1 + Frob (blk p)))) * CbL := by ring
        _ ≤ ((1 + Frob (blk p)) ^ 12) * CbL :=
            mul_le_mul_of_nonneg_right (six_Np_le_O p) hCbL0
    have htail : CB (triMulOf (carryBlkO p i) ((L.map blk).prod)) (BfO p)
        (KfO p * (2 * Amp L)) := by
      refine CB_mono (CB_triMulOf _ (carryBlkO_bound p i)) (le_refl _) ?_
      have hF := Frob_prod_le L
      calc KfO p * Frob ((L.map blk).prod) ≤ KfO p * (2 * Amp L) :=
            mul_le_mul_of_nonneg_left hF hKf0
        _ = KfO p * (2 * Amp L) := rfl
    have hadd := CB_triAdd hsum' htail
    have hCp : (1 + Frob (blk p)) ^ 12 * CbL + BfO p
        ≤ ((1 + Frob (blk p)) * Amp L) ^ 12 * (1 + (BfO p + SBO L)) := by
      rw [mul_pow, hCbL]
      have ha12 : (1 : ℝ) ≤ (1 + Frob (blk p)) ^ 12 := one_le_pow₀ hF1
      have hb12 : (1 : ℝ) ≤ Amp L ^ 12 := one_le_pow₀ hAmp1
      have hkey : BfO p ≤ (1 + Frob (blk p)) ^ 12 * Amp L ^ 12 * BfO p := by
        have h1 : (1 : ℝ) ≤ (1 + Frob (blk p)) ^ 12 * Amp L ^ 12 := by nlinarith [ha12, hb12]
        calc BfO p = 1 * BfO p := (one_mul _).symm
          _ ≤ ((1 + Frob (blk p)) ^ 12 * Amp L ^ 12) * BfO p :=
              mul_le_mul_of_nonneg_right h1 hBf0
      calc (1 + Frob (blk p)) ^ 12 * (Amp L ^ 12 * (1 + SBO L)) + BfO p
          ≤ (1 + Frob (blk p)) ^ 12 * (Amp L ^ 12 * (1 + SBO L))
            + (1 + Frob (blk p)) ^ 12 * Amp L ^ 12 * BfO p := add_le_add_right hkey _
        _ = (1 + Frob (blk p)) ^ 12 * Amp L ^ 12 * (1 + (BfO p + SBO L)) := by ring
    have hKp : max KbL (KfO p * (2 * Amp L))
        ≤ (1 + Frob (blk p)) * Amp L * (1 + (KfO p + SKO L)) := by
      rw [hKbL]
      refine max_le ?_ ?_
      · have h2 : 1 + SKO L ≤ 1 + (KfO p + SKO L) := by linarith
        calc Amp L * (1 + SKO L) ≤ Amp L * (1 + (KfO p + SKO L)) :=
              mul_le_mul_of_nonneg_left h2 hAmp0
          _ ≤ (1 + Frob (blk p)) * (Amp L * (1 + (KfO p + SKO L))) :=
              le_mul_of_one_le_left (by positivity) hF1
          _ = (1 + Frob (blk p)) * Amp L * (1 + (KfO p + SKO L)) := by ring
      · have h2 : KfO p * 2 ≤ (1 + Frob (blk p)) * (1 + (KfO p + SKO L)) := by
          nlinarith [hF2, hKf0, hSKO0]
        calc KfO p * (2 * Amp L) = (KfO p * 2) * Amp L := by ring
          _ ≤ ((1 + Frob (blk p)) * (1 + (KfO p + SKO L))) * Amp L :=
              mul_le_mul_of_nonneg_right h2 hAmp0
          _ = (1 + Frob (blk p)) * Amp L * (1 + (KfO p + SKO L)) := by ring
    rw [Amp_cons, SBO_cons, SKO_cons]
    exact CB_mono hadd hCp hKp

/-! ## The polynomial bound for `sigmaHom` of a word of blocks -/

lemma sigma_prod_le_O (L : List (ℤ × Bool)) (i j : Fin 6) :
    ‖(sigmaHom ((L.map blk).prod)) i j‖ ≤ Amp L ^ 12 := by
  induction L generalizing i j with
  | nil =>
    rw [List.map_nil, List.prod_nil, map_one, Amp_nil, Matrix.one_apply]
    split <;> norm_num
  | cons p L ih =>
    rw [List.map_cons, List.prod_cons, map_mul, Matrix.mul_apply, Amp_cons, mul_pow]
    have hA0 : (0 : ℝ) ≤ Amp L ^ 12 := by positivity
    calc ‖∑ m : Fin 6, (sigmaHom (blk p)) i m
          * (sigmaHom ((List.map blk L).prod)) m j‖
        ≤ ∑ m : Fin 6, ‖(sigmaHom (blk p)) i m‖
            * ‖(sigmaHom ((List.map blk L).prod)) m j‖ := by
          refine le_trans (norm_sum_le _ _) ?_
          exact Finset.sum_le_sum (fun m _ => by rw [norm_mul])
      _ ≤ ∑ _m : Fin 6, (96 * (1 + Frob (blk p))) * Amp L ^ 12 := by
          refine Finset.sum_le_sum (fun m _ => ?_)
          exact mul_le_mul (sigma_blkO_entry_le p i m) (ih m j) (norm_nonneg _)
            (mul_nonneg (by norm_num) (one_add_Frob_nonneg (blk p)))
      _ = 6 * ((96 * (1 + Frob (blk p))) * Amp L ^ 12) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; norm_num
      _ ≤ (1 + Frob (blk p)) ^ 12 * Amp L ^ 12 := by
          rw [show (6 : ℝ) * ((96 * (1 + Frob (blk p))) * Amp L ^ 12)
              = (6 * (96 * (1 + Frob (blk p)))) * Amp L ^ 12 from by ring]
          exact mul_le_mul_of_nonneg_right (six_Np_le_O p) hA0

/-! ## The four base carries for `δ ∈ {1, -1, S, -S}` -/

lemma MpElem_ofSL (i : Fin 6) : MpElem i = ofSL (Mp i) := rfl

lemma MpElem_coeffNorm (i : Fin 6) : coeffNorm (MpElem i) ≤ 1 := by
  rw [MpElem_ofSL]; exact coeffNorm_of_le (Mp i)

lemma MpElem_supportFrobLe (i : Fin 6) : supportFrobLe (MpElem i) 2 := by
  rw [MpElem_ofSL]
  exact supportFrobLe_mono (supportFrobLe_of_of (Mp i)) (MpFrob_le i)

lemma rowDiffOdd_zero_eq (γ : SL(2,ℤ)) :
    rowDiffOdd γ 0 = ofSL γ - ∑ j : Fin 6, (sigmaHom γ) 0 j • MpElem j := by
  rw [rowDiffOdd, show MpElem (0 : Fin 6) = (1 : R) from MpElem_zero, one_mul]

lemma carryCombO_zero_zero (c : R) : carryCombO 0 0 c = (Rneg + 1) * c := by
  simp [carryCombO]

lemma rowDiffOdd_neg_one (i : Fin 6) : rowDiffOdd (-1 : SL(2,ℤ)) i = MpElem i * (Rneg + 1) := by
  rw [rowDiffOdd, sum_smul_neg_one (fun j => MpElem j) i]
  rw [show ofSL (-1 : SL(2,ℤ)) = Work.Residues.Rneg from rfl]
  rw [sub_neg_eq_add, mul_add, mul_one]

lemma rowDiffOdd_neg_one' (i : Fin 6) :
    rowDiffOdd (-1 : SL(2,ℤ)) i = carryCombO 0 0 (MpElem i) := by
  rw [rowDiffOdd_neg_one i, carryCombO_zero_zero]
  rw [add_mul, one_mul, mul_add, mul_one, Work.Residues.Rneg_comm (MpElem i)]

noncomputable def carryDeltaO (δ : SL(2, ℤ)) (i : Fin 6) : R × R × R :=
  if δ = 1 then (0, 0, 0)
  else if δ = -1 then (0, 0, MpElem i)
  else if δ = ModularGroup.S then atomS i
  else triAdd (triSmul (-1) (atomS i)) (triMulOf (0, 0, MpElem i) ModularGroup.S)

lemma carryDeltaO_one (i : Fin 6) :
    carryDeltaO 1 i = ((0, 0, 0) : R × R × R) := by
  rw [carryDeltaO, if_pos rfl]

lemma carryDeltaO_neg_one (i : Fin 6) :
    carryDeltaO (-1) i = ((0, 0, MpElem i) : R × R × R) := by
  rw [carryDeltaO, if_neg neg_one_ne_one, if_pos rfl]

lemma carryDeltaO_S (i : Fin 6) :
    carryDeltaO ModularGroup.S i = atomS i := by
  rw [carryDeltaO, if_neg S_ne_one, if_neg S_ne_neg_one, if_pos rfl]

lemma carryDeltaO_negS (i : Fin 6) :
    carryDeltaO (-ModularGroup.S) i
      = triAdd (triSmul (-1) (atomS i)) (triMulOf (0, 0, MpElem i) ModularGroup.S) := by
  rw [carryDeltaO, if_neg negS_ne_one, if_neg negS_ne_neg_one, if_neg negS_ne_S]

lemma carryDeltaO_spec (δ : SL(2, ℤ)) (i : Fin 6)
    (h : δ = 1 ∨ δ = -1 ∨ δ = ModularGroup.S ∨ δ = -ModularGroup.S) :
    carryCombO (carryDeltaO δ i).1 (carryDeltaO δ i).2.1 (carryDeltaO δ i).2.2
      = rowDiffOdd δ i := by
  rcases h with rfl | rfl | rfl | rfl
  · rw [carryDeltaO_one]
    show carryCombO (0 : R) 0 0 = rowDiffOdd 1 i
    rw [rowDiffOdd_one]
    simp [carryCombO]
  · rw [carryDeltaO_neg_one]
    show carryCombO (0 : R) 0 (MpElem i) = rowDiffOdd (-1) i
    rw [rowDiffOdd_neg_one']
  · rw [carryDeltaO_S]; exact atomS_spec i
  · rw [carryDeltaO_negS, carryCombO_triAdd, carryCombO_triMulOf_ofSL, carryCombO_triSmul]
    rw [atomS_spec i, carryCombO_zero_zero]
    rw [show (-ModularGroup.S : SL(2,ℤ)) = (-1 : SL(2,ℤ)) * ModularGroup.S from by decide,
      rowDiffOdd_mul, sum_smul_neg_one (fun j => rowDiffOdd ModularGroup.S j) i]
    rw [show (-1 : ℂ) • rowDiffOdd ModularGroup.S i = -rowDiffOdd ModularGroup.S i from by
      rw [neg_smul (1 : ℂ) (rowDiffOdd ModularGroup.S i), one_smul]]
    rw [rowDiffOdd_neg_one i]
    have hR : (Rneg + 1) * MpElem i = MpElem i * (Rneg + 1) := by
      rw [add_mul, one_mul, mul_add, mul_one, Work.Residues.Rneg_comm (MpElem i)]
    rw [hR]

lemma carryDeltaO_bound (δ : SL(2, ℤ)) (i : Fin 6)
    (h : δ = 1 ∨ δ = -1 ∨ δ = ModularGroup.S ∨ δ = -ModularGroup.S) :
    CB (carryDeltaO δ i) 8 200 := by
  rcases h with rfl | rfl | rfl | rfl
  · rw [carryDeltaO_one]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [coeffNorm_zero, supportFrobLe_zero]
  · rw [carryDeltaO_neg_one]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [coeffNorm_zero]
    · simp [coeffNorm_zero]
    · exact le_trans (MpElem_coeffNorm i) (by norm_num)
    · exact supportFrobLe_zero 200
    · exact supportFrobLe_zero 200
    · exact supportFrobLe_mono (MpElem_supportFrobLe i) (by norm_num)
  · rw [carryDeltaO_S]
    exact CB_mono (atomS_bound i) (by norm_num : (3:ℝ) ≤ 8) (by norm_num : (100:ℝ) ≤ 200)
  · rw [carryDeltaO_negS]
    have hM : CB ((0, 0, MpElem i) : R × R × R) 1 2 := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [coeffNorm_zero]
      · simp [coeffNorm_zero]
      · exact MpElem_coeffNorm i
      · exact supportFrobLe_zero 2
      · exact supportFrobLe_zero 2
      · exact MpElem_supportFrobLe i
    have hFrobS : Frob (ModularGroup.S : SL(2,ℤ)) ≤ 2 := by
      rw [Frob_S]
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    have hCa : CB (triSmul (-1) (atomS i)) 3 100 := by
      have h := CB_triSmul (-1) (atomS_bound i)
      have h1 : ‖(-1 : ℂ)‖ * 3 = (3 : ℝ) := by norm_num
      rwa [h1] at h
    have htail : CB (triMulOf (0, 0, MpElem i) ModularGroup.S) 1 4 := by
      have hK : (2 : ℝ) * Frob (ModularGroup.S : SL(2,ℤ)) ≤ 4 := by nlinarith [hFrobS]
      exact CB_mono (CB_triMulOf ModularGroup.S hM) (le_refl 1) hK
    have hcomb := CB_triAdd hCa htail
    exact CB_mono hcomb (by norm_num : (3:ℝ) + 1 ≤ 8) (by norm_num : max (100:ℝ) 4 ≤ 200)

/-! ## The global bound -/

/-- The full carry of the word `L` followed by the base element `δ`. -/
noncomputable def wordCarryFullO (L : List (ℤ × Bool)) (δ : SL(2, ℤ)) (i : Fin 6) :
    R × R × R :=
  triAdd (triSum (Finset.univ : Finset (Fin 6))
      (fun j => triSmul ((sigmaHom ((L.map blk).prod)) i j) (carryDeltaO δ j)))
    (triMulOf (bCarryO L i) δ)

lemma wordCarryFullO_spec (L : List (ℤ × Bool)) (δ : SL(2, ℤ))
    (hδ : δ = 1 ∨ δ = -1 ∨ δ = ModularGroup.S ∨ δ = -ModularGroup.S) (i : Fin 6) :
    carryCombO (wordCarryFullO L δ i).1 (wordCarryFullO L δ i).2.1
        (wordCarryFullO L δ i).2.2
      = rowDiffOdd ((L.map blk).prod * δ) i := by
  unfold wordCarryFullO
  rw [carryCombO_triAdd, carryCombO_triSum, carryCombO_triMulOf_ofSL]
  rw [show (∑ j : Fin 6, carryCombO
        (triSmul ((sigmaHom ((L.map blk).prod)) i j) (carryDeltaO δ j)).1
        (triSmul ((sigmaHom ((L.map blk).prod)) i j) (carryDeltaO δ j)).2.1
        (triSmul ((sigmaHom ((L.map blk).prod)) i j) (carryDeltaO δ j)).2.2)
      = ∑ j : Fin 6, (sigmaHom ((L.map blk).prod)) i j
        • carryCombO (carryDeltaO δ j).1 (carryDeltaO δ j).2.1 (carryDeltaO δ j).2.2
    from Finset.sum_congr rfl (fun j _ => carryCombO_triSmul _ _)]
  rw [show (∑ j : Fin 6, (sigmaHom ((L.map blk).prod)) i j
        • carryCombO (carryDeltaO δ j).1 (carryDeltaO δ j).2.1 (carryDeltaO δ j).2.2)
      = ∑ j : Fin 6, (sigmaHom ((L.map blk).prod)) i j • rowDiffOdd δ j
    from Finset.sum_congr rfl (fun j _ => by rw [carryDeltaO_spec δ j hδ])]
  rw [bCarryO_spec L i]
  exact (rowDiffOdd_mul ((L.map blk).prod) δ i).symm

lemma wordCarryFullO_bound (L : List (ℤ × Bool)) (δ : SL(2, ℤ))
    (hδ : δ = 1 ∨ δ = -1 ∨ δ = ModularGroup.S ∨ δ = -ModularGroup.S) (i : Fin 6) :
    CB (wordCarryFullO L δ i) (48 * Amp L ^ 12 + Amp L ^ 12 * (1 + SBO L))
      (max 200 (Amp L * (1 + SKO L) * Frob δ)) := by
  have hdelta : ∀ j : Fin 6, CB (carryDeltaO δ j) 8 200 :=
    fun j => carryDeltaO_bound δ j hδ
  have hAmp0 : (0 : ℝ) ≤ Amp L ^ 12 := pow_nonneg (Amp_nonneg L) 12
  have hsumb : ∀ j : Fin 6,
      CB (triSmul ((sigmaHom ((L.map blk).prod)) i j) (carryDeltaO δ j))
        (Amp L ^ 12 * 8) 200 := by
    intro j
    refine CB_mono (CB_triSmul _ (hdelta j)) ?_ (le_refl _)
    exact mul_le_mul_of_nonneg_right (sigma_prod_le_O L i j) (by norm_num)
  have hsum : CB (triSum (Finset.univ : Finset (Fin 6))
      (fun j => triSmul ((sigmaHom ((L.map blk).prod)) i j) (carryDeltaO δ j)))
      (48 * Amp L ^ 12) 200 := by
    refine CB_mono (CB_triSum (Finset.univ : Finset (Fin 6)) _
      (Cb := Amp L ^ 12 * 8) (K := 200) (fun j _ => hsumb j)) ?_ (le_refl _)
    rw [Finset.card_univ, Fintype.card_fin]
    exact le_of_eq (by ring)
  have htail : CB (triMulOf (bCarryO L i) δ) (Amp L ^ 12 * (1 + SBO L))
      (Amp L * (1 + SKO L) * Frob δ) := CB_triMulOf δ (bCarryO_bound L i)
  unfold wordCarryFullO
  exact CB_triAdd hsum htail


/-! ## The global odd carry bound -/

set_option maxHeartbeats 8000000 in
theorem carry_bound_odd :
    ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      (∀ i : Fin 6, ∀ j : Fin 6,
        ‖Work.Asymptotics.sigmaHom γ i j‖ ≤ C * (1 + Work.Asymptotics.Frob γ) ^ N) ∧
      ∃ A B Cc : Work.Kernels.R,
        Work.Asymptotics.ofSL γ
            - (∑ j : Fin 6, (Work.Asymptotics.sigmaHom γ) 0 j • Work.Asymptotics.MpElem j)
          = (Work.Kernels.R_T - 1) ^ 2 * A + Work.Kernels.R_S * (Work.Kernels.R_T - 1) ^ 2 * B
              + (Work.Residues.Rneg + 1) * Cc
        ∧ Work.Asymptotics.coeffNorm A ≤ C * (1 + Work.Asymptotics.Frob γ) ^ N
        ∧ Work.Asymptotics.coeffNorm B ≤ C * (1 + Work.Asymptotics.Frob γ) ^ N
        ∧ Work.Asymptotics.supportFrobLe A (C * (1 + Work.Asymptotics.Frob γ) ^ N)
        ∧ Work.Asymptotics.supportFrobLe B (C * (1 + Work.Asymptotics.Frob γ) ^ N) := by
  obtain ⟨C1, N1, hC1pos, hN1, hbf⟩ := block_factorization
  have hC1 : (0 : ℝ) ≤ C1 := le_of_lt hC1pos
  have hC1le : C1 ≤ 1 + C1 := by linarith
  have hA0 : (0 : ℝ) ≤ (1 + C1) ^ 60 := pow_nonneg (by linarith) 60
  refine ⟨10 ^ 40 * (1 + C1) ^ 60, 60 * N1 + 60,
    mul_nonneg (by norm_num) hA0, by linarith, fun γ => ?_⟩
  obtain ⟨n, w, δ, hδ, hw, hprod, hn, hpr⟩ := hbf γ
  set x : ℝ := 1 + Frob γ with hx
  set KK : ℝ := 10 ^ 40 * (1 + C1) ^ 60 with hKK
  set MM : ℝ := 60 * N1 + 60 with hMM
  have hx1 : (1 : ℝ) ≤ x := by rw [hx]; linarith [Frob_nonneg γ]
  have hx0 : (0 : ℝ) ≤ x := le_trans zero_le_one hx1
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx1
  have hMM0 : (0 : ℝ) ≤ MM := by rw [hMM]; linarith
  have hKK1 : (1 : ℝ) ≤ KK := by
    rw [hKK]
    have hq : (1 : ℝ) ≤ (1 + C1) ^ 60 := one_le_pow₀ (by linarith)
    nlinarith [hA0]
  have hKKnn : (0 : ℝ) ≤ KK := le_trans zero_le_one hKK1
  have hKK200 : (200 : ℝ) ≤ KK := by
    rw [hKK]
    have hq : (1 : ℝ) ≤ (1 + C1) ^ 60 := one_le_pow₀ (by linarith)
    calc (200 : ℝ) = 200 * 1 := by ring
      _ ≤ 200 * (1 + C1) ^ 60 := mul_le_mul_of_nonneg_left hq (by norm_num)
      _ ≤ 10 ^ 40 * (1 + C1) ^ 60 := mul_le_mul_of_nonneg_right (by norm_num) hA0
  have hex : ∀ i : Fin n, ∃ q : ℤ × Bool, w i = blk q := by
    intro i
    obtain ⟨k, hk⟩ := hw i
    rcases hk with hk | hk
    · exact ⟨(k, false), by rw [hk, blk_false]⟩
    · exact ⟨(k, true), by rw [hk, blk_true]⟩
  let p : Fin n → ℤ × Bool := fun i => Classical.choose (hex i)
  have hpw : ∀ i, w i = blk (p i) := fun i => Classical.choose_spec (hex i)
  let L : List (ℤ × Bool) := List.ofFn p
  have hAmp : Amp L = ∏ i : Fin n, (1 + Frob (w i)) := by
    rw [Amp_eq]
    change (List.map (fun q => 1 + Frob (blk q)) (List.ofFn p)).prod = _
    rw [List.map_ofFn, List.prod_ofFn]
    exact Finset.prod_congr rfl (fun i _ => by
      simp only [Function.comp_apply]; rw [← hpw i])
  have hAmpLe : Amp L ≤ C1 * x ^ N1 := by
    rw [hAmp, hx]
    exact hpr
  have hLlen : (L.length : ℝ) = (n : ℝ) := by simp [L]
  have hlog : (L.length : ℝ) ≤ C1 * x := by
    have h1 : 1 + Real.log x ≤ x := by
      have := Real.log_le_sub_one_of_pos hxpos; linarith
    have h2 : C1 * (1 + Real.log x) ≤ C1 * x := mul_le_mul_of_nonneg_left h1 hC1
    have h3 : (L.length : ℝ) ≤ C1 * (1 + Real.log x) := by rw [hLlen, hx]; exact hn
    linarith
  have hLprod : (L.map blk).prod = (List.ofFn w).prod := by
    change ((List.ofFn p).map blk).prod = _
    rw [List.map_ofFn]
    rw [show (blk ∘ p) = w from funext (fun i => (hpw i).symm)]
  have hγ : (L.map blk).prod * δ = γ := by rw [hLprod]; exact hprod
  have hAmp0 : (0 : ℝ) ≤ Amp L := Amp_nonneg L
  have hSBO0 : (0 : ℝ) ≤ SBO L := SBO_nonneg L
  have hSKO0 : (0 : ℝ) ≤ SKO L := SKO_nonneg L
  have hSBO : SBO L ≤ C1 * x * (10000000 * Amp L ^ 5) := by
    have h1 : SBO L ≤ (L.length : ℝ) * (10000000 * Amp L ^ 5) := by
      rw [SBO]
      exact sum_map_le_length_mul L (fun q hq => BfO_le_Amp hq)
        (mul_nonneg (by norm_num) (pow_nonneg hAmp0 5))
    have h3 : (0 : ℝ) ≤ 10000000 * Amp L ^ 5 :=
      mul_nonneg (by norm_num) (pow_nonneg hAmp0 5)
    calc SBO L ≤ (L.length : ℝ) * (10000000 * Amp L ^ 5) := h1
      _ ≤ (C1 * x) * (10000000 * Amp L ^ 5) := mul_le_mul_of_nonneg_right hlog h3
  have hSKO : SKO L ≤ C1 * x * (10000 * Amp L ^ 2) := by
    have h1 : SKO L ≤ (L.length : ℝ) * (10000 * Amp L ^ 2) := by
      rw [SKO]
      exact sum_map_le_length_mul L (fun q hq => KfO_le_Amp hq)
        (mul_nonneg (by norm_num) (pow_nonneg hAmp0 2))
    have h3 : (0 : ℝ) ≤ 10000 * Amp L ^ 2 :=
      mul_nonneg (by norm_num) (pow_nonneg hAmp0 2)
    calc SKO L ≤ (L.length : ℝ) * (10000 * Amp L ^ 2) := h1
      _ ≤ (C1 * x) * (10000 * Amp L ^ 2) := mul_le_mul_of_nonneg_right hlog h3
  have hA12 : Amp L ^ 12 ≤ C1 ^ 12 * x ^ (N1 * 12) := by
    have h1 : Amp L ^ 12 ≤ (C1 * x ^ N1) ^ 12 := pow_le_pow_left₀ hAmp0 hAmpLe 12
    rwa [mul_pow, rpow_nat_mul x hx0 N1 12] at h1
  have hA5 : Amp L ^ 5 ≤ C1 ^ 5 * x ^ (N1 * 5) := by
    have h1 : Amp L ^ 5 ≤ (C1 * x ^ N1) ^ 5 := pow_le_pow_left₀ hAmp0 hAmpLe 5
    rwa [mul_pow, rpow_nat_mul x hx0 N1 5] at h1
  have hA3 : Amp L ^ 3 ≤ C1 ^ 3 * x ^ (N1 * 3) := by
    have h1 : Amp L ^ 3 ≤ (C1 * x ^ N1) ^ 3 := pow_le_pow_left₀ hAmp0 hAmpLe 3
    rwa [mul_pow, rpow_nat_mul x hx0 N1 3] at h1
  have hxi : ∀ a b : ℝ, a ≤ b → x ^ a ≤ x ^ b :=
    fun a b hab => Real.rpow_le_rpow_of_exponent_le hx1 hab
  have hxnn : ∀ a : ℝ, (0 : ℝ) ≤ x ^ a := fun a => Real.rpow_nonneg hx0 a
  have hmm1 : x ^ (12 * N1) ≤ x ^ MM := by rw [hMM]; exact hxi _ _ (by linarith)
  have hmm2 : x ^ (17 * N1 + 1) ≤ x ^ MM := by rw [hMM]; exact hxi _ _ (by linarith)
  have hmm3 : x ^ N1 ≤ x ^ MM := by rw [hMM]; exact hxi _ _ (by linarith)
  have hmm4 : x ^ (3 * N1 + 1) ≤ x ^ MM := by rw [hMM]; exact hxi _ _ (by linarith)
  have hxMM1 : (1 : ℝ) ≤ x ^ MM := Real.one_le_rpow hx1 hMM0
  have hδσ : ∀ m : Fin 6, ‖(sigmaHom δ) m 0‖ ≤ 2 := by
    intro m
    rcases hδ with rfl | rfl | rfl | rfl
    · rw [map_one, Matrix.one_apply]; split <;> norm_num
    · rw [sigmaHom_neg_one_apply]; split <;> norm_num
    · rw [sigmaHom_odd_generators.2]; exact oddMS_entry_le m 0
    · rw [show (-ModularGroup.S : SL(2,ℤ)) = (-1 : SL(2,ℤ)) * ModularGroup.S from by decide,
          map_mul, sigmaHom_neg_one, neg_one_mul, Matrix.neg_apply, norm_neg,
          sigmaHom_odd_generators.2]
      exact oddMS_entry_le m 0
  have hsig : ∀ i j : Fin 6, ‖sigmaHom γ i j‖ ≤ KK * x ^ MM := by
    intro i j
    have hδσj : ∀ m : Fin 6, ‖(sigmaHom δ) m j‖ ≤ 2 := by
      intro m
      rcases hδ with rfl | rfl | rfl | rfl
      · rw [map_one, Matrix.one_apply]; split <;> norm_num
      · rw [sigmaHom_neg_one_apply]; split <;> norm_num
      · rw [sigmaHom_odd_generators.2]; exact oddMS_entry_le m j
      · rw [show (-ModularGroup.S : SL(2,ℤ)) = (-1 : SL(2,ℤ)) * ModularGroup.S from by decide,
            map_mul, sigmaHom_neg_one, neg_one_mul, Matrix.neg_apply, norm_neg,
            sigmaHom_odd_generators.2]
        exact oddMS_entry_le m j
    calc ‖sigmaHom γ i j‖ = ‖sigmaHom ((L.map blk).prod * δ) i j‖ := by rw [hγ]
      _ = ‖(sigmaHom ((L.map blk).prod) * sigmaHom δ) i j‖ := by rw [map_mul]
      _ = ‖∑ m : Fin 6, (sigmaHom ((L.map blk).prod)) i m * (sigmaHom δ) m j‖ := by
            rw [Matrix.mul_apply]
      _ ≤ ∑ m : Fin 6, ‖(sigmaHom ((L.map blk).prod)) i m‖
            * ‖(sigmaHom δ) m j‖ := by
            refine le_trans (norm_sum_le _ _) ?_
            exact Finset.sum_le_sum (fun m _ => by rw [norm_mul])
      _ ≤ ∑ _m : Fin 6, Amp L ^ 12 * 2 := by
            refine Finset.sum_le_sum (fun m _ => ?_)
            exact mul_le_mul (sigma_prod_le_O L i m) (hδσj m) (norm_nonneg _)
              (pow_nonneg hAmp0 12)
      _ = 6 * (Amp L ^ 12 * 2) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; norm_num
      _ = 12 * Amp L ^ 12 := by ring
      _ ≤ 12 * (C1 ^ 12 * x ^ (N1 * 12)) := mul_le_mul_of_nonneg_left hA12 (by norm_num)
      _ = 12 * C1 ^ 12 * x ^ (12 * N1) := by
            rw [show N1 * 12 = 12 * N1 from by ring]; ring
      _ ≤ KK * x ^ MM := by
            have h1 : (0 : ℝ) ≤ x ^ (12 * N1) := hxnn _
            have h3 : 12 * C1 ^ 12 ≤ KK := by
              rw [hKK]
              have e1 : C1 ^ 12 ≤ (1 + C1) ^ 60 := pow_C1_le C1 hC1 hC1le 12 (by norm_num)
              nlinarith [e1, hA0]
            calc 12 * C1 ^ 12 * x ^ (12 * N1) ≤ KK * x ^ (12 * N1) :=
                  mul_le_mul_of_nonneg_right h3 h1
              _ ≤ KK * x ^ MM := mul_le_mul_of_nonneg_left hmm1 hKKnn
  have hCb : 48 * Amp L ^ 12 + Amp L ^ 12 * (1 + SBO L) ≤ KK * x ^ MM := by
    have hstep1 : Amp L ^ 12 * SBO L ≤ 10000000 * C1 ^ 18 * x ^ (17 * N1 + 1) := by
      have h4 : Amp L ^ 12 * SBO L
          ≤ (C1 ^ 12 * x ^ (N1 * 12)) * (C1 * x * (10000000 * Amp L ^ 5)) :=
        mul_le_mul hA12 hSBO hSBO0 (mul_nonneg (pow_nonneg hC1 12) (hxnn _))
      have h5 : (C1 ^ 12 * x ^ (N1 * 12)) * (C1 * x * (10000000 * Amp L ^ 5))
          ≤ (C1 ^ 12 * x ^ (N1 * 12))
            * (C1 * x * (10000000 * (C1 ^ 5 * x ^ (N1 * 5)))) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (pow_nonneg hC1 12) (hxnn _))
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hA5 (by norm_num))
          (mul_nonneg hC1 hx0)
      refine le_trans h4 (le_trans h5 ?_)
      have e1 : x ^ (N1 * 12) * (x * x ^ (N1 * 5)) = x ^ (17 * N1 + 1) := by
        rw [show x * x ^ (N1 * 5) = x ^ (1 : ℝ) * x ^ (N1 * 5) from by rw [Real.rpow_one]]
        rw [← Real.rpow_add hxpos, ← Real.rpow_add hxpos]
        congr 1
        ring
      have hrw : (C1 ^ 12 * x ^ (N1 * 12)) * (C1 * x * (10000000 * (C1 ^ 5 * x ^ (N1 * 5))))
          = 10000000 * C1 ^ 18 * x ^ (17 * N1 + 1) := by
        rw [show (C1 ^ 12 * x ^ (N1 * 12))
              * (C1 * x * (10000000 * (C1 ^ 5 * x ^ (N1 * 5))))
            = 10000000 * C1 ^ 18 * (x ^ (N1 * 12) * (x * x ^ (N1 * 5))) from by ring]
        rw [e1]
      rw [hrw]
    have h49 : 49 * Amp L ^ 12 ≤ 49 * C1 ^ 12 * x ^ (12 * N1) := by
      calc 49 * Amp L ^ 12 ≤ 49 * (C1 ^ 12 * x ^ (N1 * 12)) :=
            mul_le_mul_of_nonneg_left hA12 (by norm_num)
        _ = 49 * C1 ^ 12 * x ^ (12 * N1) := by
            rw [show N1 * 12 = 12 * N1 from by ring]; ring
    have hsum1 : 48 * Amp L ^ 12 + Amp L ^ 12 * (1 + SBO L)
        ≤ 49 * C1 ^ 12 * x ^ (12 * N1) + 10000000 * C1 ^ 18 * x ^ (17 * N1 + 1) := by
      have he : 48 * Amp L ^ 12 + Amp L ^ 12 * (1 + SBO L)
          = 49 * Amp L ^ 12 + Amp L ^ 12 * SBO L := by ring
      rw [he]
      linarith [h49, hstep1]
    have hcon : 49 * C1 ^ 12 + 10000000 * C1 ^ 18 ≤ KK := by
      rw [hKK]
      have e1 : 49 * C1 ^ 12 ≤ 49 * (1 + C1) ^ 60 :=
        mul_le_mul_of_nonneg_left (pow_C1_le C1 hC1 hC1le 12 (by norm_num)) (by norm_num)
      have e2 : 10000000 * C1 ^ 18 ≤ 10000000 * (1 + C1) ^ 60 :=
        mul_le_mul_of_nonneg_left (pow_C1_le C1 hC1 hC1le 18 (by norm_num)) (by norm_num)
      nlinarith [e1, e2, hA0]
    calc 48 * Amp L ^ 12 + Amp L ^ 12 * (1 + SBO L)
        ≤ 49 * C1 ^ 12 * x ^ (12 * N1) + 10000000 * C1 ^ 18 * x ^ (17 * N1 + 1) := hsum1
      _ ≤ 49 * C1 ^ 12 * x ^ MM + 10000000 * C1 ^ 18 * x ^ MM :=
          add_le_add (mul_le_mul_of_nonneg_left hmm1 (by positivity))
            (mul_le_mul_of_nonneg_left hmm2 (by positivity))
      _ = (49 * C1 ^ 12 + 10000000 * C1 ^ 18) * x ^ MM := by ring
      _ ≤ KK * x ^ MM := mul_le_mul_of_nonneg_right hcon (hxnn _)
  have hK : max 200 (Amp L * (1 + SKO L) * Frob δ) ≤ KK * x ^ MM := by
    have hFδ : Frob δ ≤ 2 := Frob_base_le δ hδ
    refine max_le ?_ ?_
    · calc (200 : ℝ) = 200 * 1 := by ring
        _ ≤ 200 * x ^ MM := mul_le_mul_of_nonneg_left hxMM1 (by norm_num)
        _ ≤ KK * x ^ MM := mul_le_mul_of_nonneg_right hKK200 (hxnn MM)
    · have h1 : Amp L * (1 + SKO L) * Frob δ ≤ Amp L * (1 + SKO L) * 2 :=
        mul_le_mul_of_nonneg_left hFδ (mul_nonneg hAmp0 (by linarith [hSKO0]))
      have h2 : Amp L * (1 + SKO L) * 2 ≤ 2 * Amp L + 20000 * C1 * x * Amp L ^ 3 := by
        have h3 : Amp L * (1 + SKO L) * 2 = 2 * Amp L + 2 * (Amp L * SKO L) := by ring
        rw [h3]
        have h4 : Amp L * SKO L ≤ Amp L * (C1 * x * (10000 * Amp L ^ 2)) :=
          mul_le_mul_of_nonneg_left hSKO hAmp0
        nlinarith [h4, hAmp0, hx0, hC1]
      have h5 : 2 * Amp L ≤ 2 * (C1 * x ^ N1) := mul_le_mul_of_nonneg_left hAmpLe (by norm_num)
      have h7 : 20000 * C1 * x * Amp L ^ 3 ≤ 20000 * C1 ^ 4 * x ^ (3 * N1 + 1) := by
        have h8 : 20000 * C1 * x * Amp L ^ 3 ≤ 20000 * C1 * x * (C1 ^ 3 * x ^ (N1 * 3)) :=
          mul_le_mul_of_nonneg_left hA3 (mul3_nonneg (by norm_num) hC1 hx0)
        refine le_trans h8 (le_of_eq ?_)
        have e1 : x * x ^ (N1 * 3) = x ^ (3 * N1 + 1) := by
          rw [show x * x ^ (N1 * 3) = x ^ (1 : ℝ) * x ^ (N1 * 3) from by rw [Real.rpow_one]]
          rw [← Real.rpow_add hxpos]
          congr 1
          ring
        rw [show 20000 * C1 * x * (C1 ^ 3 * x ^ (N1 * 3))
            = 20000 * C1 ^ 4 * (x * x ^ (N1 * 3)) from by ring]
        rw [e1]
      have h9 : 2 * (C1 * x ^ N1) ≤ 2 * C1 * x ^ MM := by
        have h10 : x ^ N1 ≤ x ^ MM := hmm3
        have h11 : (0 : ℝ) ≤ x ^ N1 := hxnn _
        have h12 : (0 : ℝ) ≤ x ^ MM := hxnn _
        nlinarith [h10, hC1, h11, h12]
      have h10 : 20000 * C1 ^ 4 * x ^ (3 * N1 + 1) ≤ 20000 * C1 ^ 4 * x ^ MM :=
        mul_le_mul_of_nonneg_left hmm4 (by positivity)
      have h12 : 2 * C1 + 20000 * C1 ^ 4 ≤ KK := by
        rw [hKK]
        have e1 : 2 * C1 ≤ 2 * (1 + C1) ^ 60 :=
          mul_le_mul_of_nonneg_left (C1_le_pow60 C1 hC1 hC1le) (by norm_num)
        have e2 : 20000 * C1 ^ 4 ≤ 20000 * (1 + C1) ^ 60 :=
          mul_le_mul_of_nonneg_left (pow_C1_le C1 hC1 hC1le 4 (by norm_num)) (by norm_num)
        nlinarith [e1, e2, hA0]
      calc Amp L * (1 + SKO L) * Frob δ ≤ Amp L * (1 + SKO L) * 2 := h1
        _ ≤ 2 * Amp L + 20000 * C1 * x * Amp L ^ 3 := h2
        _ ≤ 2 * (C1 * x ^ N1) + 20000 * C1 ^ 4 * x ^ (3 * N1 + 1) := add_le_add h5 h7
        _ ≤ 2 * C1 * x ^ MM + 20000 * C1 ^ 4 * x ^ MM := add_le_add h9 h10
        _ = (2 * C1 + 20000 * C1 ^ 4) * x ^ MM := by ring
        _ ≤ KK * x ^ MM := mul_le_mul_of_nonneg_right h12 (hxnn _)
  refine ⟨hsig, (wordCarryFullO L δ 0).1, (wordCarryFullO L δ 0).2.1,
    (wordCarryFullO L δ 0).2.2, ?_, ?_, ?_, ?_, ?_⟩
  · change ofSL γ - (∑ j : Fin 6, (sigmaHom γ) 0 j • MpElem j)
      = carryCombO (wordCarryFullO L δ 0).1 (wordCarryFullO L δ 0).2.1
          (wordCarryFullO L δ 0).2.2
    rw [wordCarryFullO_spec L δ hδ 0, hγ, rowDiffOdd_zero_eq]
  · exact le_trans (wordCarryFullO_bound L δ hδ 0).1 hCb
  · exact le_trans (wordCarryFullO_bound L δ hδ 0).2.1 hCb
  · exact supportFrobLe_mono (wordCarryFullO_bound L δ hδ 0).2.2.2.1 hK
  · exact supportFrobLe_mono (wordCarryFullO_bound L δ hδ 0).2.2.2.2.1 hK

end Work.Asymptotics

end
