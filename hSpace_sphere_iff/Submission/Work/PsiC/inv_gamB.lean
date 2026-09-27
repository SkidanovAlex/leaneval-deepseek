import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.PsiC.BFrame
import Submission.Work.PsiC.gamB_decomp
import Submission.Work.PsiC.invB_gamB_perm
import Submission.Work.PsiC.gamB_pow_sum_reflect

/-!
# `Work.PsiC.inv_gamB`

The six-cycle `gamB n` of the frame-B computation is inverted by the involution `invB n`
(`Work.PsiC.invB_gamB_perm`).  Consequently conjugating the `μ`-spectral projector
`cycProj6 n μ = (1/6) Σ_{k<6} (μ⁻¹)^k γ^k` of `gamB` by the permutation matrix of `invB` swaps
the eigenvalue `μ` for `μ⁻¹`: `invB · cycProj6 μ · invB = cycProj6 (μ⁻¹)`.

Hence the associated `K₀`-classes of `P · cycProj6 μ` and `P · cycProj6 (μ⁻¹)` agree whenever
`P` commutes with `invB`'s permutation matrix — the two projectors are conjugate, and `K₀` is
invariant under conjugation (here by an involutive permutation, `Work.KT.PsiC.clsM_conj`).
-/

open Matrix

namespace Work.PsiC

set_option linter.unusedVariables false

/-- The matrix-level core: the involution `invB n` conjugates the six-cycle projector
`cycProj6 n μ` of `gamB` into the projector `cycProj6 n μ⁻¹` of the inverse cycle. -/
theorem invB_conj_cycProj6 (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (mu : ℂ)
    (hmu : mu ^ 6 = 1) :
    (Work.KT.PsiC.invB n).permMatrix A * Work.KT.PsiC.cycProj6 (A := A) n mu
        * (Work.KT.PsiC.invB n).permMatrix A
      = Work.KT.PsiC.cycProj6 (A := A) n mu⁻¹ := by
  obtain ⟨hperm, hperm2⟩ := Work.PsiC.invB_gamB_perm n
  have hI2 : (Work.KT.PsiC.invB n).permMatrix A * (Work.KT.PsiC.invB n).permMatrix A = 1 := by
    rw [← Matrix.permMatrix_mul, hperm2, Matrix.permMatrix_one]
  -- the conjugation sends `gamB` to its fifth power (= its inverse)
  have hIGI : (Work.KT.PsiC.invB n).permMatrix A * (Work.KT.PsiC.gamB n).permMatrix A
      * (Work.KT.PsiC.invB n).permMatrix A = ((Work.KT.PsiC.gamB n).permMatrix A) ^ 5 := by
    have h5 : (Work.KT.PsiC.gamB n) ^ 5 = (Work.KT.PsiC.gamB n)⁻¹ := by
      refine eq_inv_of_mul_eq_one_right ?_
      rw [← pow_succ']
      exact Work.PsiC.GamBDecomp.gamB_pow_six n
    rw [← Matrix.permMatrix_mul (σ := Work.KT.PsiC.gamB n) (τ := Work.KT.PsiC.invB n),
        ← Matrix.permMatrix_mul (σ := Work.KT.PsiC.invB n)
          (τ := Work.KT.PsiC.gamB n * Work.KT.PsiC.invB n),
        ← mul_assoc, hperm, Work.KT.PsiC.permMatrix_pow, h5]
  -- and therefore on every power
  have hpow : ∀ k : ℕ, (Work.KT.PsiC.invB n).permMatrix A
        * ((Work.KT.PsiC.gamB n).permMatrix A) ^ k * (Work.KT.PsiC.invB n).permMatrix A
      = (((Work.KT.PsiC.gamB n).permMatrix A) ^ 5) ^ k := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_zero, mul_one]; exact hI2
    | succ k ih =>
        rw [pow_succ, pow_succ, Work.KT.PsiC.conj_mul' _ _ _ hI2, ih, hIGI]
  have hq6 : (mu⁻¹) ^ 6 = 1 := by rw [inv_pow, hmu, inv_one]
  -- unfold both projectors into plain geometric sums
  have hcyc : Work.KT.PsiC.cycProj6 (A := A) n mu
      = ((1 : ℂ) / 6) • (∑ k ∈ Finset.range 6,
          (mu⁻¹) ^ k • ((Work.KT.PsiC.gamB n).permMatrix A) ^ k) := by
    simp only [Work.KT.PsiC.cycProj6, Work.KT.PsiC.smulA_eq_smulC]
  have hcyci : Work.KT.PsiC.cycProj6 (A := A) n mu⁻¹
      = ((1 : ℂ) / 6) • (∑ k ∈ Finset.range 6,
          ((mu⁻¹)⁻¹) ^ k • ((Work.KT.PsiC.gamB n).permMatrix A) ^ k) := by
    simp only [Work.KT.PsiC.cycProj6, Work.KT.PsiC.smulA_eq_smulC]
  rw [hcyc, hcyci, mul_smul_comm, smul_mul_assoc]
  congr 1
  -- push the conjugation through the sum
  rw [Matrix.mul_sum, Matrix.sum_mul]
  have hLs : (∑ k ∈ Finset.range 6, (Work.KT.PsiC.invB n).permMatrix A
        * ((mu⁻¹) ^ k • ((Work.KT.PsiC.gamB n).permMatrix A) ^ k)
        * (Work.KT.PsiC.invB n).permMatrix A)
      = ∑ k ∈ Finset.range 6, (mu⁻¹) ^ k • (((Work.KT.PsiC.gamB n).permMatrix A) ^ 5) ^ k := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [mul_smul_comm, smul_mul_assoc, hpow k]
  rw [hLs, Work.PsiC.gamB_pow_sum_reflect A n (mu⁻¹) hq6]

theorem inv_gamB (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (P : Matrix (Work.KT.PsiC.IB n) (Work.KT.PsiC.IB n) A)
    (hP : P * P = P) (hPi : P * (Work.KT.PsiC.invB n).permMatrix A = (Work.KT.PsiC.invB n).permMatrix A * P)
    (mu : ℂ) (hmu : mu ^ 6 = 1) :
    Work.KT.Psi.clsM (Work.KT.PsiC.IB n) (P * Work.KT.PsiC.cycProj6 (A := A) n mu) =
      Work.KT.Psi.clsM (Work.KT.PsiC.IB n) (P * Work.KT.PsiC.cycProj6 (A := A) n mu⁻¹) := by
  obtain ⟨hperm, hperm2⟩ := Work.PsiC.invB_gamB_perm n
  have hI2 : (Work.KT.PsiC.invB n).permMatrix A * (Work.KT.PsiC.invB n).permMatrix A = 1 := by
    rw [← Matrix.permMatrix_mul, hperm2, Matrix.permMatrix_one]
  have hcrux : (Work.KT.PsiC.invB n).permMatrix A * Work.KT.PsiC.cycProj6 (A := A) n mu
        * (Work.KT.PsiC.invB n).permMatrix A
      = Work.KT.PsiC.cycProj6 (A := A) n mu⁻¹ := invB_conj_cycProj6 A n mu hmu
  -- `P` commutes with `invB`'s permutation matrix
  have hIPI : (Work.KT.PsiC.invB n).permMatrix A * P * (Work.KT.PsiC.invB n).permMatrix A = P := by
    rw [mul_assoc, hPi, ← mul_assoc, hI2, one_mul]
  have hconj : (Work.KT.PsiC.invB n).permMatrix A
        * (P * Work.KT.PsiC.cycProj6 (A := A) n mu) * (Work.KT.PsiC.invB n).permMatrix A
      = P * Work.KT.PsiC.cycProj6 (A := A) n mu⁻¹ := by
    rw [Work.KT.PsiC.conj_mul' _ _ _ hI2, hIPI, hcrux]
  rw [← Work.KT.PsiC.clsM_conj (A := A) (ι := Work.KT.PsiC.IB n)
      (P := P * Work.KT.PsiC.cycProj6 (A := A) n mu)
      (u := (Work.KT.PsiC.invB n).permMatrix A) (v := (Work.KT.PsiC.invB n).permMatrix A) hI2 hI2,
    hconj]

end Work.PsiC
