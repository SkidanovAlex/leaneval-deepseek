import Mathlib
import Submission.Work.TMC7Core.Rat
import Submission.Work.TMC7Core.Solutions.max_norm_roots_eq_rhoSL
import Submission.Work.TMC14Core.hyps_reduce

namespace Work.TMComp.LocCantor

open Matrix

/-- Cayley--Hamilton for a `2 × 2` matrix of determinant `1`:
`A² − (tr A) • A + 1 = 0`. -/
lemma sl2_cayley_hamilton (A : Matrix (Fin 2) (Fin 2) ℝ) (hdet : A.det = 1) :
    A * A - A.trace • A + 1 = 0 := by
  have hd : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    rwa [Matrix.det_fin_two] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, Matrix.smul_apply,
      Matrix.trace_fin_two, Fin.sum_univ_two] <;>
    nlinarith [hd]

/-- The trace sequence `m ↦ tr(A^m)` of a `2 × 2` matrix of determinant `1` satisfies the
two-term recurrence `tr(A^{m+2}) = (tr A) · tr(A^{m+1}) − tr(A^m)`. -/
lemma trace_pow_recurrence (A : Matrix (Fin 2) (Fin 2) ℝ) (hdet : A.det = 1) (n : ℕ) :
    (A ^ (n + 2)).trace = A.trace * (A ^ (n + 1)).trace - (A ^ n).trace := by
  have hCH := sl2_cayley_hamilton A hdet
  have key : A ^ n * (A * A - A.trace • A + 1) = 0 := by rw [hCH, mul_zero]
  have expand : A ^ n * (A * A - A.trace • A + 1)
      = A ^ (n + 2) - A.trace • A ^ (n + 1) + A ^ n := by
    rw [mul_add, mul_sub, mul_one, mul_smul_comm]
    rw [show A ^ n * (A * A) = A ^ (n + 2) by rw [← pow_two, ← pow_add]]
    rw [show A ^ n * A = A ^ (n + 1) by rw [pow_succ]]
  have hmat : A ^ (n + 2) - A.trace • A ^ (n + 1) + A ^ n = 0 := by rw [← expand, key]
  have hT := congrArg Matrix.trace hmat
  rw [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_zero] at hT
  simp only [smul_eq_mul] at hT
  linarith

/-- If `lam + mu = τ` and `lam * mu = 1` in `ℂ`, the sequence `m ↦ lam^m + mu^m` satisfies
the same two-term recurrence as the trace sequence. -/
lemma pow_sum_recurrence (τ lam mu : ℂ) (hsum : lam + mu = τ) (hprod : lam * mu = 1)
    (n : ℕ) :
    τ * (lam ^ (n + 1) + mu ^ (n + 1)) - (lam ^ n + mu ^ n) = lam ^ (n + 2) + mu ^ (n + 2) := by
  have h1 : lam ^ 2 - τ * lam + 1 = 0 := by rw [← hsum]; linear_combination -hprod
  have h2 : mu ^ 2 - τ * mu + 1 = 0 := by rw [← hsum]; linear_combination -hprod
  have key2 : τ * (lam ^ (n + 1) + mu ^ (n + 1)) - (lam ^ n + mu ^ n)
      - (lam ^ (n + 2) + mu ^ (n + 2))
      = -(lam ^ n * (lam ^ 2 - τ * lam + 1) + mu ^ n * (mu ^ 2 - τ * mu + 1)) := by ring
  rw [← sub_eq_zero, key2, h1, h2]; ring

/-- The eigenvalues of a `2 × 2` matrix of determinant `1` in complex form: for `A ∈ SL(2,ℝ)`
with trace `τ`, there are `lam, mu : ℂ` with `lam + mu = τ` and `lam * mu = 1` whose powers
express the traces of all powers of `A`. -/
theorem trace_pow_abs_le_rhoSL (A : Matrix (Fin 2) (Fin 2) ℝ) (hdet : A.det = 1) (m : ℕ) :
    |(A ^ m).trace| ≤ 2 * Work.TMC7Core.rhoSL A.trace ^ m := by
  -- roots `lam, mu` of `X ^ 2 - τ X + 1`
  obtain ⟨w, hw⟩ :=
    (isSquare_iff_exists_sq ((A.trace : ℂ) ^ 2 - 4)).mp (Complex.isSquare _)
  set lam : ℂ := ((A.trace : ℂ) + w) / 2 with hlam
  set mu : ℂ := ((A.trace : ℂ) - w) / 2 with hmu
  have hsum : lam + mu = (A.trace : ℂ) := by rw [hlam, hmu]; ring
  have hprod : lam * mu = 1 := by
    rw [hlam, hmu]
    have hkey : (((A.trace : ℂ) + w) / 2) * (((A.trace : ℂ) - w) / 2)
        = ((A.trace : ℂ) ^ 2 - w ^ 2) / 4 := by ring
    rw [hkey, ← hw]
    ring
  -- the trace of `A^m` is `lam^m + mu^m`
  have htrace : ∀ n : ℕ, ((A ^ n).trace : ℂ) = lam ^ n + mu ^ n :=
    Nat.twoStepInduction
      (by
        show ((A ^ 0).trace : ℂ) = lam ^ 0 + mu ^ 0
        simp [Matrix.trace_one]
        norm_num)
      (by simpa using hsum.symm)
      (by
        intro k hk hk1
        have hcast : ((A ^ (k + 2)).trace : ℂ)
            = (A.trace : ℂ) * ((A ^ (k + 1)).trace : ℂ) - ((A ^ k).trace : ℂ) := by
          rw [trace_pow_recurrence A hdet k]; push_cast; ring
        rw [hcast, hk, hk1]
        exact pow_sum_recurrence (A.trace : ℂ) lam mu hsum hprod k)
  have hnorm : |(A ^ m).trace| = ‖lam ^ m + mu ^ m‖ := by
    rw [← htrace m]
    simp
  rw [hnorm]
  calc ‖lam ^ m + mu ^ m‖ ≤ ‖lam ^ m‖ + ‖mu ^ m‖ := norm_add_le _ _
    _ = ‖lam‖ ^ m + ‖mu‖ ^ m := by rw [norm_pow, norm_pow]
    _ ≤ 2 * (max ‖lam‖ ‖mu‖) ^ m := by
        have hle1 : ‖lam‖ ^ m ≤ (max ‖lam‖ ‖mu‖) ^ m :=
          pow_le_pow_left₀ (norm_nonneg _) (le_max_left _ _) m
        have hle2 : ‖mu‖ ^ m ≤ (max ‖lam‖ ‖mu‖) ^ m :=
          pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) m
        linarith
    _ = 2 * Work.TMC7Core.rhoSL A.trace ^ m := by
        rw [Work.TMC7Core.Solutions.max_norm_roots_eq_rhoSL A.trace hsum hprod]

end Work.TMComp.LocCantor
