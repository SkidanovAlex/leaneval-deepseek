import Mathlib
import Submission.Work.L2F.Props.CentralizerTorusDefs
import Submission.Work.L2F.Semisimple.primeOrderCentralizer
import Submission.Work.L2F.Props.pow_smul_one_add_sq_zero

namespace Work.L2F.Props

/-- If `g : GL(2,F)` (char ≠ 2) has `g ^ m = μ • 1` for some `μ` with `(m : F) ≠ 0`, and its
traceless part `glW F g` is not a scalar matrix, then the discriminant `glD F g` of `g` is
nonzero.  Equivalently: when `glD F g = 0` the traceless part is nilpotent of square zero,
`g = λ + N` with `N² = 0` and `λ = tr g / 2 ≠ 0`, so `g ^ m = λ^m + m λ^{m-1} N`; a scalar
`m`-th power then forces `N` (hence `glW F g`) to be a scalar. -/
theorem glD_ne_zero (F : Type*) [Field F] (h2 : (2 : F) ≠ 0) (g : GL (Fin 2) F) (m : ℕ)
    (hmF : (m : F) ≠ 0)
    (hgpow : ∃ μ : F, ((g : Matrix (Fin 2) (Fin 2) F)) ^ m = μ • (1 : Matrix (Fin 2) (Fin 2) F))
    (hns : ∀ c : F, glW F g ≠ c • (1 : Matrix (Fin 2) (Fin 2) F)) :
    glD F g ≠ 0 := by
  intro hD
  obtain ⟨μ, hμ⟩ := hgpow
  -- The matrix, its half-trace, and the traceless part.
  let A : Matrix (Fin 2) (Fin 2) F := (g : Matrix (Fin 2) (Fin 2) F)
  let lam : F := A.trace / 2
  let W : Matrix (Fin 2) (Fin 2) F := glW F g
  -- `A = λ • 1 + W`.
  have hA : A = lam • 1 + W := glW_add F g
  -- Under `glD F g = 0` the traceless part satisfies `W * W = 0`.
  have hWW : W * W = 0 := by
    have h := glW_mul_self F h2 g
    rw [hD, zero_smul] at h
    exact h
  -- `A` is invertible, hence `det A ≠ 0`.
  have hdet : A.det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero g
  -- `glD F g = λ ^ 2 - det A`, so `λ ^ 2 = det A`.
  have hlam2 : lam ^ 2 = A.det := by
    have h := hD
    rw [glD_apply] at h
    exact sub_eq_zero.mp h
  -- Hence `λ ≠ 0`.
  have hlam : lam ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hlam2
    exact hdet hlam2.symm
  -- `m ≠ 0` as a natural number.
  have hm0 : m ≠ 0 := by rintro rfl; exact hmF Nat.cast_zero
  -- Nilpotent-case binomial collapse: `A ^ m = λ ^ m • 1 + (m λ^{m-1}) • W`.
  have hpow : A ^ m = lam ^ m • 1 + ((m : F) * lam ^ (m - 1)) • W := by
    have hbin := pow_smul_one_add_sq_zero F lam W hWW m hm0
    rw [← hA] at hbin
    exact hbin
  -- Combining with `A ^ m = μ • 1`.
  have h1 : ((m : F) * lam ^ (m - 1)) • W = (μ - lam ^ m) • 1 := by
    have h := hpow.symm.trans hμ
    rw [add_comm] at h
    rw [sub_smul]
    exact (eq_sub_iff_add_eq).mpr h
  -- The scalar `(m : F) * λ ^ (m-1)` is nonzero, so `W` is a scalar matrix.
  have hd : (m : F) * lam ^ (m - 1) ≠ 0 := mul_ne_zero hmF (pow_ne_zero (m - 1) hlam)
  have hWscal : W = ((((m : F) * lam ^ (m - 1))⁻¹) * (μ - lam ^ m)) • 1 := by
    have hc := congrArg (fun M => ((m : F) * lam ^ (m - 1))⁻¹ • M) h1
    simp only [smul_smul] at hc
    rw [inv_mul_cancel₀ hd, one_smul] at hc
    exact hc
  exact hns ((((m : F) * lam ^ (m - 1))⁻¹) * (μ - lam ^ m)) hWscal

end Work.L2F.Props
