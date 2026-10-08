import Mathlib

namespace Work.L2F.Props.oddsub

/-- Newton's identity for `2 × 2` matrices: `tr(M²) = (tr M)² - 2 det M`.
Proof: expand everything into the four entries via `Matrix.trace_fin_two`,
`Matrix.det_fin_two`, `Matrix.mul_apply`, `Fin.sum_univ_two`, then `ring`. -/
private lemma trace_mul_self_fin_two (F : Type*) [Field F] (M : Matrix (Fin 2) (Fin 2) F) :
    (M * M).trace = M.trace ^ 2 - 2 * M.det := by
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- A `2 × 2` matrix over a field with `N * N = 0` is nilpotent, hence traceless and
singular: `N.trace = 0 ∧ N.det = 0`.

* `N.det = 0` because `det N * det N = det (N * N) = 0` and a field has no zero divisors.
* `N.trace = 0` because Newton's identity `tr(N²) = (tr N)² - 2 det N` combined with
  `N * N = 0` and `N.det = 0` gives `(tr N)² = 0`. -/
theorem trace_det_eq_zero_of_mul_self_eq_zero (F : Type*) [Field F]
    (N : Matrix (Fin 2) (Fin 2) F) (hN : N * N = 0) : N.trace = 0 ∧ N.det = 0 := by
  -- Determinant: `det N * det N = det (N * N) = det 0 = 0`.
  have hdet : N.det = 0 := by
    have h : N.det * N.det = 0 := by
      simpa [Matrix.det_mul] using congrArg Matrix.det hN
    exact mul_self_eq_zero.mp h
  -- Trace: Newton's identity gives `(tr N)² = tr(N²) + 2 det N = 0`.
  have htrace : N.trace = 0 := by
    have h := trace_mul_self_fin_two F N
    rw [hN] at h
    simp only [Matrix.trace_zero, hdet, mul_zero, sub_zero] at h
    rw [pow_two] at h
    exact mul_self_eq_zero.mp h.symm
  exact ⟨htrace, hdet⟩

end Work.L2F.Props.oddsub
