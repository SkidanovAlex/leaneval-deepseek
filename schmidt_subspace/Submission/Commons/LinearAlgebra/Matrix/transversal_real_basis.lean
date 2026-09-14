import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Commons.Algebra.Matrix.det_eq_sum_of_rows

open _root_.Matrix

namespace Commons.LinearAlgebra.Matrix

/-- **Transversal real basis (Schmidt).**

Given an invertible complex `N × N` matrix `L`, one can select, independently for every row,
either the real part or the imaginary part of that row so that the resulting *real* `N × N`
matrix is again invertible.

The proof expands the complex determinant along the "real / imaginary" splitting of each row.
Writing `rowR k` for the real-part row and `rowI k` for the imaginary-part row, we have
`row k = rowR k + I · rowI k` in `ℂ^N`. Multilinearity of the determinant in the rows
(`Commons.Algebra.Matrix.det_eq_sum_of_rows`) gives

  `det L = ∑_{s : Fin N → Fin 2} (∏ k, c k (s k)) * det (rows chosen by s)`,

where `c k 0 = 1`, `c k 1 = I`. Each factor `det (rows chosen by s)` is the complex
determinant of a matrix with real entries, i.e. the cast of the real determinant of the
transversal obtained from `s`. If all of those real determinants vanished, the whole sum
would vanish and hence `det L = 0`, contradicting invertibility. So some choice `s` yields a
nonzero real determinant. -/
theorem transversal_real_basis {N : ℕ} (L : Fin N → Fin N → ℂ)
    (hdet : (Matrix.of L).det ≠ 0) :
    ∃ s : Fin N → Fin 2,
      (Matrix.of (fun i k => if s i = 0 then (L i k).re else (L i k).im)).det ≠ 0 := by
  classical
  -- The real-part row vector and the imaginary-part row vector, as complex vectors.
  let row : (k : Fin N) → Fin 2 → (Fin N → ℂ) := fun k i =>
    fun j => if i = 0 then ((L k j).re : ℂ) else ((L k j).im : ℂ)
  -- The coefficients attached to the real and imaginary parts.
  let coef : (k : Fin N) → Fin 2 → ℂ := fun k i => if i = 0 then 1 else Complex.I
  -- Each complex row is the corresponding linear combination of the two real vectors.
  have hA : ∀ k, (Matrix.of L) k = ∑ i : Fin 2, coef k i • row k i := by
    intro k
    funext j
    rw [Matrix.of_apply, Fin.sum_univ_two]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, row, coef, Fin.isValue, Fin.reduceEq,
      if_true, if_false, one_mul]
    rw [mul_comm, Complex.re_add_im]
  -- Multilinear expansion of the determinant in the rows.
  have hmain :=
    Commons.Algebra.Matrix.det_eq_sum_of_rows (A := Matrix.of L) (row := row) (c := coef) hA
  -- Each summand is the cast of a real determinant, namely that of the transversal `f`.
  have key : ∀ f : Fin N → Fin 2,
      (Matrix.of (fun k => row k (f k))).det
        = ((Matrix.of (fun i k => if f i = 0 then (L i k).re else (L i k).im)).det : ℂ) := by
    intro f
    have hmat : Matrix.of (fun k => row k (f k))
        = (Matrix.of (fun i k =>
            if f i = 0 then (L i k).re else (L i k).im)).map (algebraMap ℝ ℂ) := by
      ext i j
      simp only [Matrix.of_apply, Matrix.map_apply, row]
      by_cases h : f i = 0 <;> simp [h]
    rw [hmat, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rfl
  by_contra hcon
  simp only [not_exists, ne_eq, not_not] at hcon
  apply hdet
  rw [hmain]
  apply Finset.sum_eq_zero
  intro f _
  rw [key f, hcon f]
  simp

end Commons.LinearAlgebra.Matrix