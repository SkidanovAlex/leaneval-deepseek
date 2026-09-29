import Mathlib

/-!
# `Work.ZeroEst.case_det_detne`

If the rows of a square matrix `M` of polynomials over `ℚ` become linearly independent over the
field `RatFunc ℚ = ℚ(X)` after reducing the entries modulo the fraction field
(`(M k j : RatFunc ℚ)`), then `M.det ≠ 0`.

The proof is the contrapositive: `M.det = 0` forces the rows to be linearly dependent over `ℚ(X)`
as well.  Concretely, let `N := M.map (· : Polynomial ℚ → RatFunc ℚ)`. Then

* `N.det = (M.det : RatFunc ℚ)` (`RingHom.map_det`), and
* the hypothesis says exactly that `N.row` is linearly independent over the field `RatFunc ℚ`,
  which over a field is equivalent to `IsUnit N.det` (`Matrix.linearIndependent_rows_iff_isUnit`),
  hence to `N.det ≠ 0`.

So `M.det = 0` would give `IsUnit (0 : RatFunc ℚ)`, a contradiction.
-/

namespace Work.ZeroEst

theorem case_det_detne {m : ℕ} (M : Matrix (Fin m) (Fin m) (Polynomial ℚ))
    (h : LinearIndependent (RatFunc ℚ) (fun k : Fin m => fun j : Fin m => (M k j : RatFunc ℚ))) :
    M.det ≠ 0 := by
  intro hdet
  have hLI : LinearIndependent (RatFunc ℚ)
      (M.map (fun p : Polynomial ℚ => (p : RatFunc ℚ))).row := h
  have hunit : IsUnit (M.map (fun p : Polynomial ℚ => (p : RatFunc ℚ))).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_rows_iff_isUnit.mp hLI)
  have hNdet : (M.map (fun p : Polynomial ℚ => (p : RatFunc ℚ))).det = (M.det : RatFunc ℚ) := by
    have key := RingHom.map_det (algebraMap (Polynomial ℚ) (RatFunc ℚ)) M
    rw [RingHom.mapMatrix_apply] at key
    simpa using key.symm
  rw [hNdet, hdet] at hunit
  simp at hunit

end Work.ZeroEst
