import Mathlib

namespace Work.WilE4.CAD

/-- The rank of the Sylvester matrix of `f` and `g` (with shifts `m ≥ natDegree f` and
`n ≥ natDegree g`) equals the dimension of the range of the Sylvester map
`(p, q) ↦ f * q + g * p`, which is the linear map whose matrix is the Sylvester matrix. -/
theorem rank_sylvester_eq_finrank_range (f g : Polynomial ℝ) (m n : ℕ)
    (hm : f.natDegree ≤ m) (hn : g.natDegree ≤ n) :
    (Polynomial.sylvester f g m n).rank
      = Module.finrank ℝ (LinearMap.range (Polynomial.sylvesterMap f g hm hn)) := by
  -- `b₁` indexes `ℝ[X]_m × ℝ[X]_n` by `Fin (m + n)`, `b₂` indexes `ℝ[X]_(m+n)`.
  let b₁ := ((Polynomial.degreeLT.basis ℝ m).prod (Polynomial.degreeLT.basis ℝ n)).reindex
    finSumFinEquiv
  let b₂ := Polynomial.degreeLT.basis ℝ (m + n)
  -- Mathlib: the matrix of the Sylvester map in these bases is the Sylvester matrix.
  have hmat : (Polynomial.sylvesterMap f g hm hn).toMatrix b₁ b₂
      = Polynomial.sylvester f g m n :=
    Polynomial.toMatrix_sylvesterMap' f g hm hn
  -- The rank of a matrix is the dimension of the range of the associated linear map.
  rw [Matrix.rank_eq_finrank_range_toLin _ b₂ b₁, ← hmat, Matrix.toLin_toMatrix]

end Work.WilE4.CAD
