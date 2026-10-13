import Mathlib
import Submission.Work.WilE9G.Lagrange.LagBlocks

namespace Work.WilE9G.Lagrange

/-- The `(L,yt)` block `lagA2` of `lagJacTrue` is the transpose of the `(L,yt)` block `lagA1` of
`lagJac` (mixed `eaD`'s commute, `Work.WilE3.API.eaD_commute`). -/
theorem lagA2_eq_transpose {n m : ℕ} (S : Work.WilE9G.AmbStratum (n + (1 + m)))
    (Phi : WilkiesDesign.E.EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ)
    (z : Fin (n + (1 + m)) → ℝ) (mu : Fin S.j → ℝ) (mu0 : ℝ) :
    Work.WilE9G.Lagrange.lagA2 S Phi c z mu mu0
      = (Work.WilE9G.Lagrange.lagA1 S Phi c z mu mu0).transpose := by
  -- Entrywise: the transpose of `lagA1` at `(i,k)` is `lagA1 k i`, whose `(L,yt)` terms are
  -- `μ₀(∂_i∂_k Φ + (∂_k Φ) c_i) - ∑_a μ_a ∂_i∂_k h_a`; the mixed derivatives commute, so the two
  -- mixed-derivative occurrences (`Φ` and each `h_a`) agree with those of `lagA2 i k`.
  ext i k
  simp only [lagA2, lagA1, Matrix.transpose_apply, Matrix.of_apply]
  simp_rw [Work.WilE3.API.eaD_commute S.X.c (Fin.natAdd n k) (Fin.natAdd n i)]

end Work.WilE9G.Lagrange
