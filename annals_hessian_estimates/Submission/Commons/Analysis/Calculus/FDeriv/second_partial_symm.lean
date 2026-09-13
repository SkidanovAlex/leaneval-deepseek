import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Laplacian

open scoped Topology ContDiff

namespace Commons.Analysis.Calculus.FDeriv

/-- The second iterated derivative (Hessian) of a `C^2` real function on an open set is
symmetric: mixed partial derivatives in the directions of an orthonormal basis commute. -/
theorem second_partial_symm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι] (v : OrthonormalBasis ι ℝ E) {s : Set E}
    {u : E → ℝ} {x : E} (hs : IsOpen s) (hx : x ∈ s) (hu : ContDiffOn ℝ 2 u s) (i j : ι) :
    bilinearIteratedFDerivTwo ℝ u x (v i) (v j) =
      bilinearIteratedFDerivTwo ℝ u x (v j) (v i) := by
  -- From C^2 on the open set `s` we obtain C^2 at `x`, hence the second derivative at `x`
  -- is symmetric (`IsSymmSndFDerivAt`).
  have hsymm : IsSymmSndFDerivAt ℝ u x :=
    ContDiffAt.isSymmSndFDerivAt (𝕜 := ℝ) (n := 2) (hu.contDiffAt (hs.mem_nhds hx))
      (by simp)
  -- The bilinear iterated derivative agrees with the iterated derivative on the pair, and
  -- symmetry of the latter swaps the two vectors.
  rw [bilinearIteratedFDerivTwo_eq_iteratedFDeriv, bilinearIteratedFDerivTwo_eq_iteratedFDeriv]
  exact hsymm.iteratedFDeriv_cons (v := v i) (w := v j)

end Commons.Analysis.Calculus.FDeriv