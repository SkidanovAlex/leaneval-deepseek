import Mathlib
import Submission.Commons.Analysis.Calculus.Laplacian.laplacian_nonpos_of_isLocalMax

open Filter
open scoped Topology

namespace Commons.Analysis.Calculus.Laplacian

theorem laplacian_nonpos_of_isLocalMaxOn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {s : Set E} {u : E → ℝ} {x : E} (hs : IsOpen s) (hx : x ∈ s)
    (hu : ContDiffOn ℝ 2 u s) (hmax : IsLocalMaxOn u s x) :
    Laplacian.laplacian u x ≤ 0 := by
  have hsx : s ∈ 𝓝 x := hs.mem_nhds hx
  exact laplacian_nonpos_of_isLocalMax (hu.contDiffAt hsx) (hmax.isLocalMax hsx)

end Commons.Analysis.Calculus.Laplacian
