import Mathlib

/-!
# The range of a continuous periodic curve is closed

If `γ : ℝ → E` is continuous and periodic with period `T > 0`, then `γ` is determined by its
values on the compact interval `[0, T]`, so `Set.range γ = γ '' [0, T]` is compact, hence closed
(in the Hausdorff space `E = EuclideanSpace ℝ (Fin n)`).

This is used to see that the curve arising from a circle parametrisation of a compact
`1`-manifold is a closed set.
-/

namespace Work.ManifoldParity

open Set

theorem isClosed_range_of_periodic {n : ℕ} {γ : ℝ → EuclideanSpace ℝ (Fin n)} {T : ℝ}
    (hT : 0 < T) (hcont : Continuous γ) (hper : Function.Periodic γ T) :
    IsClosed (Set.range γ) := by
  rw [← hper.image_Icc hT 0]
  exact (isCompact_Icc.image hcont).isClosed

end Work.ManifoldParity
