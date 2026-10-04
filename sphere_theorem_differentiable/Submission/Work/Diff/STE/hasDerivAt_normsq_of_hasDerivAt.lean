import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE

theorem hasDerivAt_normsq_of_hasDerivAt {f : ℝ → ℂ} {z' : ℂ} {t : ℝ}
    (h : HasDerivAt f z' t) :
    HasDerivAt (fun s => ‖f s‖ ^ 2) (2 * (z' * star (f t)).re) t := by
  -- `HasDerivAt.norm_sq` gives the derivative `2 * ⟪f t, z'⟫_ℝ`, and on `ℂ` the real inner
  -- product is `⟪w, v⟫_ℝ = (v * star w).re`.
  simpa [Complex.inner] using h.norm_sq

end Work.Diff.STE
