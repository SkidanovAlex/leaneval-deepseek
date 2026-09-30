import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter
open scoped Topology

namespace Commons.Analysis.Calculus

/-- If `E` has a local minimum at `a`, is differentiable at `a` with derivative `0`, and its
derivative `deriv E` is differentiable at `a` with derivative `c`, then `0 ≤ c`. -/
theorem deriv_deriv_nonneg_of_isLocalMin {E : ℝ → ℝ} {a c : ℝ}
    (h1 : HasDerivAt E 0 a) (h2 : HasDerivAt (deriv E) c a) (hmin : IsLocalMin E a) :
    0 ≤ c := by
  by_contra hle
  push Not at hle
  -- `c < 0`, so `E` has a local maximum at `a` by the second-derivative test.
  have hmax : IsLocalMax E a := by
    refine isLocalMax_of_deriv_deriv_neg ?_ ?_ ?_
    · rw [h2.deriv]; exact hle
    · exact h1.deriv
    · exact h1.continuousAt
  -- `E` is locally constant at `a`.
  have heq : E =ᶠ[𝓝 a] (fun _ => E a) := by
    have hmin' : ∀ᶠ x in 𝓝 a, E a ≤ E x := hmin
    have hmax' : ∀ᶠ x in 𝓝 a, E x ≤ E a := hmax
    filter_upwards [hmin', hmax'] with x hx1 hx2
    exact le_antisymm hx2 hx1
  -- hence `deriv E` vanishes near `a`, so `deriv (deriv E) a = 0 = c`.
  have hderiv : deriv E =ᶠ[𝓝 a] (fun _ => (0 : ℝ)) := by
    filter_upwards [heq.deriv] with x hx
    rw [hx, deriv_const]
  have h0 : deriv (deriv E) a = 0 := by
    rw [hderiv.deriv_eq, deriv_const]
  rw [h2.deriv] at h0
  linarith

end Commons.Analysis.Calculus