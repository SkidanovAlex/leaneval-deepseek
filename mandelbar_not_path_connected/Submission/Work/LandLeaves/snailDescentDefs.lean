/-
Copyright: subproject `Submission/Work/LandLeaves/` of `mandelbar_not_path_connected`.

# Vocabulary for the descent ("Snail") argument

The neutral case of the Snail lemma `Work.LandLeaves.SnailLemmaMilnor` is handled as follows.

* If `deriv g z₀` is a primitive `q`-th root of unity (`q ≥ 2`), put `h = g^q`: then `h` has
  multiplier `1` at `z₀`, so `h z = z + c z^r + O(z^(r+1))` with `c ≠ 0`, `r ≥ 2`.  The Snail
  path `p` is a Snail path for `h` (`h (p t) = p (t+q)`), and the *descent chart*
  `Z w = 1 / (((r:ℂ)-1) * c * w^(r-1))` turns `h` into a translation by `-1` up to an error of
  size `O(‖Z w‖^(-1/(r-1)))` (`Work.LandLeaves.chart_descent_bound`).  Along the path the error
  is small and of one sign, which forces `Re (Z (p t)) → -∞`; consequently the tail of `p`
  eventually lies in the "petal" `{w | Re (c * w^(r-1)) < 0}`, so every limit direction `d` of the
  tail satisfies `Re (c * d^(r-1)) ≤ 0`, a *proper* closed subset of the unit circle.

* On the other hand the limit set `directionLimitSet (fun t => p t - z₀)` of the directions of the
  path is a compact, nonempty, preconnected subset of the unit circle which is invariant under
  multiplication by `deriv g z₀` (because `g w = λ w + O(w²)` rotates the direction of `w` by
  `arg λ` up to `o(1)`).

* A compact preconnected subset of the unit circle which is invariant under multiplication by a
  nontrivial root of unity `λ` must be the whole unit circle; this contradicts the previous
  paragraph.

This file only fixes the vocabulary shared by the pieces of that argument.
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

open Filter Set
open scoped Topology

/-- **The set of limit directions of a path `q`**: the intersection, over all `T ≥ 0`, of the
closures of the sets of directions `q t / ‖q t‖` for `t ≥ T`. -/
def directionLimitSet (q : ℝ → ℂ) : Set ℂ :=
  ⋂ T ∈ Set.Ici (0 : ℝ), closure ((fun t : ℝ => q t / ((‖q t‖ : ℝ) : ℂ)) '' Set.Ici T)

end Work.LandLeaves
