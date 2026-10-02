import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FBif

/-- **The telescoping identity for the difference of fifth iterates of two maps.** For arbitrary maps `f g : ℂ → ℂ` and points `x y`, `f^[5] x - g^[5] x - (f^[5] y - g^[5] y)` is the sum over `j = 0,…,4` of the differences of the `j`-th terms `f^[5-j] (g^[j] ·) - f^[5-(j+1)] (g^[j+1] ·)`, evaluated at `x` and at `y`. -/
theorem five_telescope (f g : ℂ → ℂ) (x y : ℂ) :
    ((f^[5]) x - (g^[5]) x) - ((f^[5]) y - (g^[5]) y)
      = ∑ j ∈ Finset.range 5,
          (((f^[5 - j]) ((g^[j]) x) - (f^[5 - (j + 1)]) ((g^[j + 1]) x))
            - ((f^[5 - j]) ((g^[j]) y) - (f^[5 - (j + 1)]) ((g^[j + 1]) y))) := by
  -- Distribute the sum over the two subtractions, then telescope each of the two
  -- resulting sums with `Finset.sum_range_sub'`.
  rw [Finset.sum_sub_distrib]
  rw [Finset.sum_range_sub' (f := fun j => (f^[5 - j]) ((g^[j]) x))]
  rw [Finset.sum_range_sub' (f := fun j => (f^[5 - j]) ((g^[j]) y))]
  simp

end Work.FBif
