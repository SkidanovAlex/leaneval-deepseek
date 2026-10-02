import Mathlib
import Submission.Work.Implosion.Phase
import Submission.Work.Implosion.Phase.modelOrbit_re_decrease

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Implosion.Phase

/-- **A model orbit meets a slab of width `W < 1 - δ` at most once.**  Between
two times the real part of the model orbit drops by at least `1 - δ` per step
(`modelOrbit_re_decrease`); a slab whose width is strictly smaller than that
per-step drop therefore cannot contain the orbit at two different times. -/
theorem modelOrbit_slab_at_most_once (a : ℂ) (h : ℂ → ℂ) (u : ℂ) (δ W x : ℝ) (hδ1 : δ < 1)
    (hW : W < 1 - δ) (hδ : ∀ k : ℕ, ‖modelDisp a h (modelOrbit a h k u) + 1‖ ≤ δ) {m n : ℕ}
    (hmn : m < n) (hmx : x ≤ (modelOrbit a h m u).re) (hmX : (modelOrbit a h m u).re < x + W)
    (hnx : x ≤ (modelOrbit a h n u).re) (hnX : (modelOrbit a h n u).re < x + W) : False := by
  -- the per-step drop in the real part is strictly positive
  have hpos : (0 : ℝ) < 1 - δ := sub_pos.mpr hδ1
  -- at least one step separates `m` from `n`
  have hone : (1 : ℕ) ≤ n - m := by omega
  have hcast : (1 : ℝ) ≤ (n - m : ℕ) := by exact_mod_cast hone
  -- hence the accumulated drop over the `n - m` steps is at least `1 - δ`
  have hdrop : (1 : ℝ) - δ ≤ (n - m : ℕ) * (1 - δ) := by
    have := mul_le_mul_of_nonneg_right hcast (le_of_lt hpos)
    simpa using this
  have hle := modelOrbit_re_decrease a h u δ hmn.le (fun k _ => hδ k)
  -- the `n`-th point lies strictly below the bottom of the slab
  have hlt : (modelOrbit a h n u).re < x + W - (1 - δ) := by linarith
  -- contradicted by the `n`-th point being inside the slab, and `W < 1 - δ`
  have : x < x + W - (1 - δ) := by linarith
  linarith

end Work.Implosion.Phase
