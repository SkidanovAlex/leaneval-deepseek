import Mathlib
import Submission.Work.FSeed.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FSeed.API

/-- **The multiplier of a fixed point.**  If `g : ℂ → ℂ` is differentiable and `z` is a fixed
point of `g`, then the `n`-th iterate of `g` has derivative `(g'z)^n` at `z`.

This is the chain rule applied along the (constant) orbit `z, g z, g² z, …  = z, z, z, …`: the
derivative of an iterate is the product of the derivatives at the points of the orbit, and here
every one of those points is `z`. -/
theorem deriv_iterate_fixed {g : ℂ → ℂ} (hg : Differentiable ℂ g) {z : ℂ} (hz : g z = z) :
    ∀ n : ℕ, deriv (g^[n]) z = (deriv g z) ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    have hzk : (g^[k]) z = z := Function.IsFixedPt.iterate hz k
    have hdc : deriv (g ∘ g^[k]) z = deriv g ((g^[k]) z) * deriv (g^[k]) z :=
      deriv_comp (x := z) (h := g^[k]) (h₂ := g) (hg (g^[k] z)) ((hg.iterate k) z)
    rw [Function.iterate_succ', hdc, hzk, ih, pow_succ']

theorem deriv_iterate_periodic {f : ℂ → ℂ} (hf : Differentiable ℂ f) {z : ℂ} {m : ℕ}
    (hm : 0 < m) (hper : (f^[m]) z = z) (n : ℕ) :
    deriv (f^[m * n]) z = (deriv (f^[m]) z) ^ n := by
  rw [Function.iterate_mul]
  exact deriv_iterate_fixed (hf.iterate m) hper n

end Work.FSeed.API
