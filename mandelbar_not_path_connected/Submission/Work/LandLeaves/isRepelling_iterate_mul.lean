import Mathlib
import Submission.Work.LANDCL.Defs
import Submission.Work.LandLeaves.Defs
import Submission.Work.LandLeaves.boundedOrbit_of_ball

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Repelling periodic points stay repelling at multiples of the period

`Work.Landing.IsRepelling c k y` says that `y` is fixed by `(T_c)^[k]` (`T_c` the
antiholomorphic quadratic `z ↦ z̄² + c`) and that the holomorphic second return map
`(Tsq c)^[k] = (T_c)^{2k}` has multiplier of modulus `> 1` at `y`.  Both parts survive
passing from `k` to any positive multiple `k * q`:

* `(T_c)^[k*q] = ((T_c)^[k])^[q]`, and `y` is fixed by `(T_c)^[k]`;
* `(Tsq c)^[k*q] = ((Tsq c)^[k])^[q]`; since `y` is fixed by the differentiable map
  `(Tsq c)^[k]`, the chain rule along the constant orbit gives
  `deriv ((Tsq c)^[k*q]) y = (deriv ((Tsq c)^[k]) y)^q`, whose modulus is
  `‖deriv ((Tsq c)^[k]) y‖ ^ q > 1`.
-/

namespace Work.LandLeaves

open Function
open LeanEval.ComplexAnalysis (Tantibar)

theorem isRepelling_iterate_mul {c : ℂ} {k q : ℕ} {y : ℂ}
    (h : Work.Landing.IsRepelling c k y) (hq : 0 < q) :
    Work.Landing.IsRepelling c (k * q) y := by
  obtain ⟨⟨hk, hfix⟩, hmul⟩ := h
  refine ⟨⟨Nat.mul_pos hk hq, ?_⟩, ?_⟩
  · -- `(T_c)^[k*q] y = y`
    rw [Function.iterate_mul]
    exact Function.IsFixedPt.iterate hfix q
  · -- the multiplier of the `k*q`-th second return map
    have hdiff : Differentiable ℂ (Work.Landing.Tsq c) := by
      unfold Work.Landing.Tsq
      fun_prop
    -- `y` is fixed by `(Tsq c)^[k] = (T_c)^[2*k]`
    have hgfix : ((Work.Landing.Tsq c)^[k]) y = y := by
      rw [Tsq_eq_iterate_two, ← Function.iterate_mul]
      rw [show (2 : ℕ) * k = k * 2 from Nat.mul_comm 2 k, Function.iterate_mul]
      exact Function.IsFixedPt.iterate hfix 2
    -- chain rule at the fixed point
    have hmain : deriv ((Work.Landing.Tsq c)^[k * q]) y =
        (deriv ((Work.Landing.Tsq c)^[k]) y) ^ q := by
      rw [Function.iterate_mul]
      exact (HasDerivAt.iterate y
        (((hdiff.iterate k).differentiableAt).hasDerivAt) hgfix q).deriv
    have hpow : 1 < ‖deriv ((Work.Landing.Tsq c)^[k]) y‖ ^ q := by
      calc (1 : ℝ) < ‖deriv ((Work.Landing.Tsq c)^[k]) y‖ := hmul
        _ = ‖deriv ((Work.Landing.Tsq c)^[k]) y‖ ^ 1 := (pow_one _).symm
        _ ≤ ‖deriv ((Work.Landing.Tsq c)^[k]) y‖ ^ q :=
            pow_le_pow_right₀ (le_of_lt hmul) hq
    show 1 < ‖Work.Landing.multiplier2 c (k * q) y‖
    rw [Work.Landing.multiplier2, hmain, norm_pow]
    exact hpow

end Work.LandLeaves
