import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllExist.Honesty.RadGreenDzuDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllExist.Honesty

-- `Dzu` (in `Work.FTS.EllExist.Honesty.RadGreenDzuDefs`) is `(z ∂_z)^i` on `ℝ → ℝ`.
-- If `f` satisfies the first-order relation `z f'(z) = lam * f(z) + A(z)` for all `z > 0`
-- (phrased as `HasDerivAt f ((lam * f z + A z) / z) z`), then for every `i`
--   `Dzu i f z = lam^i * f z + ∑_{t<i} lam^{i-1-t} * Dzu t A z`     (`z > 0`).
-- ROUTE: induction on `i`; at the step use `Dzu (i+1) f z = z * deriv (Dzu i f) z`, rewrite
-- `deriv (Dzu i f) z` by `Filter.EventuallyEq.deriv_eq` using the induction hypothesis on a
-- neighbourhood of `z` (only `z > 0` is needed), then `deriv_sum`/`deriv_const_mul`/`deriv_add`
-- (which need `DifferentiableAt` of `f` — from the hypothesis — and of the `Dzu t A`, which is
-- exactly `hA`), and `deriv (Dzu t A) z = Dzu (t+1) A z / z` for `z ≠ 0`, which is definitional.
-- The arithmetic at the end is `Finset.sum_range_succ` + `ring`.

theorem dzu_recursion {f A : ℝ → ℝ} {lam : ℝ} {n : ℕ}
    (hf : ∀ z : ℝ, 0 < z → HasDerivAt f ((lam * f z + A z) / z) z)
    (hA : ∀ t ≤ n, ∀ z : ℝ, 0 < z →
      DifferentiableAt ℝ (Work.FTS.EllExist.Honesty.Dzu t A) z) :
    ∀ i ≤ n, ∀ z : ℝ, 0 < z →
      Work.FTS.EllExist.Honesty.Dzu i f z
        = lam ^ i * f z
          + ∑ t ∈ Finset.range i,
              lam ^ (i - 1 - t) * Work.FTS.EllExist.Honesty.Dzu t A z := by
  intro i
  induction i with
  | zero => intro _ z _; simp
  | succ k ih =>
    intro hk z hz
    have hzk : k ≤ n := Nat.le_of_succ_le hk
    have hz0 : z ≠ 0 := ne_of_gt hz
    -- the closed-form right-hand side, which `Dzu k f` agrees with on `(0,∞)`
    have hagree : Filter.EventuallyEq (nhds z) (Dzu k f)
        (fun w => lam ^ k * f w
          + ∑ t ∈ Finset.range k, lam ^ (k - 1 - t) * Dzu t A w) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
      exact ih hzk w hw
    -- derivative of the sum, termwise
    have hsum : HasDerivAt
        (fun w => ∑ t ∈ Finset.range k, lam ^ (k - 1 - t) * Dzu t A w)
        (∑ t ∈ Finset.range k, lam ^ (k - 1 - t) * deriv (Dzu t A) z) z := by
      refine HasDerivAt.fun_sum (A := fun t w => lam ^ (k - 1 - t) * Dzu t A w)
        (A' := fun t => lam ^ (k - 1 - t) * deriv (Dzu t A) z) ?_
      intro t ht
      exact ((hA t (le_trans (Finset.mem_range.mp ht).le hzk) z hz).hasDerivAt).const_mul _
    have hstep : HasDerivAt
        (fun w => lam ^ k * f w
          + ∑ t ∈ Finset.range k, lam ^ (k - 1 - t) * Dzu t A w)
        (lam ^ k * ((lam * f z + A z) / z)
          + ∑ t ∈ Finset.range k, lam ^ (k - 1 - t) * deriv (Dzu t A) z) z :=
      ((hf z hz).const_mul (lam ^ k)).add hsum
    -- distributing `z` over the two pieces
    have hLsum : z * (∑ t ∈ Finset.range k, lam ^ (k - 1 - t) * deriv (Dzu t A) z)
        = ∑ t ∈ Finset.range k, lam ^ (k - 1 - t) * Dzu (t + 1) A z := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      show z * (lam ^ (k - 1 - t) * deriv (Dzu t A) z)
        = lam ^ (k - 1 - t) * Dzu (t + 1) A z
      rw [show Dzu (t + 1) A z = z * deriv (Dzu t A) z from rfl]
      ring
    have hRsum : (∑ t ∈ Finset.range (k + 1), lam ^ (k + 1 - 1 - t) * Dzu t A z)
        = (∑ t ∈ Finset.range k, lam ^ (k - 1 - t) * Dzu (t + 1) A z)
          + lam ^ k * A z := by
      rw [Finset.sum_range_succ']
      rw [show (∑ t ∈ Finset.range k,
            lam ^ (k + 1 - 1 - (t + 1)) * Dzu (t + 1) A z)
          = (∑ t ∈ Finset.range k, lam ^ (k - 1 - t) * Dzu (t + 1) A z) from
        Finset.sum_congr rfl (fun t _ => by
          rw [show k + 1 - 1 - (t + 1) = k - 1 - t from by omega])]
      rw [show k + 1 - 1 - 0 = k from by omega, Dzu_zero]
    -- and the first term, where the first-order relation is used
    have hzpart : z * (lam ^ k * ((lam * f z + A z) / z))
        = lam ^ (k + 1) * f z + lam ^ k * A z := by
      have h1 : z * ((lam * f z + A z) / z) = lam * f z + A z := mul_div_cancel₀ _ hz0
      calc z * (lam ^ k * ((lam * f z + A z) / z))
          = lam ^ k * (z * ((lam * f z + A z) / z)) := by ring
        _ = lam ^ k * (lam * f z + A z) := by rw [h1]
        _ = lam ^ (k + 1) * f z + lam ^ k * A z := by rw [pow_succ]; ring
    change z * deriv (Dzu k f) z = lam ^ (k + 1) * f z
      + ∑ t ∈ Finset.range (k + 1), lam ^ (k + 1 - 1 - t) * Dzu t A z
    rw [hagree.deriv_eq, hstep.deriv]
    rw [mul_add, hLsum, hzpart, hRsum]
    ring

end Work.FTS.EllExist.Honesty
