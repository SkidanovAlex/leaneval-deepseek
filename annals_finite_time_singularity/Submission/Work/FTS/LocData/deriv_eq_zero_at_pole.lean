import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.LocData

/-- `z ↦ A z / (1 + z) ^ m` has a pole of order `m ≥ 1` at `z = -1` whenever
`A (-1) ≠ 0` (and `A` is continuous there), so it is *not* differentiable at
`-1`.  Since Lean's `deriv` takes the junk value `0` at points of
non-differentiability, the derivative there is `0`. -/
theorem deriv_eq_zero_at_pole (A : ℝ → ℝ) (m : ℕ) (hm : 0 < m)
    (hA : ContinuousAt A (-1)) (hA0 : A (-1) ≠ 0) :
    deriv (fun z => A z / (1 + z) ^ m) (-1) = 0 := by
  -- `deriv` is `0` at any point where the function is not differentiable.
  apply deriv_zero_of_not_differentiableAt
  intro hd
  -- Differentiability would give continuity at the pole.
  have hc : ContinuousAt (fun z => A z / (1 + z) ^ m) (-1) := hd.continuousAt
  -- The value there is the junk value `A (-1) / 0 ^ m = 0`.
  have hzero : A (-1) / (0 : ℝ) ^ m = 0 := by
    rw [zero_pow hm.ne', div_zero]
  -- Multiply the continuous function by `(1 + y) ^ m`, which tends to `0`.
  have hprod : Filter.Tendsto (fun y : ℝ => (A y / (1 + y) ^ m) * (1 + y) ^ m)
      (nhds (-1)) (nhds 0) := by
    have h1 : Filter.Tendsto (fun y : ℝ => A y / (1 + y) ^ m) (nhds (-1)) (nhds 0) := by
      simpa [hzero] using hc.tendsto
    have h2 : Filter.Tendsto (fun y : ℝ => (1 + y) ^ m) (nhds (-1)) (nhds ((1 + (-1)) ^ m)) :=
      ((continuous_const.add continuous_id).pow m).tendsto (-1)
    simpa using h1.mul h2
  -- Off the pole the product is just `A`, so along the punctured neighbourhood
  -- of `-1` we get `A y → 0`.
  have hAt : Filter.Tendsto A (nhdsWithin (-1) {(-1 : ℝ)}ᶜ) (nhds 0) := by
    have hp : Filter.Tendsto (fun y : ℝ => (A y / (1 + y) ^ m) * (1 + y) ^ m)
        (nhdsWithin (-1) {(-1 : ℝ)}ᶜ) (nhds 0) := hprod.mono_left nhdsWithin_le_nhds
    refine hp.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy' : (1 + y : ℝ) ≠ 0 := by
      intro h; exact (Set.mem_compl_singleton_iff.mp hy) (by linarith)
    show (A y / (1 + y) ^ m) * (1 + y) ^ m = A y
    rw [div_mul_cancel₀ _ (pow_ne_zero m hy')]
  -- But continuity of `A` at `-1` also gives `A y → A (-1)`, and limits are unique.
  have hA'' : Filter.Tendsto A (nhdsWithin (-1) {(-1 : ℝ)}ᶜ) (nhds (A (-1))) :=
    hA.tendsto.mono_left nhdsWithin_le_nhds
  exact hA0 (tendsto_nhds_unique hA'' hAt)

end Work.FTS.LocData
