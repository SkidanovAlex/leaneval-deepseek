import Mathlib
import Submission.Work.SeedFatou.Defs
import Submission.Work.ELRig.Pa_subset_K

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedFatou

open Filter Function
open scoped Topology

open LeanEval.ComplexAnalysis (Tantibar)

/-- The basin of the fixed point `z₁` of `F c = (T_c)^[10]` is contained in the filled Julia set
of `T_c`.

Mathematically: a point of the basin has `(F c)`-orbit converging to `z₁`, hence the
subsequence of its `T_c`-orbit with indices divisible by `10` converges, hence the `T_c`-orbit
is bounded (`Work.ELRig.boundedOrbit_of_tendsto_iterate_mul`), which is membership in
`Work.EL.K c = Work.ParamRays.filledJulia c`. -/
theorem basin_subset_K (c z₁ : ℂ) :
    Work.FatouParabolic.basin (Work.FSeed.F c) z₁ ⊆ Work.EL.K c := by
  intro z hz
  -- `hz : Tendsto (fun n => (FSeed.F c)^[n] z) atTop (𝓝 z₁)`
  have hiter : ∀ n : ℕ, (Work.FSeed.F c)^[n] z = (Tantibar c)^[10 * n] z := by
    intro n
    rw [F_eq_tantibar_ten c, Function.iterate_mul]
  -- the `T_c`-orbit of `z` along the multiples of `10` converges to `z₁`
  have hsub : Tendsto (fun n : ℕ => (Tantibar c)^[10 * n] z) atTop (𝓝 z₁) :=
    Tendsto.congr' (Eventually.of_forall hiter) hz
  exact Work.ELRig.boundedOrbit_of_tendsto_iterate_mul (by norm_num) hsub

end Work.SeedFatou
