/-
# The layer strata cover the filling piece `W_v`

The filling piece of the `v`-th cusp is `W_v = Sq × (ℝ/ℤ)²` (`W` in `Work.Cusp.Basic`), where
`Sq = [-1,1]²` is the square of layer parameters and `(y₂,y₃) ∈ (ℝ/ℤ)²` are the two torus
coordinates.  The three layer strata of the charts are

* `coreStratum = {‖p‖∞ < 1/12}` (the source of the core chart, `r < 1/2`),
* `polarStratum = {1/24 < ‖p‖∞ ≤ 1}` (the source of the polar charts, `r > 1/4`),
* `cuspStratum = {1/2 < ‖p‖∞ ≤ 1}` (the collar, `r_J < r ≤ R₀ − log β`).

Here we record the pointwise form of the cover: **every** point of `W_v` has its layer parameter in
one of the three strata (the torus coordinates `y` play no role, and the third stratum is in fact
redundant for the cover, since `cuspStratum ⊆ polarStratum`).  This is the ingredient the assembly
of the charts of `M̂` uses to dispatch a point of the filling piece to a chart.

The mathematics is immediate: `p ∈ Sq` gives `‖p‖∞ = max(|p 0|, |p 1|) ≤ 1`, and the three
intervals `[0, 1/12)`, `(1/24, 1]`, `(1/2, 1]` cover `[0,1]`.  The global form of the same fact is
`Work.Cusp.strata_cover : coreStratum ∪ polarStratum ∪ cuspStratum = Sq`; the pointwise statement
proved here is what the cover argument consumes, and it is proved directly from `Sq` so that it does
not depend on that equality.
-/
import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.Charts

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- **The layer parameter of a point of the square lies in one of the strata.**  If
`p ∈ Sq = [-1,1]²` then `‖p‖∞ ≤ 1` and either `‖p‖∞ < 1/12` (core), or `1/24 < ‖p‖∞ ≤ 1` (polar),
or `1/2 < ‖p‖∞ ≤ 1` (cusp). -/
theorem mem_strata_of_mem_Sq {p : E2} (hp : p ∈ Sq) :
    p ∈ coreStratum ∪ polarStratum ∪ cuspStratum := by
  -- `p ∈ Sq` unfolds to `|p 0| ≤ 1 ∧ |p 1| ≤ 1`, hence `‖p‖∞ = max |p 0| |p 1| ≤ 1`.
  have hp' : |p 0| ≤ 1 ∧ |p 1| ≤ 1 := hp
  have hle : nrm p ≤ 1 := max_le hp'.1 hp'.2
  -- Split on the core condition `‖p‖∞ < 1/12`; in the remaining case `1/12 ≤ ‖p‖∞ > 1/24` so the
  -- polar stratum already applies.
  by_cases h : nrm p < 1/12
  · exact Or.inl (Or.inl h)
  · refine Or.inl (Or.inr ⟨?_, hle⟩)
    exact lt_of_lt_of_le (by norm_num) (not_lt.mp h)

/-- Every point `z = (p, y)` of the filling piece `W_v = Sq × (ℝ/ℤ)²` has its layer parameter `p`
in one of the three layer strata.  The torus coordinates `y` are irrelevant. -/
theorem W_cover (z : W) : z.1.1 ∈ coreStratum ∪ polarStratum ∪ cuspStratum :=
  mem_strata_of_mem_Sq z.1.2

end Work.Cusp
