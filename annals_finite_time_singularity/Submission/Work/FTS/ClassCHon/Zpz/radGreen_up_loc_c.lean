import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon.Zpz

/-- **Local integrability of the `rgB`-integrand near the lower end `z > 0`.**

For `c : ℝ → ℝ` differentiable at every `t > 0` (i.e. `HasDerivAt c (deriv c t) t` for `t > 0`)
and any exponents `p`, the integrand `t ↦ c t * t ^ (-p - 1)` of `rgB` is integrable on the
interval `(z, 1)` for every `z > 0`.

The point is that the cluster point `0` of the singularity of `t ↦ t^{-p-1}` lies outside the
interval: on the compact `[z,1] ⊂ (0,∞)` the function `c` is continuous (differentiability at
each point of `(0,∞)`), hence bounded, and `t ↦ t ^ (-p - 1)` is continuous there as well, so the
product is continuous — hence integrable — on the compact set `[z, 1]`; restrict to `(z,1)`.
(If `1 ≤ z` the interval `(z,1)` is empty.) -/
lemma radGreen_up_loc_c {c : ℝ → ℝ} {p z : ℝ} (hz : 0 < z)
    (hcd : ∀ t : ℝ, 0 < t → HasDerivAt c (deriv c t) t) :
    MeasureTheory.IntegrableOn (fun t => c t * t ^ (-p - 1)) (Set.Ioo z 1) := by
  rcases le_or_gt 1 z with h1z | hz1
  · -- `(z,1) = ∅`
    rw [Set.Ioo_eq_empty (not_lt.mpr h1z)]
    exact MeasureTheory.integrableOn_empty
  · -- `z < 1`: `c` is continuous on the compact `[z,1] ⊆ (0,∞)`, and so is `t ↦ t^{-p-1}`
    have hcontc : ContinuousOn c (Set.Icc z 1) := fun x hx =>
      (hcd x (lt_of_lt_of_le hz hx.1)).continuousAt.continuousWithinAt
    have hcontr : ContinuousOn (fun t : ℝ => t ^ (-p - 1)) (Set.Icc z 1) :=
      continuousOn_id.rpow_const fun x hx =>
        Or.inl (ne_of_gt (lt_of_lt_of_le hz hx.1))
    have hInt : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-p - 1)) (Set.Icc z 1) :=
      (hcontc.mul hcontr).integrableOn_compact isCompact_Icc
    exact hInt.mono_set Set.Ioo_subset_Icc_self

end Work.FTS.ClassCHon.Zpz
