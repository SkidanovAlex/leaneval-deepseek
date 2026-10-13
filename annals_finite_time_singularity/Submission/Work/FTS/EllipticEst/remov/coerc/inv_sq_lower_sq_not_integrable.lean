import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.NonIntegrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `1/θ²` is not integrable near `0`

The function `θ ↦ k / θ²` (with `k > 0`) is not integrable on any interval `(0, δ)`, so a square
`f²` that dominates it pointwise cannot be integrable either:

  `k / θ² ≤ f θ ^ 2` on `(0, δ)`  and  `f² ∈ L¹(0, δ)`  ⟹  `False`.

The mechanism: `θ ↦ -k/θ` is a primitive of `θ ↦ k/θ²` that blows up at `0⁺`.  Formally, this is
the Mathlib criterion `not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter` applied to
the filter `𝓝[>] 0`, on which `deriv (fun θ ↦ -k/θ) = fun θ ↦ k/θ²` and `‖-k/θ‖ → ∞`.  The
pointwise domination then transfers non-integrability to `f²` by the monotoneity of the upper
Lebesgue integral (`Integrable.mono'`).
-/

open MeasureTheory Filter
open scoped Topology

namespace Work.FTS.EllipticEst.remov.coerc

theorem inv_sq_lower_sq_not_integrable {f : ℝ → ℝ} {δ k : ℝ} (hδ : 0 < δ) (hk : 0 < k)
    (hf : MeasureTheory.IntegrableOn (fun θ => (f θ) ^ 2) (Set.Ioo 0 δ))
    (h : ∀ θ ∈ Set.Ioo (0 : ℝ) δ, k / θ ^ 2 ≤ (f θ) ^ 2) : False := by
  -- `θ ↦ k / θ ^ 2` is not integrable on `(0, δ)`, being the derivative of a function that blows
  -- up at `0⁺`.
  have hnot : ¬ MeasureTheory.IntegrableOn (fun θ : ℝ => k / θ ^ 2) (Set.Ioo 0 δ) := by
    have hderiv : ∀ᶠ x in 𝓝[>] (0 : ℝ), HasDerivAt (fun x : ℝ => (-k) / x) (k / x ^ 2) x := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hx0 : x ≠ 0 := ne_of_gt hx
      have hd : HasDerivAt (fun y : ℝ => (-k) / y) ((0 * x - (-k) * 1) / x ^ 2) x :=
        (hasDerivAt_const x (-k)).div (hasDerivAt_id x) hx0
      have hnum : (0 * x - (-k) * 1) / x ^ 2 = k / x ^ 2 := by ring
      rwa [hnum] at hd
    have hdiff : ∀ᶠ x in 𝓝[>] (0 : ℝ), DifferentiableAt ℝ (fun x : ℝ => (-k) / x) x :=
      hderiv.mono fun x hx => hx.differentiableAt
    have htend : Tendsto (fun x : ℝ => ‖(-k) / x‖) (𝓝[>] (0 : ℝ)) atTop := by
      have hbase : Tendsto (fun x : ℝ => k * x⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
        tendsto_inv_nhdsGT_zero.const_mul_atTop hk
      refine Filter.Tendsto.congr' ?_ hbase
      filter_upwards [self_mem_nhdsWithin] with x hx
      rw [Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos hk, abs_of_pos hx, div_eq_mul_inv]
    have hbigO :
        deriv (fun x : ℝ => (-k) / x) =O[𝓝[>] (0 : ℝ)] (fun θ : ℝ => k / θ ^ 2) := by
      refine Filter.EventuallyEq.isBigO ?_
      filter_upwards [hderiv] with x hx
      exact hx.deriv
    exact not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter (l := 𝓝[>] (0 : ℝ))
      (Ioo_mem_nhdsGT hδ) hdiff htend hbigO
  -- But `0 ≤ k / θ² ≤ f θ ^ 2` on `(0, δ)`, so integrability of `f²` would force that of `k / θ²`.
  apply hnot
  refine MeasureTheory.Integrable.mono' (g := fun θ : ℝ => (f θ) ^ 2) hf ?_ ?_
  · exact (Measurable.div measurable_const (measurable_id.pow_const 2)).aestronglyMeasurable.restrict
  · rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards with θ hθ
    rw [Real.norm_of_nonneg (div_nonneg hk.le (sq_nonneg θ))]
    exact h θ hθ

end Work.FTS.EllipticEst.remov.coerc
