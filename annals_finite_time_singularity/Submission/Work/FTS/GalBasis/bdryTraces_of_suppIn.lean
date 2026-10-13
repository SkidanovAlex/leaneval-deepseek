/-
# `Work.FTS.GalBasis.bdryTraces_of_suppIn` — the boundary traces of a box-supported profile

`BdryTraces α k f` (`Work.FTS.Nonlin.BdryTraces`) is the conjunction of the four one-sided
limits per slot `a + b ≤ k` that make the integration-by-parts boundary terms vanish:

* `z * (mixed b a f z θ * w z)^2 → 0` as `z → 0⁺` and as `z → ∞`, for each `θ ∈ (0,π/2)`;
* `sin(2θ)^{1-γ} * (mixed b a f z θ)^2 → 0` as `θ → 0⁺` and as `θ → (π/2)⁻`, for `z > 0`.

If `f` is supported in the box `[a,b] × [δ,π/2-δ]` with `0 < a`, `0 < δ`, then every one of
the functions whose limit is asserted is *eventually identically zero*, so the limits are
trivial: a neighbourhood of `z = 0`, of `z = ∞`, of `θ = 0` and of `θ = π/2` lies off the box,
and off the box every mixed derivative `D_z^b D_θ^a f` vanishes
(`Work.FTS.GalLimit.Closure.mixed_eq_zero_of_suppIn`), which multiplies the exact zero and
kills the `1/z²` and `sin(2θ)^{-γ}` singularities of the weights.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.GalBasis.Defs
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.GalLimit.Closure.phi_HQo

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis

set_option maxHeartbeats 400000

/-- **`BdryTraces` from box support.**  A profile supported in `[a,b] × [δ,π/2-δ]`, with
`0 < a` and `0 < δ`, satisfies the boundary-trace conditions at every order. -/
theorem bdryTraces_of_suppIn {f : ℝ → ℝ → ℝ} {a b δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hSupp : Work.FTS.GalBasis.SuppIn f a b δ) (α : ℝ) (k : ℕ) :
    Work.FTS.Nonlin.BdryTraces α k f := by
  intro a' b' hab
  constructor
  · intro θ hθ
    constructor
    · -- `z → 0⁺`: `z < a` is off the box
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [Ioo_mem_nhdsGT ha] with z hz
      rw [Work.FTS.GalLimit.Closure.mixed_eq_zero_of_suppIn hSupp
        (Or.inl (fun hc => absurd hc.1 (not_le.mpr hz.2))) b' a']
      ring
    · -- `z → ∞`: `z > b` is off the box
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [eventually_gt_atTop b] with z hz
      rw [Work.FTS.GalLimit.Closure.mixed_eq_zero_of_suppIn hSupp
        (Or.inl (fun hc => absurd hc.2 (not_le.mpr hz))) b' a']
      ring
  · intro z hz
    constructor
    · -- `θ → 0⁺`: `θ < δ` is off the box
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [Ioo_mem_nhdsGT hδ] with θ hθ
      rw [Work.FTS.GalLimit.Closure.mixed_eq_zero_of_suppIn hSupp
        (Or.inr (fun hc => absurd hc.1 (not_le.mpr hθ.2))) b' a']
      ring
    · -- `θ → (π/2)⁻`: `θ > π/2 - δ` is off the box
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [Ioo_mem_nhdsLT (show π / 2 - δ < π / 2 by linarith)] with θ hθ
      rw [Work.FTS.GalLimit.Closure.mixed_eq_zero_of_suppIn hSupp
        (Or.inr (fun hc => absurd hc.2 (not_le.mpr hθ.1))) b' a']
      ring

end Work.FTS.GalBasis
