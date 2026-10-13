import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.H2W.lzeroGrowthSlice
import Submission.Work.FTS.EllipticEst.H2W.lzero1SliceGrowth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.WeakPureAux

/-- Pole-type growth of an angular slice from a weighted `L¹` bound on `Lzero1 u`.

`Lzero1 u = -u'' + ∂_θ(tan θ · u) - 6u` on `(0, π/2)`; `θ = 0` is an ordinary point and
`θ = π/2` is a regular singular point with indicial exponents `±1`, so the homogeneous
solutions grow at worst like `(π/2 - θ)⁻¹` (and like `θ⁻¹` near `0`).  The hypothesis
`sinθ cos²θ · |Lzero1 u| ∈ L¹` — a weight that vanishes like `θ` at `0` and like
`(π/2 - θ)²` at `π/2` — already forces that growth.

This is the `WeakPureAux` instance of the pointwise slice-growth bound
(`Work.FTS.EllipticEst.H2W.lzero1SliceGrowth`, where the same statement is proved by the
Wronskian reduction-of-order argument for `C²` data); the only difference is the presentation
of the two reciprocal powers as `1 / θ` and `1 / (π/2 - θ)`. -/
theorem lzeroSlicePoleBound : ∀ (u : ℝ → ℝ),
    (∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo (0 : ℝ) (Real.pi / 2))) →
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2 * |Work.FTS.EllipticEst.Lzero1 u θ|)
      Work.Spaces.Iθ →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |u θ| ≤ C * (1 / θ + 1 / (Real.pi / 2 - θ)) := by
  intro u hu hint
  obtain ⟨C, hC, hbound⟩ := Work.FTS.EllipticEst.H2W.lzero1SliceGrowth u hu hint
  refine ⟨C, hC, fun θ hθ => ?_⟩
  have h := hbound θ hθ
  simpa only [one_div] using h

end Work.FTS.EllipticEst.H2W.WeakPureAux
